(* ========================================================================= *)
(*                                                                           *)
(*                       Utilities.                                          *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


external I : 'a -> 'a = "%identity";;

(* Same as [UNDISCH] but also returns the undischarged term *)
let UNDISCH_TERM th =
  let p = (fst o dest_imp o concl) th in
  p,UNDISCH th;;

(* Same as [UNDISCH_ALL] but also returns the undischarged terms *)
let rec UNDISCH_TERMS th =
  try
    let t,th' = UNDISCH_TERM th in
    let ts,th'' = UNDISCH_TERMS th' in
    t::ts,th''
  with Failure _ -> [],th;;

(* Comblies the function [f] to the conclusion of an implicational theorem. *)
let MAP_CONCLUSION f th =
  let p,th = UNDISCH_TERM th in
  DISCH p (f th);;

let strip_conj = binops `(/\)`;;

(* For a list [f1;...;fk], returns the first [fi x] that succeeds. *)
let rec tryfind_fun fs x =
  match fs with
  |[] -> failwith "tryfind_fun"
  |f::fs' -> try f x with Failure _ -> tryfind_fun fs' x;;

(* Same as [mapfilter] but also provides the rank of the iteration as an 
 * argument to [f]. *)
let mapfilteri f =
  let rec self i = function
    |[] -> []
    |h::t ->
        let rest = self (i+1) t in
        try f i h :: rest with Failure _ -> rest
  in
  self 0;;

let list_of_option = function None -> [] | Some x -> [x];;

let try_list f x = try f x with Failure _ -> [];;

(* A few constants. *)
let A_ = `A:bool` and B_ = `B:bool` and C_ = `C:bool` and D_ = `D:bool`;;
let T_ = `T:bool`;;

(* For a term t, builds `t ==> t` *)
let IMP_REFL =
  let lem = TAUT `A ==> A` in
  fun t -> INST [t,A_] lem;;

(* Conversion version of [variant]:
 * Given variables [v1;...;vk] to avoid and a term [t],
 * returns [|- t = t'] where [t'] is the same as [t] without any use of the
 * variables [v1;...;vk].
 *)
let VARIANT_CONV av t =
  let vs = variables t in
  let mapping = filter (fun (x,y) -> x <> y) (zip vs (variants av vs)) in
  DEPTH_CONV (fun u -> ALPHA_CONV (assoc (bndvar u) mapping) u) t;;

(* Rule version of [VARIANT_CONV] *)
let VARIANT_RULE = CONV_RULE o VARIANT_CONV;;

(* Discharges the first hypothesis of a theorem. *)
let DISCH_HD th = DISCH (hd (hyp th)) th;;

(* Rule version of [REWR_CONV] *)
let REWR_RULE = CONV_RULE o REWR_CONV;;

(* Given a list [A1;...;Ak] and a theorem [th],
 * returns [|- A1 /\ ... /\ Ak ==> th].
 *)
let DISCH_IMP_IMP =
  let f = function
    |[] -> I
    |t::ts -> rev_itlist (fun t -> REWR_RULE IMP_IMP o DISCH t) ts o DISCH t
  in
  f o rev;;

(* Given a term [A /\ B] and a theorem [th], returns [|- A ==> B ==> th]. *)
let rec DISCH_CONJ t th =
  try
    let t1,t2 = dest_conj t in
    REWR_RULE IMP_IMP (DISCH_CONJ t1 (DISCH_CONJ t2 th))
  with Failure _ -> DISCH t th;;

(* Specializes all the universally quantified variables of a theorem,
 * and returns both the theorem and the list of variables.
 *)
let rec SPEC_VARS th =
  try
    let v,th' = SPEC_VAR th in
    let vs,th'' = SPEC_VARS th' in
    v::vs,th''
  with Failure _ -> [],th;;

(* Comblies the function [f] to the body of a universally quantified theorem. *)
let MAP_FORALL_BODY f th =
  let vs,th = SPEC_VARS th in
  GENL vs (f th);;

(* Given a theorem of the form [!xyz. P ==> !uvw. C] and a function [f],
 * return [!xyz. P ==> !uvw. f C].
 *)
let GEN_MAP_CONCLUSION = MAP_FORALL_BODY o MAP_CONCLUSION o MAP_FORALL_BODY

(* Turn a theorem of the form [x ==> y /\ z] into [(x==>y) /\ (x==>z)].
 * Also deals with universal quantifications if necessary
 * (e.g., [x ==> !v. y /\ z] will be turned into
 * [(x ==> !v. y) /\ (x ==> !v. z)])
 *
 * possible improvement: apply the rewrite more locally
 *)
let IMPLY_AND =
  let IMPLY_AND_RDISTRIB = TAUT `(x ==> y /\ z) <=> (x==>y) /\(x==>z)` in
  PURE_REWRITE_RULE [GSYM AND_FORALL_THM;IMP_IMP;
    RIGHT_IMP_FORALL_THM;IMPLY_AND_RDISTRIB;GSYM CONJ_ASSOC];;

(* Returns the two operands of a binary combination.
 * Contrary to [dest_binary], does not check what is the operator.
 *)
let dest_binary_blind = function
  |Comb(Comb(_,l),r) -> l,r
  |_ -> failwith "dest_binary_blind";;

let spec_all = repeat (snd o dest_forall);;

let thm_lt (th1:thm) th2 = th1 < th2;;

(* GMATCH_MP (U1 |- !x1...xn. H1 /\ ... /\ Hk ==> C) (U2 |- P)
 * = (U1 u U2 |- !y1...ym. G1' /\ ... /\ Gl' ==> C')
 * where:
 * - P matches some Hi
 * - C' is the result of applying the matching substitution to C
 * - Gj' is the result of applying the matching substitution to Hj
 * - G1',...,Gl' is the list corresponding to H1,...,Hk but without Hi
 * - y1...ym are the variables among x1,...,xn that are not instantiated
 *
 * possible improvement: make a specific conversion,
 * define a MATCH_MP that also returns the instantiated variables *)
let GMATCH_MP =
  let swap = CONV_RULE (REWR_CONV (TAUT `(p==>q==>r) <=> (q==>p==>r)`)) in
  fun th1 ->
    let vs,th1' = SPEC_VARS th1 in
    let hs,th1'' = UNDISCH_TERMS (PURE_REWRITE_RULE [IMP_CONJ] th1') in
    fun th2 ->
      let f h hs =
        let th1''' = DISCH h th1'' in
        let th1'''' =
          try swap (DISCH_IMP_IMP hs th1''') with Failure _ -> th1'''
        in
        MATCH_MP (GENL vs th1'''') th2
      in
      let rec loop acc = function
        |[] -> []
        |h::hs -> 
            (try [f h (acc @ hs)] with Failure _ -> []) @ loop (h::acc) hs
      in
      loop [] hs;;

let GMATCH_MPS ths1 ths2 =
  let insert (y:thm) = function
    |[] -> [y]
    |x::_ as xs when equals_thm x y -> xs
    |x::xs when thm_lt x y -> x :: insert y xs
    |_::_ as xs -> y::xs
  in
  let inserts ys = itlist insert ys in
  match ths1 with
  |[] -> []
  |th1::ths1' ->
    let rec self acc th1 ths1 = function
      |[] -> (match ths1 with [] -> acc | th::ths1' -> self acc th ths1' ths2)
      |th2::ths2' -> self (inserts (GMATCH_MP th1 th2) acc) th1 ths1 ths2' 
    in
    self [] th1 ths1' ths2;;

let MP_CLOSURE ths1 ths2 =
  let ths1 = filter (is_imp o spec_all o concl) ths1 in
  let rec self ths2 = function
    |[] -> []
    |_::_ as ths1 ->
      let ths1'' = GMATCH_MPS ths1 ths2 in
      self ths2 ths1'' @ ths1''
  in
  self ths2 ths1;;

(* Set of terms. Implemented as ordered lists. *)
module Tset =
  struct
    type t = term list
    let cmp (x:term) y = Pervasives.compare x y
    let lt (x:term) y = Pervasives.compare x y < 0
    let lift f = List.sort cmp o f
    let of_list = lift I
    let insert ts t =
      let rec self = function
        |[] -> [t]
        |x::xs when lt x t -> x::self xs
        |x::_ as xs when x = t -> xs
        |xs -> t::xs
      in
      if t = T_ then ts else self ts
    let remove ts t =
      let rec self = function
        |[] -> []
        |x::xs when lt x t -> x::self xs
        |x::xs when x = t -> xs
        |_::_ as xs -> xs
      in
      self ts
    let strip_conj =
      let rec self acc t =
        try
          let t1,t2 = dest_conj t in
          self (self acc t1) t2
        with Failure _ -> insert acc t
      in
      self []
    let rec union l1 l2 =
      match l1 with
      |[] -> l2
      |h1::t1 ->
          match l2 with
          |[] -> l1
          |h2::t2 when lt h1 h2 -> h1::union t1 l2
          |h2::t2 when h1 = h2 -> h1::union t1 t2
          |h2::t2 -> h2::union l1 t2
    let rec mem x = function
      |x'::xs when x' = x -> true
      |x'::xs when lt x' x -> mem x xs
      |_ -> false
    let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1;;
    let empty = []
    let flat_revmap f =
      let rec self acc = function
        |[] -> acc
        |x::xs -> self (union (f x) acc) xs
      in
      self [];;
    let flat_map f = flat_revmap f o rev;;
    let rec frees acc = function
      |Var _ as t -> insert acc t
      |Const _ -> acc
      |Abs(v,b) -> remove (frees acc b) v
      |Comb(u,v) -> frees (frees acc u) v
    let freesl ts = itlist (C frees) ts empty
    let frees = frees empty
  end;;

module Type_annoted_term =
  struct
    type t =
      |Var_ of string * hol_type
      |Const_ of string * hol_type * term
      |Comb_ of t * t * hol_type
      |Abs_ of t * t * hol_type

    let type_of = function
      |Var_(_,ty) -> ty
      |Const_(_,ty,_) -> ty
      |Comb_(_,_,ty) -> ty
      |Abs_(_,_,ty) -> ty

    let rec of_term = function
      |Var(s,ty) -> Var_(s,ty)
      |Const(s,ty) as t -> Const_(s,ty,t)
      |Comb(u,v) ->
          let u' = of_term u and v' = of_term v in
          Comb_(u',v',snd (dest_fun_ty (type_of u')))
      |Abs(x,b) ->
          let x' = of_term x and b' = of_term b in
          Abs_(x',b',mk_fun_ty (type_of x') (type_of b'))

    let rec equal t1 t2 =
      match t1,t2 with
      |Var_(s1,ty1),Var_(s2,ty2)
      |Const_(s1,ty1,_),Const_(s2,ty2,_) -> s1 = s2 & ty1 = ty2
      |Comb_(u1,v1,_),Comb_(u2,v2,_) -> equal u1 u2 & equal v1 v2
      |Abs_(v1,b1,_),Abs_(v2,b2,_) -> equal v1 v2 & equal b1 b2
      |_ -> false

    let rec to_term = function
      |Var_(s,ty) -> mk_var(s,ty)
      |Const_(_,_,t) -> t
      |Comb_(u,v,_) -> mk_comb(to_term u,to_term v)
      |Abs_(v,b,_) -> mk_abs(to_term v,to_term b)

    let dummy = Var_("",aty)

    let rec find_term p t =
      if p t then t else
        match t with
        |Abs_(_,b,_) -> find_term p b
        |Comb_(u,v,_) -> try find_term p u with Failure _ -> find_term p v
        |_ -> failwith "Annot.find_term";;
  end;;

module Annot = Type_annoted_term;;
