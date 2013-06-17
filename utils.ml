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

(* Applies the function [f] to the conclusion of an implicational theorem. *)
let MAP_CONCLUSION f th =
  let p,th = UNDISCH_TERM th in
  DISCH p (f th);;

let wrap f x = f [x];;

let strip_conj = binops `(/\)`;;

(* For a list [f1;...;fk], returns the first [fi x] that succeeds. *)
let rec tryfind_fun fs x =
  match fs with
  |[] -> failwith "tryfind_fun"
  |f::fs' -> try f x with _ -> tryfind_fun fs' x;;

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
  with _ -> DISCH t th;;

(* Specializes all the universally quantified variables of a theorem,
 * and returns both the theorem and the list of variables.
 *)
let rec SPEC_VARS th =
  try
    let v,th' = SPEC_VAR th in
    let vs,th'' = SPEC_VARS th' in
    v::vs,th''
  with _ -> [],th;;

(* Applies the function [f] to the body of a universally quantified theorem. *)
let MAP_FORALL_BODY f th =
  let vs,th = SPEC_VARS th in
  GENL vs (f th);;

(* Given a theorem [~th], returns [th<=>F],
 * for any other theorem returns [th<=>T].
 *)
let GEN_EQT_INTRO th = try EQF_INTRO th with _ -> EQT_INTRO th;;

(* Expects a theorem of the form `!xyz. P ==> C`
 * Returns `!xyz. P ==> C = T` *)
let GEQT_INTRO1 = MAP_FORALL_BODY (MAP_CONCLUSION GEN_EQT_INTRO);;

(* Expects a theorem of the form `!xyz. P ==> !xyz. C`
 * Returns `!xyz. P ==> !xyz. (C = T)` *)
let GEQT_INTRO2 =
  MAP_FORALL_BODY (MAP_CONCLUSION (MAP_FORALL_BODY GEN_EQT_INTRO));;

(* Turn a theorem of the form [x ==> y /\ z] into [(x==>y) /\ (x==>z)].
 * Also deals with universal quantifications if necessary
 * (e.g., [x ==> !v. y /\ z] will be turned into
 * [(x ==> !v. y) /\ (x ==> !v. z)])
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

(* Ordering among theorems. *)
let thm_lt (th1:thm) th2 = th1 < th2;;

(* Set of terms. Implemented as ordered lists. *)
module Tset =
  struct
    type t = term list
    let lt (x:term) y = Pervasives.compare x y < 0
    let variables = sort lt o variables
    let insert ts t =
      let rec self = function
        |[] -> [t]
        |x::xs when lt x t -> x::self xs
        |x::_ as xs when x = t -> xs
        |xs -> t::xs
      in
      self ts
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
        with _ -> insert acc t
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
    let empty = []
  end;;

(* Context of a conversion.
 * Basically a list of boolean terms.
 * We also handle variables in these terms indepedently in order to avoid
 * redundant calls to [variables].
 *)
module Context =
  struct
    type t = term list * Tset.t
    let empty = [],Tset.empty
    let lt (x:term) y = Pervasives.compare x y < 0
    let augment_atom (ts,vs) a =
      let rec self = function
        |[] -> [a]
        |x::xs when lt x a -> x::self xs
        |x::_ as xs when x = a -> xs
        |xs -> a::xs
      in
      self ts,Tset.union vs (Tset.variables a)
    let augment ctx t = itlist (C augment_atom) (strip_conj t) ctx
    let augments ctx ts = itlist (C augment) ts ctx
    let terms_of (ts,_) = ts
    let make = augments empty
    let variables_of (_,vs) = vs
    let mem (ts,_) t =
      let rec self = function
        |[] -> false
        |x::xs when lt x t -> self xs
        |x::xs when x = t -> true
        |_::_ -> false
      in
      self ts
    let remove_variable (ts,vs) v =
      (filter (not o vfree_in v) ts,Tset.remove vs v)
  end;;

