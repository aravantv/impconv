(* ========================================================================= *)
(*                                                                           *)
(*       Implicational conversions and the IMP_REWRITE tactic.               *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


(*****************************************************************************)
(* UTILS                                                                     *)
(*****************************************************************************)

external I : 'a -> 'a = "%identity";;

let UNDISCH_TERM th =
  let p = (fst o dest_imp o concl) th in
  p,UNDISCH th;;

let MAP_CONCLUSION f th =
  let p,th = UNDISCH_TERM th in
  DISCH p (f th);;

let wrap f x = f [x];;

let strip_conj = binops `(/\)`;;

let rec tryfind_fun fs x =
  match fs with
  |[] -> failwith "tryfind_fun"
  |f::fs' -> try f x with _ -> tryfind_fun fs' x;;

let mapfilteri f =
  let rec self i = function
    |[] -> []
    |h::t ->
        let rest = self (i+1) t in
        try f i h :: rest with Failure _ -> rest
  in
  self 0;;

let A_ = `A:bool` and B_ = `B:bool` and C_ = `C:bool` and D_ = `D:bool`;;

let T_ = `T:bool`;;

let IMP_REFL =
  let lem = TAUT `A ==> A` in
  fun t -> INST [t,A_] lem;;

let VARIANT_CONV av t =
  let vs = variables t in
  let mapping = filter (fun (x,y) -> x <> y) (zip vs (variants av vs)) in
  DEPTH_CONV (fun u -> ALPHA_CONV (assoc (bndvar u) mapping) u) t;;

let VARIANT_RULE = CONV_RULE o VARIANT_CONV;;

let DISCH_HD th = DISCH (hd (hyp th)) th;;

let REWR_RULE = CONV_RULE o REWR_CONV;;

let DISCH_IMP_IMP =
  let f = function
    |[] -> I
    |t::ts -> rev_itlist (fun t -> REWR_RULE IMP_IMP o DISCH t) ts o DISCH t
  in
  f o rev;;

let rec DISCH_CONJ t th =
  try
    let t1,t2 = dest_conj t in
    REWR_RULE IMP_IMP (DISCH_CONJ t1 (DISCH_CONJ t2 th))
  with _ -> DISCH t th;;

let rec SPEC_VARS th =
  try
    let v,th' = SPEC_VAR th in
    let vs,th'' = SPEC_VARS th' in
    v::vs,th''
  with _ -> [],th;;

let MAP_FORALL_BODY f th =
  let vs,th = SPEC_VARS th in
  GENL vs (f th);;

(* Expects a theorem of the form `!xyz. P ==> C`
 * Returns `!xyz. P ==> C = T` *)
let GEQT_INTRO1 = MAP_FORALL_BODY (MAP_CONCLUSION EQT_INTRO);;

(* Expects a theorem of the form `!xyz. P ==> !xyz. C`
 * Returns `!xyz. P ==> !xyz. (C = T)` *)
let GEQT_INTRO2 = MAP_FORALL_BODY (MAP_CONCLUSION (MAP_FORALL_BODY EQT_INTRO));;

let hornify =
  let IMPLY_AND_RDISTRIB = TAUT `(x ==> y /\ z) <=> (x==>y) /\ (x==>z)` in
  REWRITE_RULE [GSYM AND_FORALL_THM;IMP_IMP;
    RIGHT_IMP_FORALL_THM;IMPLY_AND_RDISTRIB;GSYM CONJ_ASSOC];;

let dest_binary_blind = function
  |Comb(Comb(_,l),r) -> l,r
  |_ -> failwith "dest_binary_blind";;

(* Term set *)
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


(*****************************************************************************)
(* IMPLICATIONAL RULES                                                       *)
(* i.e., rules to build poropositions based on implications rather than      *)
(* equivalence.                                                              *)
(*****************************************************************************)

let MKIMP_common lem th1 th2 =
  let a,b = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

let MKIMP_CONJ = MKIMP_common MONO_AND;;
let MKIMP_DISJ = MKIMP_common MONO_OR;;

let MKIMP_IMP th1 th2 =
  let b,a = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  MP (INST [a,A_;b,B_;c,C_;d,D_] MONO_IMP) (CONJ th1 th2);;

let MKIMPL_common lem =
  let lem' = REWRITE_RULE[] (INST [C_,D_] lem) in
  fun th t ->
    let a,b = dest_imp (concl th) in
    MP (INST [a,A_;b,B_;t,C_] lem') th;;

let MKIMPL_CONJ = MKIMPL_common MONO_AND;;
let MKIMPL_DISJ = MKIMPL_common MONO_OR;;

let MKIMPL_IMP =
  let MONO_IMP' = REWRITE_RULE[] (INST [C_,D_] MONO_IMP) in
  fun th t ->
    let b,a = dest_imp (concl th) in
    MP (INST [a,A_;b,B_;t,C_] MONO_IMP') th;;

let MKIMPR_common lem =
  let lem' = REWRITE_RULE[] (INST [A_,B_] lem) in
  fun t th ->
    let c,d = dest_imp (concl th) in
    MP (INST [c,C_;d,D_;t,A_] lem') th;;

let MKIMPR_CONJ = MKIMPR_common MONO_AND;;
let MKIMPR_DISJ = MKIMPR_common MONO_OR;;
let MKIMPR_IMP = MKIMPR_common MONO_IMP;;

let MKIMP_NOT th =
  let b,a = dest_imp (concl th) in
  MP (INST [a,A_;b,B_] MONO_NOT) th;;

let MKIMP_QUANT lem x th =
  let x_ty = type_of x and p,q = dest_imp (concl th) in
  let p' = mk_abs(x,p) and q' = mk_abs(x,q) in
  let P = mk_var("P",mk_fun_ty x_ty bool_ty) in
  let Q = mk_var("Q",mk_fun_ty x_ty bool_ty) in
  let lem = INST [p',P;q',Q] (INST_TYPE [x_ty,aty] lem) in
  let c = ONCE_DEPTH_CONV (ALPHA_CONV x) THENC ONCE_DEPTH_CONV BETA_CONV in
  MP (CONV_RULE c lem) (GEN x th);;

let MKIMP_FORALL = MKIMP_QUANT MONO_FORALL;;
let MKIMP_EXISTS = MKIMP_QUANT MONO_EXISTS;;

let MKIMP_IMP_CTXT =
  let lem = TAUT `(B==>A) /\ (A==>C==>D) ==> (A==>C) ==> (B==>D)` in
  fun th1 th2 ->
    let b,a = dest_imp (concl th1) in
    let c,d = dest_imp (snd (dest_imp (concl th2))) in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

let MKIMPR_IMP_CTXT =
  let lem = TAUT `(A==>C==>D) ==> (A==>C) ==> (A==>D)` in
  fun t th ->
    let c,d = dest_imp (snd (dest_imp (concl th))) in
    MP (INST [c,C_;d,D_;t,A_] lem) th;;

let MKIMP_CONJ_CTXT =
  let lem = TAUT `(A==>B) /\ (A==>B==>C==>D) ==> (A/\C==>B/\D)` in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

let MKIMPL_CONJ_CTXT =
  let lem = TAUT `(C==>A==>B) ==> (A/\C==>B/\C)` in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th;;

let MKIMPR_CONJ_CTXT =
  let lem = TAUT `(A==>C==>D) ==> (A/\C==>A/\D)` in
  fun th ->
    let a,cd = dest_imp (concl th) in
    let c,d = dest_imp cd in
    MP (INST [a,A_;c,C_;d,D_] lem) th;;


(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS                                                 *)
(*****************************************************************************)

module Variance =
  struct
    type t = Co | Contra
    let neg = function Co -> Contra | Contra -> Co
  end;;

open Variance;;

(* An implicational conversion maps a term t to a theorem of the form:
 * t' ==> t if covariant
 * t ==> t' if contravariant
 *)
type imp_conv = Context.t -> Variance.t -> term -> thm;;

let imp_conv_of_conv:conv->imp_conv =
  fun c _ v t -> 
    let th1,th2 = EQ_IMP_RULE (c t) in
    match v with Co -> th1 | Contra -> th2;;

let imp_conv_outcome th v =
  let t1,t2 = dest_binary_blind (concl th) in
  match v with Co -> t1 | Contra -> t2;;

let ALL_IMPCONV:imp_conv = fun _ _ -> IMP_REFL;;
let NO_IMPCONV:imp_conv = fun _ _ _ -> failwith "NO_IMPCONV";;

let CONJ_IMPCONV :imp_conv->imp_conv->imp_conv =
  fun c1 c2 ctx v t ->
    let t1,t2 = dest_conj t in
    try 
      let th1 = c1 ctx v t1 in
      try
        let t1' = imp_conv_outcome th1 v in
        let t1',t1'' = match v with Co -> t1',t1 | Contra -> t1,t1' in
        let t1s''' = Tset.union (Tset.strip_conj t1') (Tset.strip_conj t1'') in
        let ctx'' = Context.augments ctx t1s''' in
        let th2 = DISCH_CONJ t1'' (c2 ctx'' v t2) in
        let th2' = DISCH_CONJ t1' th2 in
        MKIMP_CONJ_CTXT th1 th2'
        with Failure _ ->
          (let ctx' = Context.augments ctx (Tset.strip_conj t2) in
          try MKIMPL_CONJ_CTXT (DISCH_CONJ t2 (c1 ctx' v t1))
          with Failure _ -> MKIMPL_CONJ th1 t2)
    with Failure _ -> 
      let ctx' = Context.augments ctx (Tset.strip_conj t1) in
      MKIMPR_CONJ_CTXT (DISCH_CONJ t1 (c2 ctx' v t2));;

let DISJ_IMPCONV :imp_conv->imp_conv->imp_conv =
  fun c1 c2 ctx v t ->
    let t1,t2 = dest_disj t in
    try 
      let th1 = c1 ctx v t1 in
      try MKIMP_DISJ th1 (c2 ctx v t2) with Failure _ -> MKIMPL_DISJ th1 t2
    with Failure _ -> MKIMPR_DISJ t1 (c2 ctx v t2);;

let IMP_IMPCONV :imp_conv->imp_conv->imp_conv =
  fun c1 c2 ctx v t ->
    let t1,t2 = dest_imp t in
    try 
      let th1 = c1 ctx (Variance.neg v) t1 in
      let t1' = imp_conv_outcome th1 (Variance.neg v) in
      let ctx' = Context.augments ctx (Tset.strip_conj t1') in
      try MKIMP_IMP_CTXT th1 (DISCH_CONJ t1' (c2 ctx' v t2))
      with Failure _ -> MKIMPL_IMP th1 t2
    with Failure _ ->
      let ctx' = Context.augments ctx (Tset.strip_conj t1) in
      MKIMPR_IMP_CTXT t1 (DISCH_CONJ t1 (c2 ctx' v t2));;

let NOT_IMPCONV:imp_conv->imp_conv =
  fun c ctx v t -> MKIMP_NOT (c ctx (Variance.neg v) (dest_neg t));;

let QUANT_IMPCONV mkimp sel :imp_conv->imp_conv =
  fun c ctx v t ->
    let x,b = sel t in
    mkimp x (c (Context.remove_variable ctx x) v b);;

let FORALL_IMPCONV = QUANT_IMPCONV MKIMP_FORALL dest_forall;;
let EXISTS_IMPCONV = QUANT_IMPCONV MKIMP_EXISTS dest_exists;;

let SUB_IMPCONV:imp_conv->imp_conv =
  fun c ctx v t ->
    (match name_of (fst (strip_comb t)) with
    |"==>" -> IMP_IMPCONV c
    |"/\\" -> CONJ_IMPCONV c
    |"\//" -> DISJ_IMPCONV c
    |"!" -> FORALL_IMPCONV
    |"?" -> EXISTS_IMPCONV
    |"~" -> NOT_IMPCONV
    |_ -> failwith "SUB_IMPCONV") c ctx v t;;

let bind_impconv (c:imp_conv) ctx v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> IMP_TRANS (c ctx v t1) th
  |Contra -> IMP_TRANS th (c ctx v t2);;

let THEN_IMPCONV (c1:imp_conv) c2 hs v t =
  bind_impconv c2 hs v (c1 hs v t);;

let TRY_IMPCONV :imp_conv->imp_conv =
 fun c ctx v t -> try c ctx v t with Failure _ -> ALL_IMPCONV ctx v t;;

let ORELSE_IMPCONV :imp_conv->imp_conv->imp_conv =
  fun c1 c2 ctx v t ->
    try c1 ctx v t with Failure _ -> c2 ctx v t;;

let CHANGED_IMPCONV:imp_conv->imp_conv =
  fun c ctx v t ->
    let th = c ctx v t in
    let l,r = dest_imp (concl th) in
    if aconv l r then failwith "CHANGED_IMPCONV" else th;;

let rec ONCE_IMPCONV :imp_conv->imp_conv =
  fun c ctx v t ->
    try SUB_IMPCONV (ONCE_IMPCONV c) ctx v t with _ -> c ctx v t;;

let rec DEPTH_IMPCONV :imp_conv->imp_conv =
  let rec (+) c1 c2 ctx v t =
    try let th1 = c1 ctx v t in
      try bind_impconv c2 ctx v th1 with Failure _ -> th1
    with Failure _ -> c2 ctx v t
  and (!) c ctx v t =
    try bind_impconv !c ctx v (c ctx v t)
    with Failure _ -> ALL_IMPCONV ctx v t
  in
  fun c ctx v t ->
    (SUB_IMPCONV (DEPTH_IMPCONV c) + !c) ctx v t;;

let REDEPTH_IMPCONV:imp_conv->imp_conv =
  let rec self c =
    let rec (+) c1 c2 ctx v t =
      try let th1 = c1 ctx v t in
        try bind_impconv c2 ctx v th1 with Failure _ -> th1
      with Failure _ -> c2 ctx v t
    and (++) c1 c2 ctx v t =
      let th1 = c1 ctx v t in
      try bind_impconv c2 ctx v th1 with Failure _ -> th1
    in
    fun ctx v t -> (SUB_IMPCONV (self c) + (c ++ self c)) ctx v t
  in
  self;;


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSION                                          *)
(*****************************************************************************)

let indep_vars th =
  let hs,c = dest_thm (SPEC_ALL th) in
  let p,c = dest_imp c in
  let all_vars = union (frees p) (frees (rhs c)) in
  let dep_vars = union (frees (lhs c)) (freesl hs) in
  subtract all_vars dep_vars;;

let GEN_IMP_REWR_CONV av =
  let pmatch = GEN_PART_MATCH (lhs o snd o strip_forall o snd o dest_imp) in
  fun th ->
    let pmatch' = pmatch th in
    fun t ->
      let th' = pmatch' t in
      VARIANT_RULE av (GENL (indep_vars th') th');;

type conv_with_hyp = term -> thm * term list;;

let IMP_REWR_CONV:Tset.t->thm->conv_with_hyp =
  fun av th ->
    let f t = SPEC_ALL (GEN_IMP_REWR_CONV av th t) in
    fun t ->
      let uh = f t in
      let u = fst (dest_imp (concl uh)) in
      UNDISCH uh,[u];;

(* TODO `~P` --> `P=F` *)
(* TODO gerer les rewrite cycliques *)
let impconv_net_of_thm
  :thm -> (term list->conv_with_hyp) net -> (term list->conv_with_hyp) net =
  let REWR_CONV th t = REWR_CONV th t,[] in
  fun th ->
    let enter = enter (freesl (hyp th)) and c = concl th in
    match snd (strip_forall c) with
    |Comb(Comb(Const("=",_),l),_) -> enter (l,fun _ -> REWR_CONV th)
    |Comb(Comb(Const("==>",_),_),l) ->
          let enter' =
            try
              let l',_ = dest_eq (snd (strip_forall l)) in
              enter (l',C IMP_REWR_CONV th)
            with _ -> I
          in
          let enter'' =
            try
              let _,l' = dest_forall l in
              enter (snd (strip_forall l'),C IMP_REWR_CONV (GEQT_INTRO2 th))
            with _ -> I
          in
          enter' o enter'' o enter (l,C IMP_REWR_CONV (GEQT_INTRO1 th))
    |l ->
        let enter' =
          if l = c then I
          else enter (l,fun _ -> REWR_CONV (MAP_FORALL_BODY EQT_INTRO th))
        in
        enter' o enter (c,fun _ -> REWR_CONV (EQT_INTRO th));;

let patterns_of_thm th =
  let c = concl th in
  match snd (strip_forall c) with
  |Comb(Comb(Const("=",_),l),_) -> [l]
  |Comb(Comb(Const("==>",_),_),l) ->
        let p1s = try [fst (dest_eq (snd (strip_forall l)))] with _ -> [] in
        let p2s = try [snd (strip_forall (snd (dest_forall l)))] with _ -> [] in
        l :: (p1s @ p2s)
  |l -> l :: if l=c then [] else [c];;

let REWRITES_IMPCONV (net:(term list -> conv_with_hyp) net) avs t =
  try tryfind (fun c -> c avs t) (lookup t net)
  with Failure _ -> failwith "REWRITES_IMPCONV";;

extend_basic_rewrites [NOT_FORALL_THM;NOT_IMP];;

let DEEP_IMP_REWR_CONV:thm list->Context.t->conv_with_hyp =
  (* Almost the same as TOP_DEPTH_CONV but with no TRY_CONV on top.
   * The same could be achieved by just using CHANGED_CONV TOP_DEPTH_CONV but
   * this would be probably less efficient.
   *)
  let rec top_depth c t =
    let rec (++) c1 c2 t =
      let th1,hs1 as c1t = c1 t in
      try
        let th2,hs2 = c2 (rand (concl th1)) in
        TRANS th1 th2, union hs1 hs2
      with Failure _ -> c1t
    and (+) c1 c2 t = try (c1 ++ c2) t with Failure _ -> c2 t
    and COMB_QCONV c t =
      let l,r = dest_comb t in
      try
        let th1,hs1 = c l in
        try
          let th2,hs2 = c r in
          MK_COMB(th1,th2), union hs1 hs2
        with Failure _ -> AP_THM th1 r,hs1
      with Failure _ ->
        let th2,hs2 = c r in
        AP_TERM l th2,hs2
    in
    let SUB_QCONV c t =
      let hs = ref [] in
      if is_abs t
      then
        let c' t =
          let th,hs' = c t in
          hs := hs'; th
        in
        let res = ABS_CONV c' t in
        res,!hs
      else COMB_QCONV c t
    in
    let rec (!) c t = (c ++ !c) t in
    (!c + (SUB_QCONV (top_depth c) ++ (c ++ top_depth c))) t
  in
  let basic_cnv t = REWRITES_CONV (basic_net ()) t,[] in
  fun ths ->
    let cnvs = REWRITES_IMPCONV (itlist impconv_net_of_thm ths empty_net) in
    fun ctx t ->
      let av = Tset.union (Tset.variables t) (Context.variables_of ctx) in
      top_depth (fun t -> try cnvs av t with _ -> basic_cnv t) t;;


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

let MATCH_MP_IMPCONV:thm->imp_conv =
  fun th _ -> function
    |Co -> GEN_PART_MATCH rand th
    |Contra -> GEN_PART_MATCH lhand th;;

let IMP_REFLCONV:imp_conv =
  fun ctx v t ->
    if t = T_ then failwith "IMP_REFLCONV"
    else
      if mem t (Context.terms_of ctx)
      then match v with Co -> DISCH T_ (ASSUME t) | Contra -> DISCH t TRUTH
      else failwith "IMP_REFLCONV";;

let EXISTSs i p =
  let codom,dom = unzip i in
  let f i ps = vsubst [i] (snd (dest_exists (hd ps))) :: ps in
  let h::ps = rev_itlist f i [list_mk_exists(dom,p)] in
  rev_itlist EXISTS (zip ps (rev codom)) (ASSUME h);;

let EXISTS_IMPCONV:imp_conv =
  fun ctx v t ->
    match v,t with
    |Co,Comb(Const("?",_),_) ->
        let vs,b = strip_exists t in
        let hmatch (n,b) =
          match partition (C mem vs) (variables b) with
          |[],_ -> failwith "EXISTS_IMPCONV"
          |_::_ as lvs,lcs -> 
              fun h ->
                match term_match lcs b h with 
                |_,i,j when filter (uncurry (<>)) j = [] ->
                    (if i = [] then zip lvs lvs else i),n
                |_ -> failwith "EXISTS_IMPCONV"
        in
        let bs = strip_conj b in
        let ts = Context.terms_of ctx in
        let s,n = tryfind_fun (mapfilteri (curry (tryfind o hmatch)) bs) ts in
        let th = EXISTSs (map (fun v -> rev_assocd v s v,v) vs) b in
        let th' = DISCH_HD th in
        let h = fst (dest_imp (concl th')) in
        (match strip_conj h with
        |[] -> assert false
        |[h] -> th'
        |_::_ as hs ->
          let hs1,h'::hs2 = chop_list n hs in
          let hs_th = CONJ_ACI_RULE (mk_eq(h,list_mk_conj (h'::(hs1@hs2)))) in
          let th1 = CONV_RULE (LAND_CONV (REWR_CONV hs_th)) th' in
          let th2 = UNDISCH (CONV_RULE (REWR_CONV IMP_CONJ) th1) in
          let vs' = subtract vs (map snd s) in
          itlist (fun v -> REWR_RULE LEFT_FORALL_IMP_THM o GEN v) vs' th2)
    |_ -> failwith "EXISTS_IMPCONV";;

let GENERAL_REWRITE_IMPCONV:(Context.t->conv_with_hyp)->imp_conv =
  let IMP_IMP_SYM = TAUT `A==>B==>C <=> B==>A==>C` in
  let IMP_EXIST = GSYM LEFT_IMP_EXISTS_THM in
  fun cnv ctx v t ->
    let th,hyps = cnv ctx t in
    let th1,th2 = EQ_IMP_RULE th in
    let u = concl th2 in
    let u_vs = unions (map (setify o variables) (u::hyps)) in
    let new_vars = subtract u_vs (variables (snd (dest_imp u))) in
    match v with
    |Co -> 
        let p,th2' = UNDISCH_TERM th2 in
        let rec exists_intro = function
          |[] -> DISCH_IMP_IMP (p::hyps) th2'
          |v::vs -> 
              let th = exists_intro vs in
              try REWR_RULE IMP_EXIST (GEN v th) with _ -> th
        in
        exists_intro new_vars
    |Contra ->
        let res =
          match hyps with
          |[] -> th1
          |h::hs -> (REWR_RULE IMP_IMP_SYM o DISCH_IMP_IMP hs o DISCH h) th1
        in
        match new_vars with
        |[] -> res
        |_::_ as vs ->
            let TRY_GEN v th = try GEN v th with _ -> th in
            MAP_CONCLUSION (itlist TRY_GEN vs) res;;

let PURE_REWRITE_IMPCONV ths =
  let (||) = ORELSE_IMPCONV in
  REDEPTH_IMPCONV (GENERAL_REWRITE_IMPCONV (DEEP_IMP_REWR_CONV ths)
    || IMP_REFLCONV || EXISTS_IMPCONV);;

let ONCE_PURE_REWRITE_IMPCONV ths =
  let (+) = THEN_IMPCONV and (||) = ORELSE_IMPCONV in
  ONCE_IMPCONV (GENERAL_REWRITE_IMPCONV (DEEP_IMP_REWR_CONV ths))
  + REDEPTH_IMPCONV (IMP_REFLCONV || EXISTS_IMPCONV);;


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

let hornify =
  let IMPLY_AND_RDISTRIB = TAUT `(x ==> y /\ z) <=> (x==>y) /\(x==>z)` in
  PURE_REWRITE_RULE [GSYM AND_FORALL_THM;IMP_IMP;
    RIGHT_IMP_FORALL_THM;IMPLY_AND_RDISTRIB;GSYM CONJ_ASSOC];;

let preprocess = CONJUNCTS o hornify;;

let REWRITE_IMPCONV = TRY_IMPCONV o PURE_REWRITE_IMPCONV o preprocess;;

let IMPCONV_RULE:imp_conv->thm->thm =
  fun c th ->
    let t = concl th in
    MATCH_MP (c Context.empty Contra t) th;;

let IMPCONV_TAC:imp_conv->tactic =
  fun cnv (asms,c as g) ->
    (MATCH_MP_TAC (cnv (Context.make (map (concl o snd) asms)) Co c)
    THEN TRY (ACCEPT_TAC TRUTH)) g;;

let IMP_REWRITE_TAC ths =
  let tc = IMPCONV_TAC o CHANGED_IMPCONV o PURE_REWRITE_IMPCONV o preprocess in
  let tacs = map tc ths in
  REPEAT (CHANGED_TAC (MAP_EVERY TRY tacs));;
  
(* TODO a context-aware rewrite which adds on the fly the theorems from the
 * context, like the simplifier -> "IMP_SIMP_TAC" *)
let ASM_IMP_REWRITE_TAC = ASM IMP_REWRITE_TAC;;

let CASE_REWRITE_CONV =
  let lem = TAUT `(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\ (P ==> Q))` in
  let lem' = TAUT `(P ==> Q = R) ==> (Q <=> (P ==> R) /\ (~P ==> Q))` in
  fun th t ->
    let th,hyps = DEEP_IMP_REWR_CONV [th] Context.empty t in
    let th' = DISCH_IMP_IMP hyps th in
    REWR_CONV (try MATCH_MP lem th' with _ -> MATCH_MP lem' th') t;;

let CASE_REWRITE_TAC = CONV_TAC o CASE_REWRITE_CONV;;

