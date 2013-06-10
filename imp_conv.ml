(* ========================================================================= *)
(*                                                                           *)
(*                 Implicational conversions.                                *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


needs "utils.ml";;


(*****************************************************************************)
(* IMPLICATIONAL RULES                                                       *)
(* i.e., rules to build propositions based on implications rather than       *)
(* equivalence.                                                              *)
(*****************************************************************************)

let MKIMP_common lem th1 th2 =
  let a,b = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

(* Similar to [MK_CONJ] but theorems should be implicational instead of
 * equational, i.e., conjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A /\ C ==> B /\ D].
 *)
let MKIMP_CONJ = MKIMP_common MONO_AND;;

(* Similar to [MK_DISJ] but theorems should be implicational instead of
 * equational, i.e., disjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A \/ C ==> B \/ D].
 *)
let MKIMP_DISJ = MKIMP_common MONO_OR;;

(* Given two theorems [A ==> B] and [C ==> D],
 * returns [(B ==> C) ==> (A ==> D)].
 *)
let MKIMP_IMP th1 th2 =
  let b,a = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  MP (INST [a,A_;b,B_;c,C_;d,D_] MONO_IMP) (CONJ th1 th2);;

let MKIMPL_common lem =
  let lem' = REWRITE_RULE[] (INST [C_,D_] lem) in
  fun th t ->
    let a,b = dest_imp (concl th) in
    MP (INST [a,A_;b,B_;t,C_] lem') th;;

(* Given a theorem [A ==> B] and a term [C],
 * returns [A /\ C ==> B /\ C].
 *)
let MKIMPL_CONJ = MKIMPL_common MONO_AND;;

(* Given a theorem [A ==> B] and a term [C],
 * returns [A \/ C ==> B \/ C].
 *)
let MKIMPL_DISJ = MKIMPL_common MONO_OR;;

(* Given a theorem [A ==> B] and a term [C],
 * returns [(B ==> C) ==> (A ==> C)].
 *)
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

(* Given a term [A] and a theorem [B ==> C],
 * returns [A /\ B ==> A /\ C].
 *)
let MKIMPR_CONJ = MKIMPR_common MONO_AND;;

(* Given a term [A] and a theorem [B ==> C],
 * returns [A \/ B ==> A \/ C].
 *)
let MKIMPR_DISJ = MKIMPR_common MONO_OR;;

(* Given a term [A] and a theorem [B ==> C],
 * returns [(A ==> B) ==> (A ==> C)].
 *)
let MKIMPR_IMP = MKIMPR_common MONO_IMP;;

(* Given a theorem [A ==> B], returns [~B ==> ~A]. *)
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

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(!x. A) ==> (!x. B)]. *)
let MKIMP_FORALL = MKIMP_QUANT MONO_FORALL;;

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(?x. A) ==> (?x. B)]. *)
let MKIMP_EXISTS = MKIMP_QUANT MONO_EXISTS;;

(* Given two theorems [A ==> B] and [B ==> C ==> D],
 * returns [(B ==> C) ==> (A ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
let MKIMP_IMP_CTXT =
  let lem = TAUT `(B==>A) /\ (A==>C==>D) ==> (A==>C) ==> (B==>D)` in
  fun th1 th2 ->
    let b,a = dest_imp (concl th1) in
    let c,d = dest_imp (snd (dest_imp (concl th2))) in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

(* Given a theorem [B ==> C ==> D], returns [(B ==> C) ==> (B ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
let MKIMPR_IMP_CTXT =
  let lem = TAUT `(A==>C==>D) ==> (A==>C) ==> (A==>D)` in
  fun th ->
    let a,cd = dest_imp (concl th) in
    let c,d = dest_imp cd in
    MP (INST [c,C_;d,D_;a,A_] lem) th;;

(* Given two theorems [A ==> B] and [A ==> B ==> C ==> D],
 * returns [(A /\ C) ==> (B /\ D)],
 * i.e., similar to [MKIMP_CONJ] but allows to remove the contexts [A] and [B].
 *)
let MKIMP_CONJ_CTXT =
  let lem = TAUT `(A==>B) /\ (A==>B==>C==>D) ==> (A/\C==>B/\D)` in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

(* Given a theorem [C ==> A ==> B], returns [(A /\ C) ==> (B /\ C)],
 * i.e., similar to [MKIMPL_CONJ] but allows to remove the context [C].
 *)
let MKIMPL_CONJ_CTXT =
  let lem = TAUT `(C==>A==>B) ==> (A/\C==>B/\C)` in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th;;

(* Given a theorem [A ==> B ==> C], returns [(A /\ B) ==> (A /\ C)],
 * i.e., similar to [MKIMPR_CONJ] but allows to remove the context [A].
 *)
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
 *
 * Note to CPP reviewers: 
 * We also add explicitly a context in the type, but this will probably change
 * in the future in favour of an independent handling of the context. Something
 * similar to what is currently done for SIMP_TAC.
 *)
(* TODO handle contexts in a better way, as it is the case for SIMP_TAC for
 * instance. *)
type imp_conv = Context.t -> Variance.t -> term -> thm;;

(* Trivial embedding of conversions into implicational conversions. *)
let imp_conv_of_conv:conv->imp_conv =
  fun c _ v t -> 
    let th1,th2 = EQ_IMP_RULE (c t) in
    match v with Co -> th1 | Contra -> th2;;

(* Retrieves the outcome of an implicational conversion, i.e., t'. *)
let imp_conv_outcome th v =
  let t1,t2 = dest_binary_blind (concl th) in
  match v with Co -> t1 | Contra -> t2;;

(* [ALL_IMPCONV _ t] returns `t==>t` *)
let ALL_IMPCONV:imp_conv = fun _ _ -> IMP_REFL;;

(* The implicational conversion which always fails. *)
let NO_IMPCONV:imp_conv = fun _ _ _ -> failwith "NO_IMPCONV";;

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ C)] returns [B /\ D ==> A /\ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [CONJ_IMPCONV ic1 ic2 Contra (A /\ B)]
 * returns [A /\ B ==> C /\ D].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [A |- D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ B)] returns [|- C /\ D ==> A /\ B]
 * (i.e., [A] does not appear in the hypotheses).
 *)
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

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [DISJ_IMPCONV ic1 ic2 Co (A \/ C)] returns [B \/ D ==> A \/ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [DISJ_IMPCONV ic1 ic2 Contra (A \/ B)]
 * returns [A \/ B ==> C \/ D].
 *)
let DISJ_IMPCONV :imp_conv->imp_conv->imp_conv =
  fun c1 c2 ctx v t ->
    let t1,t2 = dest_disj t in
    try 
      let th1 = c1 ctx v t1 in
      try MKIMP_DISJ th1 (c2 ctx v t2) with Failure _ -> MKIMPL_DISJ th1 t2
    with Failure _ -> MKIMPR_DISJ t1 (c2 ctx v t2);;

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Co C] returns [D ==> C],
 * then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns [(B ==> D) ==> (A ==> C)].
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Contra C] returns
 * [C ==> D], then [IMP_IMPCONV ic1 ic2 Contra (A ==> C)]
 * returns [(A ==> C) ==> (B ==> D)].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [B |- D ==> C], then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns
 * [|- (B ==> D) ==> (A ==> C)] (i.e., [B] does not appear in the hypotheses).
 *)
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
      MKIMPR_IMP_CTXT (DISCH_CONJ t1 (c2 ctx' v t2));;

(* Consider an implicational conversion ic.
 * Suppose [ic Contra A] returns [A ==> B]
 * then [NOT_IMPCONV ic Co ~A] returns [~B ==> ~A].
 * Suppose [ic Co A] returns [B ==> A]
 * then [NOT_IMPCONV ic Contra ~A] returns [~A ==> ~B].
 *)
let NOT_IMPCONV:imp_conv->imp_conv =
  fun c ctx v t -> MKIMP_NOT (c ctx (Variance.neg v) (dest_neg t));;

let QUANT_IMPCONV mkimp sel :imp_conv->imp_conv =
  fun c ctx v t ->
    let x,b = sel t in
    mkimp x (c (Context.remove_variable ctx x) v b);;

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [FORALL_IMPCONV ic Co (!x.A)] returns [(!x.B) ==> (!x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [FORALL_IMPCONV ic Contra (!x.A)] returns [(!x.A) ==> (!x.B)].
 *)
let FORALL_IMPCONV = QUANT_IMPCONV MKIMP_FORALL dest_forall;;

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [EXISTS_IMPCONV ic Co (?x.A)] returns [(?x.B) ==> (?x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [EXISTS_IMPCONV ic Contra (?x.A)] returns [(?x.A) ==> (?x.B)].
 *)
let EXISTS_IMPCONV = QUANT_IMPCONV MKIMP_EXISTS dest_exists;;

(* Applies an implicational conversion on the subformula(s) of the input term*)
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

(* Takes a theorem which results of an implicational conversion and applies a
 * another implicational conversion on the outcome.
 *)
let bind_impconv (c:imp_conv) ctx v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> IMP_TRANS (c ctx v t1) th
  |Contra -> IMP_TRANS th (c ctx v t2);;

(* Sequential combinator. *)
let THEN_IMPCONV (c1:imp_conv) c2 hs v t =
  bind_impconv c2 hs v (c1 hs v t);;

(* Try combinator *)
let TRY_IMPCONV :imp_conv->imp_conv =
 fun c ctx v t -> try c ctx v t with Failure _ -> ALL_IMPCONV ctx v t;;

(* Applies the first of two implicational conversions that succeeds. *)
let ORELSE_IMPCONV :imp_conv->imp_conv->imp_conv =
  fun c1 c2 ctx v t ->
    try c1 ctx v t with Failure _ -> c2 ctx v t;;

(* Makes an implicational conversion fail if applying it leaves a term 
 * unchanged.
 *)
let CHANGED_IMPCONV:imp_conv->imp_conv =
  fun c ctx v t ->
    let th = c ctx v t in
    let l,r = dest_imp (concl th) in
    if aconv l r then failwith "CHANGED_IMPCONV" else th;;

(* Applies an implicational conversion once to the first suitable sub-term(s)
 * encountered in top-down order.
 *)
let rec ONCE_IMPCONV :imp_conv->imp_conv =
  fun c ctx v t ->
    try SUB_IMPCONV (ONCE_IMPCONV c) ctx v t with _ -> c ctx v t;;

(* Applies an implicational conversion repeatedly to all the sub-terms of a
 * term, in bottom-up order.
 *) 
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

(* Applies an implicational conversion bottom-up to all subterms, retraversing
 * changed ones.
 *)
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
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* From an implicational conversion builds a rule, i.e., a function which
 * takes a theorem and returns a new theorem.
 *)
let IMPCONV_RULE:imp_conv->thm->thm =
  fun c th ->
    let t = concl th in
    MATCH_MP (c Context.empty Contra t) th;;

(* From an implicational conversion builds a tactic. *)
let IMPCONV_TAC:imp_conv->tactic =
  fun cnv (asms,c as g) ->
    (MATCH_MP_TAC (cnv (Context.make (map (concl o snd) asms)) Co c)
    THEN TRY (ACCEPT_TAC TRUTH)) g;;
