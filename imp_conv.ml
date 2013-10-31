(* ========================================================================= *)
(*                                                                           *)
(*                 Implicational conversions.                                *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Analysis and Design of Dependable Systems                *)
(*                  fortiss GmbH, Munich, Germany                            *)
(*                                                                           *)
(*       Formerly:  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent.aravantinos@fortiss.org>                      *)
(*                                                                           *)
(* ========================================================================= *)

needs "utils.ml";;
needs "fo_match.ml";;


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

let MKIMP_IFF =
  let lem = 
    TAUT `((A ==> B) ==> (C ==> D)) /\ ((B ==> A) ==> (D ==> C)) ==> (A <=> B)
      ==> (C <=> D)`
  in
  fun th1 th2 ->
    let ab,cd = dest_imp (concl th1) in
    let a,b = dest_imp ab and c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

(* th1 = (A ==> B) ==> C1
 * th2 = (B ==> A) ==> C2
 * output = (A <=> B) ==> (C1 /\ C2)
 *)
let MKIMP_CONTRA_IFF =
  let lem = 
    TAUT `((A ==> B) ==> C) /\ ((B ==> A) ==> D) ==> (A <=> B) ==> C /\ D`
  in
  fun th1 th2 ->
    let ab,c = dest_imp (concl th1) and _,d = dest_imp (concl th2) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

let MKIMPL_CONTRA_IFF =
  let lem = TAUT `((A ==> B) ==> C) ==> (A <=> B) ==> C /\ (B ==> A)` in
  fun th ->
    let ab,c = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th;;

let MKIMPR_CONTRA_IFF =
  let lem = 
    TAUT `((B ==> A) ==> D) ==> (A <=> B) ==> (A ==> B) /\ D`
  in
  fun th ->
    let ba,d = dest_imp (concl th) in
    let b,a = dest_imp ba in
    MP (INST [a,A_;b,B_;d,D_] lem) th;;

let MKIMP_CO_IFF =
  let lem = 
    TAUT `(C ==> A ==> B) /\ (D ==> B ==> A) ==> C /\ D ==> (A <=> B)`
  in
  fun th1 th2 ->
    let c,ab = dest_imp (concl th1) and d,_ = dest_imp (concl th2) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

let MKIMPL_CO_IFF =
  let lem = 
    TAUT `(C ==> A ==> B) ==> C /\ (B ==> A) ==> (A <=> B)`
  in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th;;

let MKIMPR_CO_IFF =
  let lem = TAUT `(D ==> B ==> A) ==> (A ==> B) /\ D ==> (A <=> B)` in
  fun th ->
    let d,ba = dest_imp (concl th) in
    let b,a = dest_imp ba in
    MP (INST [a,A_;b,B_;d,D_] lem) th;;

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
let MKIMP_IMP_CONTRA_CTXT =
  let lem = TAUT `(B==>A) /\ (A==>B==>C==>D) ==> (A==>C) ==> (B==>D)` in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

let MKIMP_IMP_CO_CTXT =
  let lem = TAUT `(A==>B) /\ (A==>B==>D==>C) ==> (B==>D) ==> (A==>C)` in
  fun th1 th2 ->
    let a,bdc = dest_imp (concl th2) in
    let b,dc = dest_imp bdc in
    let d,c = dest_imp dc in
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
let MKIMP_CONJ_CONTRA_CTXT =
  let lem = TAUT `(C==>A==>B) /\ (A==>B==>C==>D) ==> (A/\C==>B/\D)` in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

let MKIMPL_CONJ_CONTRA_CTXT =
  let lem = TAUT `(C==>A==>B) ==> (A/\C==>B/\C)` in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th;;

let MKIMPR_CONJ_CONTRA_CTXT =
  let lem = TAUT `(A==>C==>D) ==> (A/\C==>A/\D)` in
  fun th ->
    let a,cd = dest_imp (concl th) in
    let c,d = dest_imp cd in
    MP (INST [a,A_;c,C_;d,D_] lem) th;;

let MKIMP_CONJ_CO_CTXT =
  let lem = TAUT `(B==>A) /\ (B==>D==>C) ==> (B/\D==>A/\C)` in
  fun th1 th2 ->
    let b,a = dest_imp (concl th1) in
    let d,c = dest_imp (snd (dest_imp (concl th2))) in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2);;

let MKIMPL_CONJ_CO_CTXT =
  let lem = TAUT `(B==>A) ==> (B/\C==>A/\C)` in
  fun th ->
    let b,a = dest_imp (concl th) in
    fun c -> MP (INST [a,A_;b,B_;c,C_] lem) th;;

let MKIMPL_CONJ_CO2_CTXT =
  let lem = TAUT `(C==>B==>A) ==> (B/\C==>A/\C)` in
  fun th ->
    let c,ba = dest_imp (concl th) in
    let b,a = dest_imp ba in
    MP (INST [a,A_;b,B_;c,C_] lem) th;;

let MKIMPR_CONJ_CO_CTXT = MKIMPR_CONJ_CONTRA_CTXT;;


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
type imp_conv = Variance.t -> term -> thm;;

(* Trivial embedding of conversions into implicational conversions. *)
let imp_conv_of_conv:conv->imp_conv =
  fun c v t -> 
    let th1,th2 = EQ_IMP_RULE (c t) in
    match v with Co -> th2 | Contra -> th1;;

(* Retrieves the outcome of an implicational conversion, i.e., t'. *)
let imp_conv_outcome th v =
  let t1,t2 = dest_binary_blind (concl th) in
  match v with Co -> t1 | Contra -> t2;;

(* [ALL_IMPCONV _ t] returns `t==>t` *)
let ALL_IMPCONV:imp_conv = fun _ -> IMP_REFL;;

(* The implicational conversion which always fails. *)
let NO_IMPCONV:imp_conv = fun _ _ -> failwith "NO_IMPCONV";;

let bind_impconv (c:imp_conv) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> IMP_TRANS (c v t1) th
  |Contra -> IMP_TRANS th (c v t2);;

let THEN_IMPCONV (c1:imp_conv) c2 v t = bind_impconv c2 v (c1 v t);;


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Given a theorem [p ==> c], returns the implicational conversion which:
  * - in the covariant case, matches the input term [t] against [c] and returns
  *   [s(p) ==> t], where [s] is the matching substitution
  * - in the contravariant case, matches the input term [t] against [p] and returns
  *   [t ==> s(c)], where [s] is the matching substitution
  *)
let MATCH_MP_IMPCONV:thm->imp_conv =
  fun th -> function
    |Co -> GEN_PART_MATCH rand th
    |Contra -> GEN_PART_MATCH lhand th;;


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* From an implicational conversion builds a rule, i.e., a function which
 * takes a theorem and returns a new theorem.
 *)
let IMPCONV_RULE:imp_conv->thm->thm =
  fun c th ->
    let t = concl th in
    MATCH_MP (c Contra t) th;;

(* From an implicational conversion builds a tactic. *)
let IMPCONV_TAC:imp_conv->tactic =
  fun cnv (_,c as g) ->
    (MATCH_MP_TAC (cnv Co c) THEN TRY (ACCEPT_TAC TRUTH)) g;;


(*****************************************************************************)
(* CONTEXT HANDLING                                                          *)
(*****************************************************************************)

(* [term list] = terms to add to the context *)
type 'a with_context =
  With_context of 'a * (Tset.t -> 'a with_context) * (term -> 'a with_context);;

let apply (With_context(c,_,_)) = c;;

(* Maybe avoid the augment if the input list is empty? *)
let augment (With_context(_,a,_)) = a;;
let diminish (With_context(_,_,d)) = d;;
let apply_with_context c ctx v t =
  DISCH_CONJ ctx (apply (augment c (Tset.strip_conj ctx)) v t);;

let imp_conv_of_ctx_imp_conv = (apply:imp_conv with_context -> imp_conv);;

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
let rec CONJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_conj t in
      match v with
      |Co ->
          (try 
            let th1 = apply c Co t1 in
            try
              let t1' = imp_conv_outcome th1 Co in
              MKIMP_CONJ_CO_CTXT th1 (apply_with_context c t1' Co t2)
              with Failure _ -> MKIMPL_CONJ_CO_CTXT th1 t2
          with Failure _ -> MKIMPR_CONJ_CO_CTXT (apply_with_context c t1 Co t2))
      |Contra ->
          try 
            (* note: we remove t1 in case it appears in t2, since otherwise,
             * t1 removes t2 and t2 removes t1
             *)
            let t2s = Tset.remove (Tset.strip_conj t2) t1 in
            let th1 = apply (augment c t2s) Contra t1 in
              try
                let t1' = imp_conv_outcome th1 Contra in
                let t1s = Tset.strip_conj t1 and t1s' = Tset.strip_conj t1' in
                let t1s'' = Tset.union t1s t1s' in
                let th2 = apply (augment c t1s'') Contra t2 in
                let th2' = DISCH_CONJ t1 (DISCH_CONJ t1' th2) in
                MKIMP_CONJ_CONTRA_CTXT (DISCH_CONJ t2 th1) th2'
              with Failure _ -> MKIMPL_CONJ_CONTRA_CTXT (DISCH_CONJ t2 th1)
            with Failure _ -> 
              MKIMPR_CONJ_CONTRA_CTXT (apply_with_context c t1 Contra t2))
      :imp_conv),
    CONJ_CTXIMPCONV o augment c,
    CONJ_CTXIMPCONV o diminish c);;

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [DISJ_IMPCONV ic1 ic2 Co (A \/ C)] returns [B \/ D ==> A \/ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [DISJ_IMPCONV ic1 ic2 Contra (A \/ B)]
 * returns [A \/ B ==> C \/ D].
 *)
let rec DISJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_disj t in
      try 
        let th1 = apply c v t1 in
        try MKIMP_DISJ th1 (apply c v t2) with Failure _ -> MKIMPL_DISJ th1 t2
      with Failure _ -> MKIMPR_DISJ t1 (apply c v t2)):imp_conv),
    DISJ_CTXIMPCONV o augment c,
    DISJ_CTXIMPCONV o diminish c);;

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
let rec IMP_CTXIMPCONV (c:imp_conv with_context)  =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_imp t in
      try 
        let v' = Variance.neg v in
        let th1 = apply c v' t1 in
        let t1' = imp_conv_outcome th1 v' in
        let t1s = Tset.union (Tset.strip_conj t1) (Tset.strip_conj t1') in
        let c' = augment c t1s in
        let mk =
          match v with Co -> MKIMP_IMP_CO_CTXT | Contra -> MKIMP_IMP_CONTRA_CTXT
        in
        try mk th1 (DISCH_CONJ t1 (DISCH_CONJ t1' (apply c' v t2)))
        with Failure _ -> MKIMPL_IMP th1 t2
      with Failure _ -> MKIMPR_IMP_CTXT (apply_with_context c t1 v t2)
      ):imp_conv),
    IMP_CTXIMPCONV o augment c,
    IMP_CTXIMPCONV o diminish c);;

let rec IFF_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_iff t in
      let lr,l,r =
        match v with
        |Co -> MKIMP_CO_IFF,MKIMPL_CO_IFF,MKIMPR_CO_IFF
        |Contra -> MKIMP_CONTRA_IFF,MKIMPL_CONTRA_IFF,MKIMPR_CONTRA_IFF
      in
      (try 
        let th1 = apply c v (mk_imp (t1,t2)) in
        try
          let th2 = apply c v (mk_imp (t2,t1)) in
          (try MKIMP_IFF th1 th2 with Failure _ -> lr th1 th2)
        with Failure _ -> l th1
      with Failure _ -> r (apply c v (mk_imp (t2,t1))))):imp_conv),
    IFF_CTXIMPCONV o augment c,
    IFF_CTXIMPCONV o diminish c);;

(* Consider an implicational conversion ic.
 * Suppose [ic Contra A] returns [A ==> B]
 * then [NOT_IMPCONV ic Co ~A] returns [~B ==> ~A].
 * Suppose [ic Co A] returns [B ==> A]
 * then [NOT_IMPCONV ic Contra ~A] returns [~A ==> ~B].
 *)
let rec NOT_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t -> MKIMP_NOT (apply c (Variance.neg v) (dest_neg t))):imp_conv),
    NOT_CTXIMPCONV o augment c,
    NOT_CTXIMPCONV o diminish c);;

let rec QUANT_CTXIMPCONV mkimp sel (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let x,b = sel t in
      let c' = diminish c x in
      mkimp x (apply c' v b)):imp_conv),
    QUANT_CTXIMPCONV mkimp sel o augment c,
    QUANT_CTXIMPCONV mkimp sel o diminish c);;

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [FORALL_IMPCONV ic Co (!x.A)] returns [(!x.B) ==> (!x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [FORALL_IMPCONV ic Contra (!x.A)] returns [(!x.A) ==> (!x.B)].
 *)
let FORALL_CTXIMPCONV = QUANT_CTXIMPCONV MKIMP_FORALL dest_forall;;

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [EXISTS_IMPCONV ic Co (?x.A)] returns [(?x.B) ==> (?x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [EXISTS_IMPCONV ic Contra (?x.A)] returns [(?x.A) ==> (?x.B)].
 *)
let EXISTS_CTXIMPCONV = QUANT_CTXIMPCONV MKIMP_EXISTS dest_exists;;

(* Applies an implicational conversion on the subformula(s) of the input term*)
let rec SUB_CTXIMPCONV =
  let iff_ty = `:bool->bool->bool` in
  fun c ->
    With_context(
    ((fun v t ->
      let n,ty = dest_const (fst (strip_comb t)) in
      apply
        ((match n with
        |"==>" -> IMP_CTXIMPCONV
        |"/\\" -> CONJ_CTXIMPCONV
        |"\\/" -> DISJ_CTXIMPCONV
        |"=" when ty = iff_ty -> IFF_CTXIMPCONV
        |"!" -> FORALL_CTXIMPCONV
        |"?" -> EXISTS_CTXIMPCONV
        |"~" -> NOT_CTXIMPCONV
        |_ -> failwith "SUB_CTXIMPCONV") c)
        v t):imp_conv),
    SUB_CTXIMPCONV o augment c,
    SUB_CTXIMPCONV o diminish c);;

(* Takes a theorem which results of an implicational conversion and applies
 * another implicational conversion on the outcome.
 *)
let bind_ctximpconv (c:imp_conv with_context) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> IMP_TRANS (apply c v t1) th
  |Contra -> IMP_TRANS th (apply c v t2);;

let rec BIND_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v th -> bind_ctximpconv c v th),
    BIND_CTXIMPCONV o augment c,
    BIND_CTXIMPCONV o diminish c));;

(* Sequential combinator. *)
let rec THEN_CTXIMPCONV (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fun v t -> bind_ctximpconv c2 v (apply c1 v t)):imp_conv),
    (fun x -> THEN_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fun x -> THEN_CTXIMPCONV (diminish c1 x) (diminish c2 x)));;

exception Unchanged;;

(* Try combinator *)
let rec TRY_CTXIMPCONV (c:imp_conv with_context) =
    With_context(
      ((fun v t ->
        try apply c v t
        with Failure _ | Unchanged -> ALL_IMPCONV v t):imp_conv),
      TRY_CTXIMPCONV o augment c,
      TRY_CTXIMPCONV o diminish c);;

(* Applies the first of two implicational conversions that succeeds. *)
let rec ORELSE_CTXIMPCONV
  (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fun v t -> try apply c1 v t with Failure _ -> apply c2 v t):imp_conv),
    (fun x -> ORELSE_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fun x -> ORELSE_CTXIMPCONV (diminish c1 x) (diminish c2 x)));;

(* Makes an implicational conversion fail if applying it leaves a term 
 * unchanged.
 *)
let rec CHANGED_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let th = apply c v t in
      let l,r = dest_imp (concl th) in
      if aconv l r then failwith "CHANGED_CTXIMPCONV" else th):imp_conv),
    CHANGED_CTXIMPCONV o augment c,
    CHANGED_CTXIMPCONV o diminish c);;

let rec UNCHANGED_OF_FAIL_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t -> try apply c v t with Failure _ -> raise Unchanged
      ):imp_conv),
    UNCHANGED_OF_FAIL_CTXIMPCONV o augment c,
    UNCHANGED_OF_FAIL_CTXIMPCONV o diminish c);;

let rec REPEAT_UNCHANGED_CTXIMPCONV =
  let rec map_all f xs x =
    match xs with
    |[] -> []
    |y::ys -> f y x :: map_all f ys x
  in
  fun (cs:imp_conv with_context list) ->
    With_context(
      ((fun v t ->
        let rec loop changed acc = function
          |[] when changed -> loop false acc cs
          |[] -> acc
          |c::cs' ->
              try
                let acc' = bind_ctximpconv c v acc in
                loop true acc' cs'
              with Unchanged -> loop changed acc cs'
        in
        loop false (IMP_REFL t) cs):imp_conv),
      REPEAT_UNCHANGED_CTXIMPCONV o map_all augment cs,
      REPEAT_UNCHANGED_CTXIMPCONV o map_all diminish cs);;


type atomic = Atomic | Non_atomic;;

let DEPTH_CTXIMPCONV =
  let bind c na v th =
    let t1,t2 = dest_imp (concl th) in
    match v with
    |Co -> IMP_TRANS (apply c na v t1) th
    |Contra -> IMP_TRANS th (apply c na v t2)
  in
  let rec self (c:(atomic->imp_conv) with_context) =
    With_context(
      (fun v t ->
        try
          let th1 = apply (SUB_CTXIMPCONV (self c)) v t in
          (try bind c Non_atomic v th1 with Failure _ -> th1)
        with
        | Failure "SUB_CTXIMPCONV" -> 
          let th1 = apply c Atomic v t in
          (try bind_ctximpconv (self c) v th1 with Failure _ -> th1)
        | Failure _ -> apply c Non_atomic v t),
      self o augment c,
      self o diminish c)
  in
  UNCHANGED_OF_FAIL_CTXIMPCONV o self;;

let TOP_DEPTH_CTXIMPCONV =
  let rec self (c:imp_conv with_context) =
    With_context(
      (fun v t ->
        try
          let th = apply c v t in
          try bind_ctximpconv (self c) v th with Failure _ -> th
        with Failure _ -> apply (SUB_CTXIMPCONV (self c)) v t),
      self o augment c,
      self o diminish c)
  in
  UNCHANGED_OF_FAIL_CTXIMPCONV o self;;

let ONCE_DEPTH_CTXIMPCONV =
  let rec self (c:(atomic->imp_conv) with_context) =
    With_context(
      (fun v t ->
        try apply (SUB_CTXIMPCONV (self c)) v t
        with
        | Failure "SUB_CTXIMPCONV" -> apply c Atomic v t
        | Failure _ -> apply c Non_atomic v t),
      self o augment c,
      self o diminish c)
  in
  UNCHANGED_OF_FAIL_CTXIMPCONV o self;;


let CTXIMPCONV_RULE (c:imp_conv with_context) th =
  MATCH_MP (apply c Contra (concl th)) th;;

let CTXIMPCONV_TAC (cnv:imp_conv with_context) : tactic =
  fun (asms,c as g) ->
    let cnv' = augment cnv (map (concl o snd) asms) in
    (MATCH_MP_TAC (apply cnv' Co c) THEN TRY (ACCEPT_TAC TRUTH)) g;;
