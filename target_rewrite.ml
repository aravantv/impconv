(* ========================================================================= *)
(*                                                                           *)
(*                       Target rewriting.                                   *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)

needs "imp_rewrite.ml";;


(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS WITH MULTIPLE RESULTS                           *)
(*****************************************************************************)

(* Multiple implicational conversion.
 *
 * Note to CPP reviewers: this is directly implemented with implicational 
 * conversions instead of conversions as presented in the paper.
 *)
type imp_mconv = Context.t -> Variance.t -> term -> thm list;;

let BIN_IMPMCONV sel var mkimp mkimpl mkimpr :imp_mconv->imp_mconv->imp_mconv =
  fun c1 c2 ctx v t ->
    let t1,t2 = sel t in
    map (C mkimpl t2) (c1 ctx (var v) t1) @ map (mkimpr t1) (c2 ctx v t2);;

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [CONJ_IMPMCONV ic1 ic2 Co (A /\ C)] returns
 * [B1 /\ C ==> A /\ C; ...; Bk /\ C ==> A /\ C; A /\ D1 ==> A /\ C; ...; Dn
 * ==> A /\ C].
 *
 * And similarly for the contravariant case.
 *)
let CONJ_IMPMCONV =
  BIN_IMPMCONV dest_conj I MKIMP_CONJ MKIMPL_CONJ MKIMPR_CONJ;;

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [B1 \/ C ==> A \/ C; ...; Bk \/ C ==> A \/ C; A \/ D1 ==> A \/ C; ...; Dn
 * ==> A \/ C].
 *
 * And similarly for the contravariant case.
 *)
let DISJ_IMPMCONV =
  BIN_IMPMCONV dest_disj I MKIMP_DISJ MKIMPL_DISJ MKIMPR_DISJ;;

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [(B1 ==> C) ==> (A ==> C); ...; (Bk ==> C) ==> (A ==> C); (A ==> D1) ==> (A
 * ==> C); ...; (A ==> Dn) ==> (A ==> C)].
 *
 * And similarly for the contravariant case.
 *)
let IMP_IMPMCONV = BIN_IMPMCONV dest_imp neg MKIMP_IMP MKIMPL_IMP MKIMPR_IMP;;

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * then [NOT_IMPMCONV ic Co ~A] returns [~B1 ==> ~A; ...; ~Bk ==> ~A].
 *
 * And similarly for the contravariant case.
 *)
let (NOT_IMPMCONV:imp_mconv->imp_mconv) =
  fun c ctx v t -> map MKIMP_NOT (c ctx (Variance.neg v) (dest_neg t));;

let QUANT_IMPMCONV mkimp sel :imp_mconv->imp_mconv =
  fun c ctx v t ->
    let x,b = sel t in
    map (mkimp x) (c ctx v b);;

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [FORALL_IMPMCONV ic Co (!x.A)] returns [(!x.B1) ==> (!x.A); ...;
 * (!x.Bk) ==> (!x.A)].
 *
 * And similarly for the contravariant case.
 *)
let FORALL_IMPMCONV = QUANT_IMPMCONV MKIMP_FORALL dest_forall;;

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [EXISTS_IMPMCONV ic Co (?x.A)] returns [(?x.B1) ==> (?x.A); ...;
 * (?x.Bk) ==> (?x.A)].
 *
 * And similarly for the contravariant case.
 *)
let EXISTS_IMPMCONV = QUANT_IMPMCONV MKIMP_EXISTS dest_exists;;

(* Applies a multiple implicational conversion on the subformula(s) of the
 * input term
 *)
let SUB_IMPMCONV:imp_mconv->imp_mconv =
  fun c ctx v t ->
    (match name_of (fst (strip_comb t)) with
    |"/\\" -> CONJ_IMPMCONV c 
    |"\//" -> DISJ_IMPMCONV c
    |"==>" -> IMP_IMPMCONV c 
    |"!" -> FORALL_IMPMCONV
    |"?" -> EXISTS_IMPMCONV
    |"~" -> NOT_IMPMCONV
    |_ -> failwith "SUB_IMPMCONV")
    c ctx v t;;

(* Applies a multiple implicational conversion once to the first suitable sub-term(s)
 * encountered in top-down order.
 *)
let ONCE_IMPMCONV:imp_mconv->imp_mconv =
  fun c ->
    let rec self ctx v t =
      try
        match SUB_IMPMCONV self ctx v t with
        |[] -> c ctx v t
        |_::_ as ths -> ths
      with _ -> c ctx v t
    in
  self;;


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSIONS                                         *)
(*****************************************************************************)

(* Multiple implicational conversion with hypotheses. *)
type mconv_with_hyp = term -> (thm * term list) list;;

(* Multiple conversion which returns all the possible rewrites (on one subterm
 * only) by one theorem.
 *
 * TODO: handle several theorems at a time.
 *)
let DEEP_IMP_REWR_MCONV:thm->Context.t->mconv_with_hyp =
  let COMB_MCONV c t =
    let l,r = dest_comb t in
    map (fun th,hs -> AP_THM th r,hs) (c l)
    @ map (fun th,hs -> AP_TERM l th,hs) (c r)
  and ABS_MCONV c t =
    let v,bod = dest_abs t in
    let ths = c bod in
    try map (fun th,hs -> ABS v th,hs) ths
    with Failure _ ->
      let gv = genvar(type_of v) in
      let f (gth,hs) =
        let gtm = concl gth in
        let l,r = dest_eq gtm in
        let v' = variant (frees gtm) v in
        let l' = alpha v' l and r' = alpha v' r in
        EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth,hs
      in
      let bod' = vsubst[gv,v] bod in
      map f (map (fun th,hs -> ABS gv th,hs) (c bod'))
  in
  let SUB_MCONV c = function
    |Comb(_,_) as t -> COMB_MCONV c t
    |Abs(_,_) as t -> ABS_MCONV c t
    |_ -> []
  in
  let rec top_depth c t = SUB_MCONV (top_depth c) t @ c t in
  fun th ->
    let cnv av t =
      try [REWRITES_IMPCONV (impconv_net_of_thm th empty_net) av t]
      with _ -> []
    in
    fun ctx t ->
      let av = Tset.union (Tset.variables t) (Context.variables_of ctx) in
      top_depth (cnv av) t;;

(* Takes a multiple conversion with hypotheses (which also takes a context as
 * parameter) and makes a multiple implicational conversion out of it.
 *
 * Basically extends [GENERAL_REWRITE_IMPCONV] to the multiple conversion
 * case.
 *)
let GENERAL_REWRITE_IMPMCONV:(Context.t->mconv_with_hyp)->imp_mconv =
  let IMP_IMP_SYM = TAUT `A==>B==>C <=> B==>A==>C` in
  let IMP_EXIST = GSYM LEFT_IMP_EXISTS_THM in
  fun cnv ctx v t ->
    let f (th,hyps) =
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
              MAP_CONCLUSION (itlist TRY_GEN vs) res
    in
    map f (cnv ctx t);;


(*****************************************************************************)
(* TARGET REWRITING                                                          *)
(*****************************************************************************)

(* Takes a theorem which results of an implicational conversion and applies a
 * multiple implicational conversion on the outcome.
 *)
let bind_impmconv (c:imp_mconv) ctx v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> map (C IMP_TRANS th) (c ctx v t1)
  |Contra -> map (IMP_TRANS th) (c ctx v t2);;

(* Target rewrite implicational conversion:
 * [TARGET_REWRITE_IMPCONV sths ts] is an implicational conversion which
 * applies all the possible implicational rewrites on the input term until
 * one of the resulting terms matches one of the terms in [ts].
 *
 * Note that we allow several target terms and not just one. See 
 * TARGET_REWRITE_TAC for a justification.
 *)
let TARGET_REWRITE_IMPCONV : thm list -> term list -> imp_conv =
  fun sths ->
    let one_step_one_th th ctx v uh =
      let f =
        ONCE_IMPMCONV o GENERAL_REWRITE_IMPMCONV o DEEP_IMP_REWR_MCONV
      in
      bind_impmconv (f th) ctx v uh
    in
    let flat l = uniq (itlist (merge thm_lt) l []) in
    let one_step ctx v uh =
      flat (map (fun f -> sort thm_lt (f ctx v uh)) (map one_step_one_th sths))
    in
    fun ts ctx v t ->
      let rec self ths =
        let pool = flat (map (one_step ctx v) ths) in
        let sel th = imp_conv_outcome th v in
        let is_one_sol g = (can o find_term o can o term_match []) g o sel in
        let is_sol = tryfind is_one_sol ts in
        try find is_sol pool
        with _ ->
          match pool with
          |[] -> failwith "TARGET_REWRITE_IMPCONV: no path found"
          |_::_ -> self pool
      in
      self [IMP_REFL t];;

(* Tactic version of it.
 *
 * Since the target theorem is preprocessed, it can yield several theorems.
 * Therefore, there is not just one possible target pattern but several.
 *)
let TARGET_REWRITE_TAC sths th =
  let sths' = flat (map preprocess sths) in
  let ths = preprocess th and (+) = THEN_IMPCONV in
  IMPCONV_TAC
  (TARGET_REWRITE_IMPCONV sths' (flat (map patterns_of_thm ths))
    + PURE_REWRITE_IMPCONV ths);;
