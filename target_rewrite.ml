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

(* Multiple implicational conversion. *)
type imp_mconv = Variance.t -> term -> thm list;;

let mapply_with_context c ctx v t =
  map (DISCH_CONJ ctx) (apply (augment c (Tset.strip_conj ctx)) v t);;

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [CONJ_IMPMCONV ic1 ic2 Co (A /\ C)] returns
 * [B1 /\ C ==> A /\ C; ...; Bk /\ C ==> A /\ C; A /\ D1 ==> A /\ C; ...; Dn
 * ==> A /\ C].
 *
 * And similarly for the contravariant case.
 *)
let rec CONJ_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_conj t in
      let left,right =
        match v with
        |Co -> MKIMPL_CONJ_CO2_CTXT,MKIMPR_CONJ_CO_CTXT
        |Contra -> MKIMPL_CONJ_CONTRA_CTXT,MKIMPR_CONJ_CONTRA_CTXT
      in
      let th1s = map left (mapply_with_context c t2 v t1) in
      let th2s = map right (mapply_with_context c t1 v t2) in
      th1s @ th2s),
    CONJ_CTXIMPMCONV o augment c,
    CONJ_CTXIMPMCONV o diminish c);;

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [B1 \/ C ==> A \/ C; ...; Bk \/ C ==> A \/ C; A \/ D1 ==> A \/ C; ...; Dn
 * ==> A \/ C].
 *
 * And similarly for the contravariant case.
 *)
let rec DISJ_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_disj t in
      let th1s = map (C MKIMPL_DISJ t2) (apply c v t1) in
      let th2s = map (MKIMPR_DISJ t1) (apply c v t2) in
      th1s @ th2s),
    DISJ_CTXIMPMCONV o augment c,
    DISJ_CTXIMPMCONV o diminish c);;

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [(B1 ==> C) ==> (A ==> C); ...; (Bk ==> C) ==> (A ==> C); (A ==> D1) ==> (A
 * ==> C); ...; (A ==> Dn) ==> (A ==> C)].
 *
 * And similarly for the contravariant case.
 *)
let rec IMP_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_imp t in
      let th1s = map (C MKIMPL_IMP t2) (apply c (Variance.neg v) t1) in
      let th2s = map MKIMPR_IMP_CTXT (mapply_with_context c t1 v t2) in
      th1s @ th2s),
    CONJ_CTXIMPMCONV o augment c,
    CONJ_CTXIMPMCONV o diminish c);;

let rec IFF_CTXIMPCONV (c:imp_mconv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_iff t in
      let left,right =
        match v with
        |Co -> MKIMPL_CO_IFF,MKIMPR_CO_IFF
        |Contra -> MKIMPL_CONTRA_IFF,MKIMPR_CONTRA_IFF
      in
      let th1s = map left (apply c v (mk_imp(t1,t2))) in
      let th2s = map right (apply c v (mk_imp(t2,t1))) in
      th1s @ th2s):imp_mconv),
    IFF_CTXIMPCONV o augment c,
    IFF_CTXIMPCONV o diminish c);;

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * then [NOT_IMPMCONV ic Co ~A] returns [~B1 ==> ~A; ...; ~Bk ==> ~A].
 *
 * And similarly for the contravariant case.
 *)
let rec NOT_CTXIMPMCONV (c:imp_mconv with_context) : imp_mconv with_context =
  With_context(
    (fun v t ->
      map MKIMP_NOT (try_list (apply c (Variance.neg v)) (dest_neg t))),
    NOT_CTXIMPMCONV o augment c,
    NOT_CTXIMPMCONV o diminish c);;

let rec QUANT_CTXIMPMCONV mkimp sel (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let x,b = sel t in
      let c' = diminish c x in
      map (mkimp x) (try_list (apply c' v) b)),
    QUANT_CTXIMPMCONV mkimp sel o augment c,
    QUANT_CTXIMPMCONV mkimp sel o diminish c);;

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [FORALL_IMPMCONV ic Co (!x.A)] returns [(!x.B1) ==> (!x.A); ...;
 * (!x.Bk) ==> (!x.A)].
 *
 * And similarly for the contravariant case.
 *)
let FORALL_CTXIMPMCONV = QUANT_CTXIMPMCONV MKIMP_FORALL dest_forall;;

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [EXISTS_IMPMCONV ic Co (?x.A)] returns [(?x.B1) ==> (?x.A); ...;
 * (?x.Bk) ==> (?x.A)].
 *
 * And similarly for the contravariant case.
 *)
let EXISTS_CTXIMPMCONV = QUANT_CTXIMPMCONV MKIMP_EXISTS dest_exists;;

(* Applies a multiple implicational conversion on the subformula(s) of the
 * input term
 *)
let rec SUB_CTXIMPMCONV =
  let iff_ty = `:bool->bool->bool` in
  fun c ->
  With_context(
    ((fun v t ->
      let n,ty = dest_const (fst (strip_comb t)) in
      apply
        ((match n with
        |"==>" -> IMP_CTXIMPMCONV
        |"/\\" -> CONJ_CTXIMPMCONV
        |"\//" -> DISJ_CTXIMPMCONV
        |"!" -> FORALL_CTXIMPMCONV
        |"?" -> EXISTS_CTXIMPMCONV
        |"~" -> NOT_CTXIMPMCONV
        |"=" when ty = iff_ty -> IFF_CTXIMPCONV
        |_ -> failwith "SUB_CTXIMPMCONV") c) v t):imp_mconv),
    SUB_CTXIMPMCONV o augment c,
    SUB_CTXIMPMCONV o diminish c);;


(* Applies a multiple implicational conversion once to the first suitable sub-term(s)
 * encountered in bottom-up order.
 *)
let rec DEPTH_CTXIMPMCONV (c : (atomic->imp_mconv) with_context) =
  With_context(
    (fun v t ->
      try
        let ths = apply (SUB_CTXIMPMCONV (DEPTH_CTXIMPMCONV c)) v t in
        apply c Non_atomic v t @ ths
      with Failure "SUB_CTXIMPMCONV" ->
        (apply c Atomic v t)),
      DEPTH_CTXIMPMCONV o augment c,
      DEPTH_CTXIMPMCONV o diminish c);;


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSIONS                                         *)
(*****************************************************************************)

(* Multiple implicational conversion with hypotheses. *)
type annot_mconv = term -> (thm * term option * term list) list;;

(* Takes a theorem, a net of conversions with hypotheses (which also take
 * variables to avoid), and adds to the net the conversion corresponding to
 * the theorem.
 *
 * Special cases:
 * - usual term rewriting is handled with [REWR_CONV] instead of introducing 
 *   a fake premise. Might be useful though to introduce a fake premise since
 *   the conversion would benefit from a better handling of variables occurring
 *   in the r.h.s. but not in the l.h.s.
 * - a theorem of the form [p ==> c] where [c] is not equational is turned into
 *   [p ==> c = T]
 * - a theorem of the form [p ==> ~c] is turned into [p ==> c = F]
 *)
let target_pat_cnv_of_thm th : (term * (term list->annot_conv)) =
  let th = SPEC_ALL th in
  let c = concl th in
  match snd (strip_forall c) with
  |Comb(Comb(Const("=",_),l),_) -> l,C REWR_ANNOTCONV th
  |Comb(Comb(Const("==>",_),_),c) ->
      let pat,th' =
        match c with
        |Comb(Comb(Const("=",_),l),_) -> l, th
        |Comb(Const("~",_),l) -> l, GEN_MAP_CONCLUSION EQF_INTRO th
        |l -> l, GEN_MAP_CONCLUSION EQT_INTRO th
      in
      pat, C IMPREWR_CONV th'
  |Comb(Const("~",_),l) -> l, C REWR_ANNOTCONV (EQF_INTRO th)
  |Const("T",bool_ty) -> failwith "target_pat_cnv_of_thm"
  |l -> l, C REWR_ANNOTCONV (EQT_INTRO th);;

let target_impconv_net_of_thm th =
  try
    let p,c = target_pat_cnv_of_thm th in
    let vs = Tset.freesl (hyp th) in
    Fo_nets.enter vs (p,(c,vs,th))
  with Failure _ -> I;;

let target_patterns_of_thm = fst o target_pat_cnv_of_thm;;

(* Multiple conversion which returns all the possible rewrites (on one subterm
 * only) by one theorem.
 *)

let DEEP_IMP_REWR_MCONV:thm list->(atomic->annot_mconv) with_context =
  let map_fst f (x,y,z) = f x,y,z in
  let COMB_MCONV c l r =
    map (map_fst (C AP_THM r)) (c l) @ map (map_fst (AP_TERM l)) (c r)
  and ABS_MCONV c v b =
    let ths = c b in
    try map (map_fst (ABS v)) ths
    with Failure _ ->
      let gv = genvar(type_of v) in
      let f (gth,ho,vs) =
        let gtm = concl gth in
        let l,r = dest_eq gtm in
        let v' = variant (frees gtm) v in
        let l' = alpha v' l and r' = alpha v' r in
        EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth,ho,vs
      in
      let b' = vsubst[gv,v] b in
      map f (map (map_fst (ABS gv)) (c b'))
  in
  let SUB_MCONV c = function
    |Comb(l,r) -> COMB_MCONV c l r
    |Abs(v,b) -> ABS_MCONV c v b
    |Const _ | Var _ -> []
  in
  let rec top_depth c t = SUB_MCONV (top_depth c) t @ c t in
  let REWRITES_IMPCONV (net:((term list -> annot_conv) * Tset.t * thm) Fo_nets.t) avs t =
    mapfilter (fun c,_,_ -> c avs t) (Fo_nets.lookup t net)
  in
  let rec self net ths =
    let avs = Tset.flat_revmap (Tset.freesl o hyp) ths in
    With_context(
      (fun a t ->
        let avs' = Tset.union (Tset.frees t) avs in
        let cnv t = REWRITES_IMPCONV net avs' t in
        let f =
          match a with
          |Atomic -> top_depth
          |Non_atomic -> (fun cnv avs -> cnv avs)
        in
        f cnv t),
      (fun _ -> self net ths),
      (fun v ->
        let ths = ref [] in
        let f (_,vs,th) =
          if not (Tset.mem v vs) then (ths := th :: !ths; true) else false
        in
        let net' = Fo_nets.filter f net in
        self net' !ths))
  in
  fun ths ->
    self (itlist target_impconv_net_of_thm ths Fo_nets.empty_net) ths;;

(* Takes a multiple conversion with hypotheses (which also takes a context as
 * parameter) and makes a multiple implicational conversion out of it.
 *
 * Basically extends [GENERAL_REWRITE_IMPCONV] to the multiple conversion
 * case.
 *)
let rec REWR_IMPMCONV_OF_MCONV =
  let IMP_SYM = REWR_RULE (TAUT `A==>B==>C <=> B==>A==>C`) in
  let IMP_EXIST = GSYM LEFT_IMP_EXISTS_THM in
  let TRY_GEN v th = try GEN v th with Failure _ -> th in
  fun (c:(atomic -> annot_mconv) with_context) ->
    With_context(
      ((fun a v t ->
        let f (th,ho,new_vars) =
          let th1,th2 = EQ_IMP_RULE th in
          match v with
          |Co -> 
              let p,th2' = UNDISCH_TERM th2 in
              let rec exists_intro = function
                |[] -> DISCH_IMP_IMP (p::list_of_option ho) th2'
                |v::vs -> 
                    let th = exists_intro vs in
                    try REWR_RULE IMP_EXIST (GEN v th) with Failure _ -> th
              in
              exists_intro new_vars
          |Contra ->
              let th1' =
                match ho with None -> th1 | Some h -> IMP_SYM (DISCH h th1)
              in
              match new_vars with
              |[] -> th1'
              |_::_ -> MAP_CONCLUSION (itlist TRY_GEN new_vars) th1'
        in
        map f (apply c a t)):atomic->imp_mconv),
      REWR_IMPMCONV_OF_MCONV o augment c,
      REWR_IMPMCONV_OF_MCONV o diminish c);;


(*****************************************************************************)
(* TARGET REWRITING                                                          *)
(*****************************************************************************)

let EXISTS_CTXIMPCONV:imp_conv with_context =
  let EXISTSs i p =
    let codom,dom = unzip i in
    let f i ps = vsubst [i] (snd (dest_exists (hd ps))) :: ps in
    let h::ps = rev_itlist f i [list_mk_exists(dom,p)] in
    rev_itlist EXISTS (zip ps (rev codom)) (ASSUME h)
  in
  let LEFT_FORALL_IMP = REWR_RULE LEFT_FORALL_IMP_THM in
  let rec self ts =
    With_context
    ((fun v t ->
      match v,t with
      |Co,Comb(Const("?",_),_) ->
          let vs,b = strip_exists t in
          let bs = strip_conj b in
          let hmatch (n,b) =
            match partition (C mem vs) (variables b) with
            |[],_ -> failwith "EXISTS_CTXIMPCONV"
            |_::_ as lvs,lcs ->
                fun h ->
                  match term_match lcs b h with
                  |_,i,j when filter (uncurry (<>)) j = [] ->
                      (if i = [] then zip lvs lvs else i),n
                  |_ -> failwith "EXISTS_CTXIMPCONV"
          in
          let s,n = tryfind_fun (mapfilteri (curry (tryfind o hmatch)) bs) ts in
          let th = EXISTSs (map (fun v -> rev_assocd v s v,v) vs) b in
          let th' = DISCH_HD th in
          let h = fst (dest_imp (concl th')) in
          (match strip_conj h with
          |[] -> assert false
          |[h] -> DISCH T_ th
          |_::_ as hs ->
            let hs1,h'::hs2 = chop_list n hs in
            let hs_th = CONJ_ACI_RULE (mk_eq(h,list_mk_conj (h'::(hs1@hs2)))) in
            let th1 = CONV_RULE (LAND_CONV (REWR_CONV hs_th)) th' in
            let th2 = UNDISCH (CONV_RULE (REWR_CONV IMP_CONJ) th1) in
            let vs' = subtract vs (map snd s) in
            let f v th = try LEFT_FORALL_IMP (GEN v th) with Failure _ -> th in
            itlist f vs' th2)
      |_ -> failwith "EXISTS_CTXIMPCONV"),
      (fun ts' -> self (Tset.union ts' ts)),
      (fun _ -> self ts))
  in
  self [];;

(* Takes a theorem which results of an implicational conversion and applies a
 * multiple implicational conversion on the outcome.
 *)
let bind_impmconv (c:imp_mconv) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> map (C IMP_TRANS th) (c v t1)
  |Contra -> map (IMP_TRANS th) (c v t2);;


(* Target rewrite implicational conversion:
 * [TARGET_REWRITE_IMPCONV sths ts] is an implicational conversion which
 * applies all the possible implicational rewrites on the input term until
 * one of the resulting terms matches one of the terms in [ts].
 *
 * Note that we allow several target terms and not just one. See 
 * TARGET_REWRITE_TAC for a justification.
 *)
let TARGET_REWRITE_IMPCONV : thm list -> term list -> imp_conv =
  let PRE = apply (TRY_CTXIMPCONV (REWRITE_CTXIMPCONV [])) in
  let POST = TRY_CTXIMPCONV (TOP_DEPTH_CTXIMPCONV EXISTS_CTXIMPCONV) in
  fun sths ->
    let one_step_sths v uh =
      let pre v th = try bind_impconv PRE v th with Unchanged -> th in
      let post v = bind_ctximpconv POST v in
      let f =
        DEPTH_CTXIMPMCONV o REWR_IMPMCONV_OF_MCONV o DEEP_IMP_REWR_MCONV
      in
      map (post v) (bind_impmconv (apply (f sths)) v (pre v uh))
    in
    let flat l = uniq (itlist (merge thm_lt) l []) in
    fun ts v t ->
      let rec self ths =
        let pool = flat (map (mergesort thm_lt o one_step_sths v) ths) in
        let sel th = imp_conv_outcome th v in
        let is_one_sol g = (can o find_term o can o fo_term_match []) g o sel in
        let is_sol th = tryfind is_one_sol ts th in
        try bind_ctximpconv POST v (find is_sol pool)
        with _ ->
          match pool with
          |[] -> failwith "TARGET_REWRITE_IMPCONV: no path found"
          |_::_ -> self (map (bind_ctximpconv POST v) pool)
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
  (TARGET_REWRITE_IMPCONV sths' (map patterns_of_thm ths)
    + imp_conv_of_ctx_imp_conv (REWRITE_CTXIMPCONV ths));;

let HINT_EXISTS_TAC = CTXIMPCONV_TAC (TOP_DEPTH_CTXIMPCONV EXISTS_CTXIMPCONV);;
