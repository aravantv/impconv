(* ========================================================================= *)
(*                                                                           *)
(*       Reasoning in order to match a goal term.                            *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)

needs "imp_conv.ml";;


(*****************************************************************************)
(* UTILS                                                                     *)
(*****************************************************************************)

let thm_lt (th1:thm) th2 = th1 < th2;;

let flat' lt l = itlist (merge lt) l [];;


(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS WITH MULTIPLE RESULTS                           *)
(*****************************************************************************)

type imp_convs = Context.t -> Variance.t -> term -> thm list;;

let BIN_IMPCONVS sel var mkimp mkimpl mkimpr :imp_convs->imp_convs->imp_convs =
  fun c1 c2 ctx v t ->
    let t1,t2 = sel t in
    map (C mkimpl t2) (c1 ctx (var v) t1) @ map (mkimpr t1) (c2 ctx v t2);;

let CONJ_IMPCONVS = BIN_IMPCONVS dest_conj I MKIMP_CONJ MKIMPL_CONJ MKIMPR_CONJ;;
let DISJ_IMPCONVS = BIN_IMPCONVS dest_disj I MKIMP_DISJ MKIMPL_DISJ MKIMPR_DISJ;;
let IMP_IMPCONVS = BIN_IMPCONVS dest_imp neg MKIMP_IMP MKIMPL_IMP MKIMPR_IMP;;

let (NOT_IMPCONVS:imp_convs->imp_convs) =
  fun c ctx v t -> map MKIMP_NOT (c ctx (Variance.neg v) (dest_neg t));;

let QUANT_IMPCONVS mkimp sel :imp_convs->imp_convs =
  fun c ctx v t ->
    let x,b = sel t in
    map (mkimp x) (c ctx v b);;

let FORALL_IMPCONVS = QUANT_IMPCONVS MKIMP_FORALL dest_forall;;
let EXISTS_IMPCONVS = QUANT_IMPCONVS MKIMP_EXISTS dest_exists;;

let SUB_IMPCONVS:imp_convs->imp_convs =
  fun c ctx v t ->
    (match name_of (fst (strip_comb t)) with
    |"/\\" -> CONJ_IMPCONVS c 
    |"\//" -> DISJ_IMPCONVS c
    |"==>" -> IMP_IMPCONVS c 
    |"!" -> FORALL_IMPCONVS
    |"?" -> EXISTS_IMPCONVS
    |"~" -> NOT_IMPCONVS
    |_ -> failwith "SUB_IMPCONVS")
    c ctx v t;;

let ONESTEP_IMPCONVS:imp_convs->Context.t->Variance.t->term->thm list =
  fun c ->
    let rec self ctx v t =
      try
        match SUB_IMPCONVS self ctx v t with
        |[] -> c ctx v t
        |_::_ as ths -> ths
      with _ -> c ctx v t
    in
  self;;


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSIONS                                         *)
(*****************************************************************************)

type convs_with_hyp = term -> (thm * term list) list;;

let DEEP_IMP_REWR_CONVS:thm->Context.t->convs_with_hyp =
  let COMB_CONVS c t =
    let l,r = dest_comb t in
    map (fun th,hs -> AP_THM th r,hs) (c l)
    @ map (fun th,hs -> AP_TERM l th,hs) (c r)
  and ABS_CONVS c t =
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
  let SUB_CONVS c = function
    |Comb(_,_) as t -> COMB_CONVS c t
    |Abs(_,_) as t -> ABS_CONVS c t
    |_ -> []
  in
  let rec top_depth c t = SUB_CONVS (top_depth c) t @ c t in
  fun th ->
    let cnv av t =
      try [REWRITES_IMPCONV (impconv_net_of_thm th empty_net) av t]
      with _ -> []
    in
    fun ctx t ->
      let av = Tset.union (Tset.variables t) (Context.variables_of ctx) in
      top_depth (cnv av) t;;

let GENERAL_REWRITE_IMPCONVS:(Context.t->convs_with_hyp)->imp_convs =
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
(* GOAL MATCHING                                                             *)
(*****************************************************************************)

let bind_impconvs (c:imp_convs) ctx v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> map (C IMP_TRANS th) (c ctx v t1)
  |Contra -> map (IMP_TRANS th) (c ctx v t2);;

let GOAL_MATCH_REWRITE_IMPCONV : thm list -> term list -> imp_conv =
  fun ths ->
    let one_step_one_th th ctx v uh =
      let f =
        ONESTEP_IMPCONVS o GENERAL_REWRITE_IMPCONVS o DEEP_IMP_REWR_CONVS
      in
      bind_impconvs (f th) ctx v uh
    in
    let flat l = uniq (itlist (merge thm_lt) l []) in
    let one_step ctx v uh =
      flat (map (fun f -> sort thm_lt (f ctx v uh)) (map one_step_one_th ths))
    in
    fun gs ctx v t ->
      let rec self ths =
        let pool = flat (map (one_step ctx v) ths) in
        let sel th = imp_conv_outcome th v in
        let is_one_sol g = (can o find_term o can o term_match []) g o sel in
        let is_sol = tryfind is_one_sol gs in
        try find is_sol pool
        with _ ->
          match pool with
          |[] -> failwith "GOAL_MATCH_REWRITE_IMPCONV: no path found"
          |_::_ -> self pool
      in
      self [IMP_REFL t];;

let GOAL_MATCH_REWRITE_TAC eqs th =
  let eqs' = flat (map preprocess eqs) in
  let ths = preprocess th and (+) = THEN_IMPCONV in
  IMPCONV_TAC
  (GOAL_MATCH_REWRITE_IMPCONV eqs' (flat (map patterns_of_thm ths))
    + PURE_REWRITE_IMPCONV ths);;
