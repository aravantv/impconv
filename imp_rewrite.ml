(* ========================================================================= *)
(*                                                                           *)
(*                   Implicational rewriting.                                *)
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
(* REWRITE IMPLICATIONAL CONVERSION                                          *)
(*****************************************************************************)

(* Given a theorem [H1,...,Hn |- P ==> l = r],
 * returns the variables that occur in [P] and [r] but not in the rest.
 * Basically represents the variables that are introduced by the implicational
 * rewrite (similar status as variables occurring in the r.h.s. of a rewrite
 * but not in the l.h.s.).
 *)
let indep_vars th =
  let hs,c = dest_thm (SPEC_ALL th) in
  let p,c = dest_imp c in
  let all_vars = union (frees p) (frees (rhs c)) in
  let dep_vars = union (frees (lhs c)) (freesl hs) in
  subtract all_vars dep_vars;;

(* Given a list of variables to avoid [v1,...,vk], a theorem of the form
 * [hs |- !x1...xn. p ==> !y1...ym. l = r], and a term [t], matches [t] with
 * [l], yielding the substitution [s], and returns the theorem
 * [s(hs) |- !z1...zp. s(p) ==> s(l) = s(r)] where [z1], ..., [zp] are the
 * variables among [x1], ..., [xn], [y1], ..., [ym] that are not instantiated
 * by [s], and renamed so as to avoid [v1], ..., [vk].
 *)
let GEN_IMPREWR_CONV av =
  let pmatch = GEN_PART_MATCH (lhs o snd o strip_forall o snd o dest_imp) in
  fun th ->
    let pmatch' = pmatch th in
    fun t ->
      let th' = pmatch' t in
      VARIANT_RULE av (GENL (indep_vars th') th');;

(* A conversion which returns not only a theorem but also a list of terms
 * which is a sublist of the theorem hypotheses.
 *
 * See [IMPREWR_CONV] for an example.
 *)
type conv_with_hyp = term -> thm * term list;;

(* Takes a list of variables to avoid [av], a theorem [th] of the form
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t]
 * and returns a conversion with hypotheses defined as follows:
 * for a term [t], if [t] matches [l] with substitution [s], then return
 * the theorem [h1,...,hk,s(p) |- t = s(r)] and the the list containing only
 * [s(p)].
 *
 * The purpose of the conversion with hypothesis is to be able to distinguish
 * which hypothesis comes from the input theorem and which is added by the
 * conversion itself.
 *)
let IMPREWR_CONV:Tset.t->thm->conv_with_hyp =
  fun av th ->
    let f t = SPEC_ALL (GEN_IMPREWR_CONV av th t) in
    fun t ->
      let uh = f t in
      let u = fst (dest_imp (concl uh)) in
      UNDISCH uh,[u];;

(* Takes a theorem, a net of conversions with hypotheses (which also take
 * variables to avoid), and adds to the net the conversion(s) corresponding to
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
 * - ...
 *)
(* TODO remove trivially cyclic rewrites *)
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
              enter (l',C IMPREWR_CONV th)
            with _ -> I
          in
          let enter'' =
            try
              let _,l' = dest_forall l in
              enter (snd (strip_forall l'),C IMPREWR_CONV (GEQT_INTRO2 th))
            with _ -> I
          in
          enter' o enter'' o enter (l,C IMPREWR_CONV (GEQT_INTRO1 th))
    |l ->
        let enter' =
          if l = c then I
          else enter (l,fun _ -> REWR_CONV (MAP_FORALL_BODY GEN_EQT_INTRO th))
        in
        enter' o enter (c,fun _ -> REWR_CONV (GEN_EQT_INTRO th));;

(* Given a theorem returns the patterns corresponding to the conversions
 * generated by [impconv_net_of_thm].
 *)
let patterns_of_thm th =
  let c = concl th in
  match snd (strip_forall c) with
  |Comb(Comb(Const("=",_),l),_) -> [l]
  |Comb(Comb(Const("==>",_),_),l) ->
        let p1s = try [fst (dest_eq (snd (strip_forall l)))] with _ -> [] in
        let p2s = try [snd (strip_forall (snd (dest_forall l)))] with _ -> [] in
        l :: (p1s @ p2s)
  |l -> l :: if l=c then [] else [c];;

(* Apply a conversion net to the term at the top level, taking
 * avoided variables as parameter too.
 *)
let REWRITES_IMPCONV (net:(term list -> conv_with_hyp) net) avs t =
  try tryfind (fun c -> c avs t) (lookup t net)
  with Failure _ -> failwith "REWRITES_IMPCONV";;

extend_basic_rewrites [NOT_FORALL_THM;NOT_IMP];;

(* Conversion (with hypotheses) corresponding to implicational rewrite.
 * Takes several theorems as input and a context.
 * Goes deep.
 *)
let DEEP_IMPREWR_CONV:thm list->Context.t->conv_with_hyp =
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

(* Given a theorem [p ==> c], returns the implicational conversion which:
  * - in the covariant case, matches the input term [t] against [c] and returns
  *   [s(p) ==> t], where [s] is the matching substitution
  * - in the contravariant case, matches the input term [t] against [p] and returns
  *   [t ==> s(c)], where [s] is the matching substitution
  *)
let MATCH_MP_IMPCONV:thm->imp_conv =
  fun th _ -> function
    |Co -> GEN_PART_MATCH rand th
    |Contra -> GEN_PART_MATCH lhand th;;

(* Implicational conversion which fails if the input term does not appear in
 * the context, and otherwise returns:
 * - [t |- T ==> t] in the covariant case
 * - [|- t ==> T] in the contravariant case
 *
 * Used to remove an atom which occurs in the context.
 *)
let IMP_REFLCONV:imp_conv =
  fun ctx v t ->
    if t = T_ then failwith "IMP_REFLCONV"
    else
      if mem t (Context.terms_of ctx)
      then match v with Co -> DISCH T_ (ASSUME t) | Contra -> DISCH t TRUTH
      else failwith "IMP_REFLCONV";;

(* If the input term has the form [?x1...xk. P1 /\ ... /\ Pn] and there exists
 * in the context a term H which matches one of P1, ..., Pn, then returns the
 * theorem:
 * [H |- (?y1...yn. s(P1) /\ ... /\ s(Pn)) ==> ?x1...xk. P1 /\ ... /\ Pn]
 * where [s] is the matching substitution, [y1], ..., [yn] are the variables
 * that are not instantiated by [s], and [H] is removed from the [s(P1)], ...,
 * [s(Pn)].
 *
 * Used to remove an existential quantification if the context trivially
 * provides a witness.
 *)
let EXISTS_IMPCONV:imp_conv =
  let EXISTSs i p =
    let codom,dom = unzip i in
    let f i ps = vsubst [i] (snd (dest_exists (hd ps))) :: ps in
    let h::ps = rev_itlist f i [list_mk_exists(dom,p)] in
    rev_itlist EXISTS (zip ps (rev codom)) (ASSUME h)
  in
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

(* Takes a conversion with hypotheses (which also takes a context as
 * parameter) and makes an implicational conversion out of it.
 * Basically turns a rewrite with hypotheses into an implicational rewrite
 * withouth hypotheses.
 * Adds existential quantifications for variables introduced by the rewrite.
 *)
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

(* Applies the implicational rewrite, with context simplifications. *)
let PURE_REWRITE_IMPCONV ths =
  let (||) = ORELSE_IMPCONV in
  REDEPTH_IMPCONV (GENERAL_REWRITE_IMPCONV (DEEP_IMPREWR_CONV ths)
    || IMP_REFLCONV || EXISTS_IMPCONV);;

(* Applies the implicational rewrite once, with context simplifications. *)
let ONCE_PURE_REWRITE_IMPCONV ths =
  let (+) = THEN_IMPCONV and (||) = ORELSE_IMPCONV in
  ONCE_IMPCONV (GENERAL_REWRITE_IMPCONV (DEEP_IMPREWR_CONV ths))
  + REDEPTH_IMPCONV (IMP_REFLCONV || EXISTS_IMPCONV);;


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* Preprocessor. For now takes a theorem of the form [p ==> c1 /\ ... /\ ck]
 * and returns the list of theorems [p ==> c1], ..., [p ==> ck].
 *)
let preprocess = CONJUNCTS o IMPLY_AND;;

(* Final implicational conversion to use for implicational rewrite. *)
let REWRITE_IMPCONV = TRY_IMPCONV o PURE_REWRITE_IMPCONV o preprocess;;

(* Tactic for implicational rewrite. *)
let IMP_REWRITE_TAC ths =
  let tc = IMPCONV_TAC o CHANGED_IMPCONV o PURE_REWRITE_IMPCONV o preprocess in
  let tacs = map tc ths in
  REPEAT (CHANGED_TAC (MAP_EVERY TRY tacs));;
  
(* Tactic for implicational rewrite with assumptions. *)
let ASM_IMP_REWRITE_TAC = ASM IMP_REWRITE_TAC;;

(* Cases-like conversion for implicational theorems, i.e., for a theorem of
 * the form:
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t],
 * return [(p ==> t') /\ (~p ==> t)], where [t'] is the result of rewriting
 * [t] by [l=r].
 *)
let CASE_REWRITE_CONV =
  let lem = TAUT `(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\ (P ==> Q))` in
  let lem' = TAUT `(P ==> Q = R) ==> (Q <=> (P ==> R) /\ (~P ==> Q))` in
  fun th t ->
    let th,hyps = DEEP_IMPREWR_CONV [th] Context.empty t in
    let th' = DISCH_IMP_IMP hyps th in
    REWR_CONV (try MATCH_MP lem th' with _ -> MATCH_MP lem' th') t;;

(* Tactic version of it. *)
let CASE_REWRITE_TAC = CONV_TAC o CASE_REWRITE_CONV;;

