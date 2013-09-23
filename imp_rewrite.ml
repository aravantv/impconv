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
let GEN_IMPREWR_CONV avs =
  let sel = lhs o snd o strip_forall o snd o dest_imp in
  let pmatch = GEN_PART_MATCH_ALL sel in
  fun th ->
    let pmatch' = pmatch th in
    fun t ->
      let th' = pmatch' t in
      VARIANT_RULE avs (GENL (indep_vars th') th');;

(* A conversion which returns not only a theorem but also a list of terms
 * which is a sublist of the theorem hypotheses, and a list of terms which
 * are the variables newly introduced by the conversion.
 *
 * See [IMPREWR_CONV] for an example.
 *)
type annot_conv = term -> thm * term option * term list;;

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
let IMPREWR_CONV:Tset.t->thm->annot_conv =
  fun avs th ->
    let f t = SPEC_VARS (GEN_IMPREWR_CONV avs th t) in
    fun t ->
      let vs,uh = f t in
      let u = fst (dest_imp (concl uh)) in
      UNDISCH uh,Some u,Tset.of_list vs;;

let REWR_ANNOTCONV avs th t =
  let th' = PART_MATCH lhs th t in
  let _,t' = dest_binary_blind (concl th') in
  let new_vars = Tset.frees t' in
  let old_vars = Tset.union (Tset.frees t) (Tset.freesl (hyp th')) in
  th',None,Tset.subtract new_vars old_vars;;

let ORDER_ANNOTCONV cnv t =
  let th,_,_ as res = cnv t in
  let l,r = dest_binary_blind (concl th) in
  if term_order l r then res else failwith "ORDER_ANNOTCONV";;

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
let pat_cnv_of_thm th : (term * (term list->annot_conv)) =
  let th = SPEC_ALL th in
  let lconsts = freesl (hyp th) and c = concl th in
  match snd (strip_forall c) with
  |Comb(Comb(Const("=",_),l),r) as t -> 
      let matches = C (can o term_match lconsts) in
      if free_in l r or (matches l r & matches r l)
      then t,C REWR_ANNOTCONV (MAP_FORALL_BODY EQT_INTRO th)
      else l,C REWR_ANNOTCONV th
  |Comb(Comb(Const("==>",_),p),c) as t ->
      let matches = C (can o fo_term_match lconsts) in
      let imprewr_concl f = C IMPREWR_CONV (GEN_MAP_CONCLUSION f th) in
      (match c with
      |Comb(Comb(Const("=",_),l),r) ->
          if free_in l r or (matches l r & matches r l) or is_var l
          then 
            if matches p c
            then t, C REWR_ANNOTCONV (EQT_INTRO th)
            else c, imprewr_concl EQT_INTRO
          else l, C IMPREWR_CONV th
      |Comb(Const("~",_),l) -> l, imprewr_concl EQF_INTRO
      |l -> l, imprewr_concl EQT_INTRO)
  |Comb(Const("~",_),l) -> l, C REWR_ANNOTCONV (EQF_INTRO th)
  |Const("T",bool_ty) -> failwith "pat_cnv_of_thm"
  |l -> l, C REWR_ANNOTCONV (EQT_INTRO th);;

let impconv_net_of_thm th =
  try
    let p,c = pat_cnv_of_thm th in
    let vs = Tset.freesl (hyp th) in
    Fo_nets.enter vs (p,(c,vs,th))
  with Failure _ -> I;;

let patterns_of_thm = fst o pat_cnv_of_thm;;

(* Apply a conversion net to the term at the top level, taking
 * avoided variables as parameter too.
 *)
let REWRITES_IMPCONV
  (net:((term list -> annot_conv) * Tset.t * thm) Fo_nets.t) avs t =
  tryfind (fun c,_,_ -> c avs t) (Fo_nets.lookup t net);;

extend_basic_rewrites [NOT_FORALL_THM;NOT_IMP];;

let IMPREWR_CTXCONV :thm list -> (atomic->annot_conv) with_context =
  let rec top_depth c avs t =
    let rec (++) c1 c2 avs t =
      match c1 avs t with
      |_,Some _,_ as c1t -> c1t
      |th1,None,vs1 as c1t ->
        (try
          let th2,ho2,vs2 = c2 (Tset.union vs1 avs) (rand (concl th1)) in
          TRANS th1 th2, ho2, Tset.union vs1 vs2
        with Failure _ -> c1t)
    and (+) c1 c2 avs t = try (c1 ++ c2) avs t with Failure _ -> c2 avs t
    and COMB_QCONV c avs l r =
      try
        match c avs l with
        |th,(Some _ as ho),vs -> AP_THM th r,ho,vs
        |th1,None,vs1 ->
          (try
            let th2,ho2,vs2 = c (Tset.union vs1 avs) r in
            MK_COMB (th1,th2), ho2, Tset.union vs1 vs2
          with Failure _ -> AP_THM th1 r,None,vs1)
      with Failure _ ->
        let th2,ho2,vs2 = c avs r in
        AP_TERM l th2,ho2,vs2
    in
    let SUB_QCONV c avs t =
      match t with
      |Comb(l,r) -> COMB_QCONV c avs l r
      |Abs(v,_) ->
          let ho = ref None and vs = ref [] in
          let c' t =
            let th,ho',vs' = c (Tset.insert avs v) t in
            ho := ho'; vs := vs'; th
          in
          let res = ABS_CONV c' t in
          res,!ho,!vs
      |_ -> failwith "SUB_QCONV"
    in
    let rec (!) c avs t = (c ++ !c) avs t in
    (!c + (SUB_QCONV (top_depth c) ++ top_depth c)) avs t
  in
  let basic_cnv t = REWRITES_CONV (basic_net ()) t,None,[] in
  let rec self net ths =
    let avs = Tset.flat_revmap (Tset.freesl o hyp) ths in
    let cnv avs t =
      try REWRITES_IMPCONV net avs t with Failure _ -> basic_cnv t
    in
    With_context(
      (fun a t ->
        let f = match a with Atomic -> top_depth | Non_atomic -> I in
        f cnv (Tset.union (Tset.frees t) avs) t),
      (fun ts -> 
        let ths' = map ASSUME ts in
        (*let ths'' = ths' @ GMATCH_MPS ths ths' in*)
        let ths'' = MP_CLOSURE ths' ths' @ ths' @ MP_CLOSURE ths ths' in
        self (itlist impconv_net_of_thm ths'' net) (ths'' @ ths)),
      (fun v ->
        let ths = ref [] in
        let f (_,vs,th) =
          if not (Tset.mem v vs) then (ths := th :: !ths; true) else false
        in
        let net' = Fo_nets.filter f net in
        self net' !ths))
  in
  fun ths -> self (itlist impconv_net_of_thm ths Fo_nets.empty_net) ths;;


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Takes a conversion with hypotheses (with context) and makes an
 * implicational conversion out of it.
 * Basically turns a rewrite with hypotheses into an implicational rewrite
 * withouth hypotheses.
 * Adds existential quantifications for variables introduced by the rewrite.
 *)
let rec REWR_IMPCONV_OF_CONV =
  let IMP_SYM = REWR_RULE (TAUT `A==>B==>C <=> B==>A==>C`) in
  let IMP_EXIST = GSYM LEFT_IMP_EXISTS_THM in
  let TRY_GEN v th = try GEN v th with Failure _ -> th in
  fun (c:(atomic -> annot_conv) with_context) ->
    With_context(
      ((fun a v t ->
        let th,ho,new_vars = apply c a t in
        let th1,th2 = EQ_IMP_RULE th in
        let res =
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
        let t1,t2 = dest_imp (concl res) in
        if t1 = t2 then raise Unchanged else res):atomic->imp_conv),
      REWR_IMPCONV_OF_CONV o augment c,
      REWR_IMPCONV_OF_CONV o diminish c);;

(* Applies the implicational rewrite, with context simplifications. *)
let REWRITE_CTXIMPCONV =
  DEPTH_CTXIMPCONV o REWR_IMPCONV_OF_CONV o IMPREWR_CTXCONV;;
    

(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* Preprocessor. For now takes a theorem of the form [p ==> c1 /\ ... /\ ck]
 * and returns the list of theorems [p ==> c1], ..., [p ==> ck].
 *)
let preprocess = CONJUNCTS o IMPLY_AND;;

(* Tactic for implicational rewrite. *)
let IMP_REWRITE_TAC ths = 
  CTXIMPCONV_TAC (REWRITE_CTXIMPCONV (flat (map preprocess ths)));;

let SEQ_IMP_REWRITE_TAC ths =
  let cnv =
    match ths with
    |[] -> REWRITE_CTXIMPCONV [TRUTH]
    |[th] -> REWRITE_CTXIMPCONV (preprocess th)
    |_::_ ->
        let fcnv = REWRITE_CTXIMPCONV o preprocess in
        REPEAT_UNCHANGED_CTXIMPCONV (map fcnv ths)
  in
  CTXIMPCONV_TAC cnv;;
  
(* Tactic for implicational rewrite with assumptions. *)
let ASM_IMP_REWRITE_TAC = ASM IMP_REWRITE_TAC;;

(* Cases-like conversion for implicational theorems, i.e., for a theorem of
 * the form:
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t],
 * return [(p ==> t') /\ (~p ==> t)], where [t'] is the result of rewriting
 * [t] by [l=r].
 *)
let rec CASE_REWR_IMPCONV_OF_CONV =
  let MP_TAUT th = MATCH_MP (TAUT th) in
  let MP_LEM1 = MP_TAUT `(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\ (P ==> Q))` in
  let MP_LEM2 = MP_TAUT `(P ==> Q = R) ==> (Q <=> (P ==> R) /\ (~P ==> Q))` in
  fun (c:(atomic -> annot_conv) with_context) ->
    With_context(
      (fun a v t ->
        match apply c a t with
        |_,None,_ -> failwith "CASE_REWR_IMPCONV_OF_CONV"
        |th,Some h,_ ->
            let th' = DISCH h th in
            let th'' = try MP_LEM1 th' with Failure _ -> MP_LEM2 th' in
            imp_conv_of_conv (REWR_CONV th'') v t),
      CASE_REWR_IMPCONV_OF_CONV o augment c,
      CASE_REWR_IMPCONV_OF_CONV o diminish c);;

let CASE_REWRITE_CTXIMPCONV =
  ONCE_DEPTH_CTXIMPCONV o CASE_REWR_IMPCONV_OF_CONV o IMPREWR_CTXCONV;;

(* Tactic version of it. *)
let CASE_REWRITE_TAC = CTXIMPCONV_TAC o CASE_REWRITE_CTXIMPCONV o preprocess;;

