(* ========================================================================= *)
(*                                                                           *)
(*           Library of complex function vector spaces.                      *)
(*                                                                           *)
(*   (c) Copyright, Mohamed Yousri Mahmoud & Vincent Aravantinos, 2012-2013  *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*          Contact: <mosolim@ece.concordia.ca>, <vincent@ece.concordia.ca>  *)
(*                                                                           *)
(* ========================================================================= *)


needs "Multivariate/make_complex.ml";;
#cd "..";;
needs "target_rewrite.ml";;
#cd "example";;
needs "utils.ml";;

(* ------------------------------------------------------------------------- *)
(* EMBEDDING OF REALS IN COMPLEX NUMBERS                                     *)
(* ------------------------------------------------------------------------- *)

let real_of_complex = new_definition
  `real_of_complex c = @r. c = Cx r`;;

let REAL_OF_COMPLEX = prove
  (`!c. real c ==> Cx(real_of_complex c) = c`,
  MESON_TAC[REAL;real_of_complex]);;

let REAL_OF_COMPLEX_RE = prove
  (`!c. real c ==> real_of_complex c = Re c`,
  MESON_TAC[RE_CX;REAL_OF_COMPLEX]);;

let REAL_OF_COMPLEX_CX = prove
  (`!r. real_of_complex (Cx r) = r`,
  SIMP_TAC[REAL_CX;REAL_OF_COMPLEX_RE;RE_CX]);;

let REAL_OF_COMPLEX_NORM = prove
  (`!c. real c ==> norm c = abs (real_of_complex c)`,
  SIMP_TAC[REAL_NORM;REAL_OF_COMPLEX_RE]);;

let REAL_OF_COMPLEX_ADD = prove
  (`!x y. real x /\ real y ==>
    real_of_complex (x+y) = real_of_complex x + real_of_complex y`,
  MESON_TAC[REAL_ADD;REAL_OF_COMPLEX_RE;RE_ADD]);;

let REAL_MUL = prove
  (`!x y. real x /\ real y ==> real (x*y)`,
  REWRITE_TAC[real] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let REAL_OF_COMPLEX_MUL = prove
  (`!x y. real x /\ real y ==>
    real_of_complex (x*y) = real_of_complex x * real_of_complex y`,
  MESON_TAC[REAL_MUL;REAL_OF_COMPLEX;CX_MUL;REAL_OF_COMPLEX_CX]);;

let NORM2_ADD_REAL = prove
  (`!x y. real x /\ real y ==>
    norm (x + ii * y) pow 2 = norm x pow 2 + norm y pow 2`,
  SIMP_TAC[real;complex_norm;RE_ADD;IM_ADD;RE_MUL_II;IM_MUL_II;REAL_NEG_0;
    REAL_ADD_LID;REAL_ADD_RID;REAL_POW_ZERO;ARITH_RULE `~(2=0)`;REAL_LE_POW_2;
    SQRT_POW_2;REAL_LE_ADD]);;

let real_thms,add_real_thm,add_real_thms = updatable_thms ();;

let REAL_TAC g =
  (IMP_REWRITE_TAC (real_thms ())
  ORELSE (REWRITE_TAC[real] THEN GCONV_TAC COMPLEX_FIELD)) g;;

add_real_thm REAL_MUL;;


(* ------------------------------------------------------------------------- *)
(* MAP OVER FUNCTIONS                                                        *)
(* ------------------------------------------------------------------------- *)

let fun_map2 = new_definition
  `fun_map2 (f:B->C->D) (g1:A->B) (g2:A->C) = \x. f (g1 x) (g2 x)`;;

let FUN_MAP2_THM = prove
  (`!f g1 g2 x. fun_map2 f g1 g2 x = f (g1 x) (g2 x)`,
  REWRITE_TAC[fun_map2]);;

let K_DEF = new_definition
  `K (x:A) = \y:B. x`;;

let K_THM = prove
  (`!x y. K x y = x`,
  REWRITE_TAC[K_DEF]);;

let fun_map_defs = CONJS [K_DEF;o_DEF;fun_map2];;

let FUN_MAP_THMS = CONJS [K_THM;o_THM;FUN_MAP2_THM];;


(* --------------------------------------------------------------------------- *)
(* COMPLEX VALUED FUNCTIONS                                                    *)
(* --------------------------------------------------------------------------- *)

new_type_abbrev("cfun",`:A->complex`);;
new_type_abbrev("cfunB",`:B->complex`);;
new_type_abbrev("cfunC",`:C->complex`);;

(* The following definitions can be accessed by prefixing "cfun_" to their
 * names. *)
(* Remark to CPP reviewers: these definition slightly differ from their
 * presentation in the paper since we make use of general combinators
 * (fun_map2, (o), K) which allow to factorize some proofs.
 * The resulting definitions are equivalent however.
 *)
List.iter (fun (s,t) -> let s' = "cfun_" ^ s in Meta.new_definition s' (s' ^ t))
  [
    "add",  "= fun_map2 (+):cfun->cfun->cfun";
    "smul", "= ((o) o ( * )) :complex->cfun->cfun";
    "neg",  "= (o) (--) :cfun->cfun";
    "sub",  "= fun_map2 (-) :cfun->cfun->cfun";
    "zero", "= K (Cx(&0)) :cfun";
    "cnj",  "= (o) cnj :cfun->cfun";
  ];;

let CFUN_SMUL =
  REWRITE_RULE[] (ONCE_REWRITE_RULE[FUN_EQ_THM] (REWRITE_RULE[o_DEF]
    cfun_smul));;

let cfun_defs = CONJS [cfun_add;cfun_sub;CFUN_SMUL;cfun_neg;cfun_cnj;cfun_zero];;

make_overloadable "%" `:A->B->B`;;
overload_interface("%",`(%):real->real^N->real^N`);;

let prioritize_cfun () =
  overload_interface("+",`cfun_add:cfun->cfun->cfun`);
  overload_interface("%",`cfun_smul:complex->cfun->cfun`);
  overload_interface("--",`cfun_neg : cfun->cfun`);
  overload_interface("-",`cfun_sub:cfun->cfun->cfun`);;

prioritize_cfun ();;

(* Intended restriction of FUN_EQ_THM to the type :cfun *)
let CFUN_EQ = prove
  (`!f g:cfun. f = g <=> !x. f x = g x`,
  REWRITE_TAC[FUN_EQ_THM]);;

let CFUN_TO_COMPLEX = CONJS [FUN_MAP_THMS;cfun_defs;CFUN_EQ];;


(* General tactic *)

let CFUN_ARITH_TAC =
  let lemma = MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)` in
  REWRITE_TAC[CFUN_TO_COMPLEX]
  THEN (CONV_TAC COMPLEX_FIELD
    ORELSE (REWRITE_TAC[cnj] THEN SIMPLE_COMPLEX_ARITH_TAC)
    ORELSE (REPEAT STRIP_TAC THEN CONV_TAC PRENEX_CONV
      THEN MATCH_MP_TAC lemma THEN CONV_TAC COMPLEX_FIELD));;

let CFUN_ARITH t = prove(t,CFUN_ARITH_TAC);;

(* Properties *)

let store_cfun_thm,cfun_thms = property_db "CFUN";;
let CFUN_ARITH_store s = store_cfun_thm s o CFUN_ARITH;;
let cfun_prove_store s t tac = store_cfun_thm s (prove(t,tac));;


(* All the following theorems can be accessed by prefixing "CFUN_" to their
 * names *)
List.iter (uncurry CFUN_ARITH_store) [
    "SUB_THM",        `!f g x. (f - g) x = f x - g x`;
    "ADD",            `!f g. f + g = \x. f x + g x`;
    "SMUL",           `!a f. a % f = \x. a * f x`;
    "ZERO",           `!x. cfun_zero x = Cx(&0)`;
    "SMUL_THM",       `!a f x. (a % f) x = a * f x`;
    "NEG_LAMBDA",     `!f. --f = \x. --(f x)`;
    "SMUL_LNEG",      `!a f. (--a) % f = --(a % f)`;
    "SMUL_RNEG",      `!a f. a % (--f) = --(a % f)`;
    "ADD_SYM",        `!x y. x + y = y + x`;
    "ADD_ASSOC",      `!x y z. (x + y) + z = x + y + z`;
    "SUB",            `!x y. x - y = x + --y`;
    "SMUL_LZERO",     `!x. Cx(&0) % x = cfun_zero`;
    "ADD_LID",        `!x. cfun_zero + x = x`;
    "ADD_RID",        `!x. x + cfun_zero = x`;
    "SMUL_RZERO",     `!a. a % cfun_zero = cfun_zero`;
    "SMUL_SYM",       `!a b x. a % (b % x) = b % (a % x)`;
    "SUB_REFL",       `!x. x - x = cfun_zero`;
    "SMUL_DIS",       `!a x y. a % (x + y) = a % x + a % y`;
    "SMUL_ASSOC",     `!a b x. a % (b % x) = (a * b) % x`;
    "ADD_RDISTRIB",   `!a b x. (a + b) % x = a % x + b % x`;
    "SUB_RDISTRIB",   `!a b x. (a - b) % x = a % x - b % x`;
    "SUB_RADD",       `!x y z. x - (y + z) = x - y - z`;
    "ADD_RSUB",       `!x y z. x + (y - z) = (x + y) - z`;
    "ADD_LSUB",       `!x y z. (x - y) + z= (x + z) - y`;
    "SUB_RSUB",       `!x y z. x - (y - z) = x - y + z`;
    "EQ_LSUB",        `!x y z. x - y = z <=> x = z + y`;
    "EQ_RSUB",        `!x y z. x = y - z <=> x + z = y`;
    "ZERO_ADD",       `!x y. y + x = x <=> y = cfun_zero`;
    "ADD_RINV",       `!x. x + --x = cfun_zero`;
    "ADD_LINV",       `!x. --x + x = cfun_zero`;
    "NEG_0",          `--cfun_zero = cfun_zero`;
    "NEG_NEG",        `!x. --(--x) = x`;
    "NEG_SUB",        `!x y. --(x - y) = y - x`;
    "NEG_EQ_0",       `!x. --x = cfun_zero <=> x = cfun_zero`;
    "SUB_LDISTRIB",   `!a x y. a % (x - y) = a % x - a % y`;
    "ADD_LDISTRIB",   `!a x y. a % (x + y) = a % x + a % y`;
    "SMUL_DISTRIB",   `!a b f. a % (b % f) = (a * b) % f`;
    "SMUL_LID",       `!v. Cx(&1) % v = v`;
    "MINUS1_NEG",     `!v. (--Cx(&1)) % v = --v`;
    "EQ_NEG2",        `!x y. --x = --y <=> x = y`;
    "EQ_ADD_LCANCEL", `!x y z. x + y = x + z <=> y = z`;
    "EQ_ADD_RCANCEL", `!x y z. x + z = y + z <=> x = y`;
    "EQ_SUB_LCANCEL", `!x y z. x - y = x - z <=> y = z`;
    "EQ_SUB_RADD",    `!x y z. x - y = z <=> x = z + y`;
    "SUB_ADD2",       `!x y. y + x - y = x`;
    "SUB_0",          `!x y. x - y = cfun_zero <=> x = y`;
    "ENTIRE",         `!a x. a % x = cfun_zero <=> a = Cx(&0) \/ x = cfun_zero`;
    "SMUL_LCANCEL",   `!x y a. a % x = a % y <=> a = Cx(&0) \/ x = y`;
    "SMUL_RCANCEL",   `!x a b. a % x = b % x <=> a = b \/ x = cfun_zero`;
    "SUB_LZERO",      `!op. cfun_zero - op = --op`;
    "SUB_RZERO",      `!op. op - cfun_zero = op`;
    "CNJ_ADD",        `!x y. cfun_cnj (x+y) = cfun_cnj x + cfun_cnj y`;
    "CNJ_SUB",        `!x y. cfun_cnj (x-y) = cfun_cnj x - cfun_cnj y`;
    "CNJ_NEG",        `!x y. cfun_cnj (--x) = -- cfun_cnj x`;
    "CNJ_CNJ",        `!x y. cfun_cnj (cfun_cnj x) = x`;
  ];;

store_cfun_thm "ADD_ID" (CONJ CFUN_ADD_LID CFUN_ADD_RID);;

store_cfun_thm "ADD_NEUTRAL" (prove
  (`neutral (+) = cfun_zero`,
  REWRITE_TAC[neutral] THEN MESON_TAC[CFUN_ADD_ID]));;

store_cfun_thm "ADD_MONOIDAL" (prove
  (`monoidal ((+):cfun->cfun->cfun)`,
  REWRITE_TAC[monoidal;CFUN_ADD_NEUTRAL] THEN CFUN_ARITH_TAC));;

store_cfun_thm "ZERO_CLAUSES"  
  (CONJS [CFUN_SUB_REFL;CFUN_ADD_RID;CFUN_SMUL_LZERO;CFUN_SMUL_RZERO]);;

store_cfun_thm "ADD_INV" (CONJ CFUN_ADD_LINV CFUN_ADD_RINV);;

cfun_prove_store "EQ_SMUL_LCANCEL2"
  `!a x y. ~(a=Cx(&0)) ==> (a % x = y <=> x = inv a % y)`
  (REWRITE_TAC[CFUN_TO_COMPLEX] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC (MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)`)
  THEN GEN_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

(* Sub-space *)
let is_cfun_subspace = new_definition 
  `is_cfun_subspace (spc:cfun->bool) <=>
    cfun_zero IN spc
    /\ !x. x IN spc ==> (!a. a % x IN spc) /\ !y. y IN spc ==> x+y IN spc`;;

let [CFUN_SUBSPACE_ZERO;CFUN_SUBSPACE_SMUL;CFUN_SUBSPACE_ADD] =
  preprocess (EQ_RIMP is_cfun_subspace);;

let CFUN_SUBSPACE = CONJS [is_cfun_subspace;GSYM CFUN_MINUS1_NEG;CFUN_SUB];;

let CFUN_SUBSPACE_TAC = IMP_REWRITE_TAC [GSYM CFUN_MINUS1_NEG;CFUN_SUB;EQ_RIMP
  is_cfun_subspace];;

let CFUN_SUBSPACE_NEG = prove
  (`!s x. is_cfun_subspace s /\ x IN s ==> --x IN s`,
  CFUN_SUBSPACE_TAC);;

let CFUN_SUBSPACE_SUB = prove
  (`!s x y. is_cfun_subspace s /\ x IN s /\ y IN s ==> x-y IN s`,
  CFUN_SUBSPACE_TAC);;

let CFUN_SUBSPACE_SING_CFUNZERO = prove
  (`is_cfun_subspace {cfun_zero}`,
  SIMP_TAC[is_cfun_subspace;IN_SING;CFUN_SMUL_RZERO;CFUN_ADD_RID]);;

let CFUN_SUBSPACE_UNIV = prove
  (`is_cfun_subspace UNIV`,
  REWRITE_TAC[is_cfun_subspace;IN_UNIV]);;


(* ------------------------------------------------------------------------- *)
(* SUMMATION OF CFUNS                                                        *)
(* ------------------------------------------------------------------------- *)

let cfun_sum = new_definition `cfun_sum = iterate cfun_add`;;
  
let CFUN_SUM_CLAUSES =
  let th = MATCH_MP ITERATE_CLAUSES CFUN_ADD_MONOIDAL in
  REWRITE_RULE[GSYM cfun_sum;CFUN_ADD_NEUTRAL] th;;

let CFUN_SUM_CLAUSES_NUMSEG =
  let th = MATCH_MP ITERATE_CLAUSES_NUMSEG CFUN_ADD_MONOIDAL in
  REWRITE_RULE[GSYM cfun_sum;CFUN_ADD_NEUTRAL] th;;

let CFUN_SUM_EQ =
  let CFUN_ADD_MONOIDAL' = INST_TYPE [`:C`,`:A`] CFUN_ADD_MONOIDAL in
  let th = MATCH_MP ITERATE_EQ CFUN_ADD_MONOIDAL' in
  REWRITE_RULE[GSYM cfun_sum;CFUN_ADD_NEUTRAL] th;;

let CFUN_SUM_VSUM = prove
  (`!s f x. FINITE s ==> cfun_sum s f x = vsum s (\i. f i x)`,
  ONCE_REWRITE_TAC[TAUT `(A ==> B) <=> (A ==> A ==> B)`]
  THEN REPEAT GEN_TAC THEN Pa.SPEC_TAC ("s","s")
  THEN MATCH_MP_TAC FINITE_INDUCT
  THEN SIMP_TAC[CFUN_SUM_CLAUSES;VSUM_CLAUSES;CFUN_TO_COMPLEX;COMPLEX_VEC_0;
    FINITE_INSERT;fun_map2;TAUT `((A==>B)==>A==>C) <=> (A==>B==>C)`]
  THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC[]);;

let VSUM_CFUN_SUM = prove
  (`!s f x. FINITE s ==> vsum s (f x) = cfun_sum s (\i x. f x i) x`,
  SIMP_TAC[CFUN_SUM_VSUM;ETA_AX]);;


(* ------------------------------------------------------------------------- *)
(* EMBEDDING COMPLEX NUMBERS IN CFUNS                                        *)
(* ------------------------------------------------------------------------- *)

let SING_IND,SING_REC = define_type "singleton = SING_ELT";;

let SING_EQ = prove
  (`!x. x = SING_ELT`,
  MATCH_MP_TAC SING_IND THEN REFL_TAC);;

let cfun_of_complex = new_definition
  `cfun_of_complex = K :complex->singleton->complex`;;

List.iter (fun (s,t) -> Meta.prove ~prefix:"CFUN_OF_COMPLEX_" s t
  "REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC")
  [
    "ADD", "!x y. cfun_of_complex (x+y) = cfun_of_complex x+cfun_of_complex y";
    "SUB", "!x y. cfun_of_complex (x-y) = cfun_of_complex x-cfun_of_complex y";
    "NEG", "!x. cfun_of_complex (--x) = --cfun_of_complex x";
    "SMUL","!a x. cfun_of_complex (a*x) = a%cfun_of_complex x";
    "CNJ", "!x. cfun_of_complex (cnj x) = cfun_cnj (cfun_of_complex x)";
    "ZERO","cfun_of_complex (Cx(&0)) = cfun_zero";
  ];;

let complex_of_cfun = new_definition
  `complex_of_cfun f :complex = f SING_ELT`;;

List.iter (fun (s,t) -> Meta.prove ~prefix:"COMPLEX_OF_CFUN_" s t
  "REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC")
  [
    "ADD", "!x y. complex_of_cfun (x+y) = complex_of_cfun x+complex_of_cfun y";
    "SUB", "!x y. complex_of_cfun (x-y) = complex_of_cfun x-complex_of_cfun y";
    "NEG", "!x. complex_of_cfun (--x) = --complex_of_cfun x";
    "SMUL","!a x. complex_of_cfun (a%x) = a*complex_of_cfun x";
  ];;

let COMPLEX_OF_CFUN_OF_COMPLEX = prove
  (`complex_of_cfun o cfun_of_complex = I`,
  REWRITE_TAC[complex_of_cfun;cfun_of_complex;o_DEF;K_THM;I_DEF]);;

let CFUN_OF_COMPLEX_OF_CFUN = prove
  (`cfun_of_complex o complex_of_cfun = I`,
  REWRITE_TAC[complex_of_cfun;cfun_of_complex;o_DEF;K_DEF;FUN_EQ_THM;I_THM;
    GSYM SING_EQ]);;


(* ------------------------------------------------------------------------- *)
(* INNER PRODUCT                                                             *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("inprod",`:cfun->cfun->complex`);;

new_type_abbrev("inner_space",`:(cfun->bool)#inprod`);;

let is_inner_space = new_definition
  `is_inner_space ((s,inprod):inner_space) <=>
    is_cfun_subspace s /\
    !x. x IN s ==>
      real (inprod x x) /\ &0 <= real_of_complex (inprod x x)
      /\ (inprod x x = Cx(&0) <=> x = cfun_zero)
      /\ !y. y IN s ==>
        cnj (inprod y x) = inprod x y /\
        (!a. inprod x (a%y) = a * (inprod x y))
        /\ !z. z IN s ==> inprod (x+y) z = inprod x z + inprod y z`;;


(* EVERY THEOREM proved using "inner_space_prove" implicitly has the assumption
 * "!s inprod. is_inner_space (s,inprod) ==>"
 *)
let inner_space_parse s =
  parse_term ("!s inprod. is_inner_space (s,inprod) ==> " ^ s);;
let inner_space_prove (s,p) = prove(gimp_imp (inner_space_parse s),p);;
let inner_space_g s = g (gimp_imp (inner_space_parse s));;

let full_inner_space_parse s = parse_term ("!is. is_inner_space is ==> " ^ s);;
let full_inner_space_prove (s,p) =
  prove(gimp_imp (full_inner_space_parse s),p);;
let full_inner_space_g s = g (gimp_imp (full_inner_space_parse s));;


(* Properties *)

let store_inner_space_thm,inner_space_thms = property_db "INSPACE";;
let inner_space_prove_store s t tac =
  store_inner_space_thm s (inner_space_prove(t,tac));;

let FORALL_INSPACE_THM = prove
  (`!P. (!is:inner_space. P is) <=> !s inprod. P (s,inprod)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let _ =
  List.iter (uncurry store_inner_space_thm) (zip
    ["IS_SUBSPACE";"SELF_REAL";"SELF_POS";"ZERO_EQ";"CNJ";"RSMUL";"ADD_RDIST"]
    (preprocess (EQ_RIMP is_inner_space)));;

add_real_thm INSPACE_SELF_REAL;;

inner_space_prove_store "ZERO"
  "inprod cfun_zero cfun_zero = Cx(&0)"
  (SIMP_TAC[is_inner_space;is_cfun_subspace]);;

inner_space_prove_store "LSMUL"
  "!x y a. x IN s /\ y IN s ==> inprod (a%x) y = cnj a * inprod x y"
  (TARGET_REWRITE_TAC[GSYM INSPACE_CNJ;GSYM CNJ_MUL] CNJ_INJ
  THEN IMP_REWRITE_TAC[INSPACE_RSMUL;CFUN_SUBSPACE_SMUL;INSPACE_IS_SUBSPACE]);;

inner_space_prove_store "LNEG"
  "!x y. x IN s /\ y IN s ==> inprod (--x) y = --inprod x y"
  (IMP_REWRITE_TAC[GSYM CFUN_MINUS1_NEG;INSPACE_LSMUL;CNJ_NEG;CNJ_CX;
    GSYM COMPLEX_NEG_MINUS1]);;

inner_space_prove_store "SUB_RDIST"
  "!x y z. x IN s /\ y IN s /\ z IN s ==>
      inprod (x-y) z = inprod x z - inprod y z"
  (IMP_REWRITE_TAC[CFUN_SUB;complex_sub;INSPACE_ADD_RDIST;INSPACE_LNEG;
    CFUN_SUBSPACE_NEG;INSPACE_IS_SUBSPACE]);;

inner_space_prove_store "RNEG"
  "!x y. x IN s /\ y IN s ==> inprod x (--y) = --inprod x y"
  (IMP_REWRITE_TAC[GSYM CFUN_MINUS1_NEG;INSPACE_RSMUL;GSYM COMPLEX_NEG_MINUS1]);;

inner_space_prove_store "ADD_LDIST"
  "!x y z. x IN s /\ y IN s /\ z IN s ==>
      inprod z (x+y) = inprod z x + inprod z y"
  (TARGET_REWRITE_TAC[GSYM INSPACE_CNJ] (GSYM CNJ_ADD)
  THEN TARGET_REWRITE_TAC[GSYM INSPACE_CNJ] INSPACE_ADD_RDIST
  THEN IMP_REWRITE_TAC[INSPACE_IS_SUBSPACE;CFUN_SUBSPACE_ADD]);;

inner_space_prove_store "SUB_LDIST"
  "!x y z. x IN s /\ y IN s /\ z IN s ==>
    inprod z (x-y) = inprod z x - inprod z y"
  (IMP_REWRITE_TAC[CFUN_SUB;complex_sub;INSPACE_ADD_LDIST;INSPACE_RNEG;
    CFUN_SUBSPACE_NEG;INSPACE_IS_SUBSPACE]);;

inner_space_prove_store "RZERO"
  "!x. x IN s ==> inprod x cfun_zero = Cx(&0)"
  (IMP_REWRITE_TAC[GSYM CFUN_SMUL_LZERO;INSPACE_RSMUL;COMPLEX_MUL_LZERO]);;

inner_space_prove_store "LZERO"
  "!x. x IN s ==> inprod cfun_zero x = Cx(&0)"
  (IMP_REWRITE_TAC[GSYM CFUN_SMUL_LZERO;INSPACE_LSMUL;CNJ_CX;COMPLEX_MUL_LZERO]);;

inner_space_prove_store "SELF_CNJ"
  "!x. x IN s ==> cnj (inprod x x) = inprod x x"
  (SIMP_TAC[GSYM REAL_CNJ;is_inner_space]);;

inner_space_prove_store "SELF_NORM"
  "!x. x IN s ==> norm (inprod x x) = real_of_complex (inprod x x)"
  (TARGET_REWRITE_TAC[GSYM REAL_OF_COMPLEX] COMPLEX_NORM_CX
  THEN IMP_REWRITE_TAC[REAL_ABS_REFL;EQ_RIMP is_inner_space]);;

inner_space_prove_store "SELF_RE"
  "!x. x IN s ==> real_of_complex (inprod x x) = Re (inprod x x)"
  (IMP_REWRITE_TAC[REAL_OF_COMPLEX_RE;EQ_RIMP is_inner_space]);;

inner_space_prove_store "NORM_SYM"
  "!x y. x IN s /\ y IN s ==> norm (inprod x y) = norm (inprod y x)"
  (TARGET_REWRITE_TAC[GSYM INSPACE_CNJ] COMPLEX_NORM_CNJ);;

(* Surjection holds in finite dimension only *)
inner_space_prove_store "INJ"
  "!x y. x IN s /\ y IN s ==> (inprod x = inprod y <=> x = y)"
  (TARGET_REWRITE_TAC[GSYM CFUN_SUB_0] (GSYM INSPACE_ZERO_EQ)
  THEN IMP_REWRITE_TAC [INSPACE_SUB_RDIST;COMPLEX_SUB_0;CFUN_SUBSPACE_SUB;
    INSPACE_IS_SUBSPACE]);;

inner_space_prove_store "INJ_ALT"
  "!x y. x IN s /\ y IN s
    ==> ((!z. z IN s ==> inprod x z = inprod y z) <=> x = y)"
  (TARGET_REWRITE_TAC[GSYM CFUN_SUB_0] (GSYM INSPACE_ZERO_EQ)
  THEN IMP_REWRITE_TAC [INSPACE_SUB_RDIST;COMPLEX_SUB_0;CFUN_SUBSPACE_SUB;
    INSPACE_IS_SUBSPACE]);;

(* TODO RIESZ *)


(* ------------------------------------------------------------------------- *)
(* ORTHOGONALITY                                                             *)
(* ------------------------------------------------------------------------- *)

let are_orthogonal = new_definition
  `are_orthogonal ((s,inprod):inner_space) u v <=>
    is_inner_space (s,inprod) /\ u IN s /\ v IN s ==> inprod u v = Cx(&0)`;;

let store_orthogonal_thm,orthogonal_thms = property_db "ARE_ORTHOGONAL";;

let orthogonal_prove_store s t tac =
  store_orthogonal_thm s (inner_space_prove(t,tac));;

orthogonal_prove_store "ALT"
  "!u v. u IN s /\ v IN s ==>
      (are_orthogonal (s,inprod) u v <=> inprod u v = Cx(&0))"
  (IMP_REWRITE_TAC[are_orthogonal]);;

orthogonal_prove_store "SYM"
  "!u v. u IN s /\ v IN s
      ==> (are_orthogonal (s,inprod) u v <=> are_orthogonal (s,inprod) v u)"
  (IMP_REWRITE_TAC[ARE_ORTHOGONAL_ALT]
  THEN REPEAT (TARGET_REWRITE_TAC [GSYM INSPACE_CNJ] CNJ_EQ_CX));;

orthogonal_prove_store "LSCALAR"
  "!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v
      ==> !a. are_orthogonal (s,inprod) (a % u) v"
  (IMP_REWRITE_TAC[are_orthogonal;INSPACE_LSMUL;COMPLEX_MUL_RZERO]);;

orthogonal_prove_store "LZERO"
  "!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v
      ==> !a. are_orthogonal (s,inprod) cfun_zero v"
  (IMP_REWRITE_TAC[are_orthogonal;INSPACE_LZERO]);;

orthogonal_prove_store "RZERO"
  "!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v
      ==> !a. are_orthogonal (s,inprod) v cfun_zero"
  (IMP_REWRITE_TAC[are_orthogonal;INSPACE_RZERO]);;

orthogonal_prove_store "INSPACE_SELF_ADD"
  "!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v ==>
    inprod (u+v) (u+v) = inprod u u + inprod v v"
  (IMP_REWRITE_TAC[are_orthogonal;INSPACE_ADD_LDIST;INSPACE_ADD_RDIST;
    CFUN_SUBSPACE_ADD;INSPACE_IS_SUBSPACE]
  THEN TARGET_REWRITE_TAC[GSYM INSPACE_CNJ] CNJ_EQ_CX
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

orthogonal_prove_store "DECOMPOSITION"
  "!u v. u IN s /\ v IN s ==>
      let proj_v = inprod v u / inprod v v in
      let orthogonal_component = u - proj_v % v in
      u = proj_v % v + orthogonal_component
      /\ are_orthogonal (s,inprod) v orthogonal_component"
  (IMP_REWRITE_TAC[LET_DEFS;CFUN_SUB_ADD2;are_orthogonal;
    INSPACE_SUB_LDIST;INSPACE_RSMUL;EQ_RIMP is_cfun_subspace;
    INSPACE_IS_SUBSPACE]
  THEN CASE_REWRITE_TAC COMPLEX_DIV_RMUL
  THEN IMP_REWRITE_TAC[INSPACE_ZERO_EQ;INSPACE_LZERO]
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

inner_space_prove_store "SCHWARZ_INEQUALITY"
  "!x y. x IN s /\ y IN s
      ==> norm (inprod x y) pow 2
        <= real_of_complex (inprod x x) * real_of_complex (inprod y y)"
  (IMP_REWRITE_TAC[GSYM REAL_OF_COMPLEX_MUL;INSPACE_SELF_REAL]
  THEN TARGET_REWRITE_TAC[REWRITE_RULE[LET_DEFS] ARE_ORTHOGONAL_DECOMPOSITION]
    ARE_ORTHOGONAL_INSPACE_SELF_ADD
  THEN SEQ_IMP_REWRITE_TAC[REWRITE_RULE[LET_DEFS] ARE_ORTHOGONAL_DECOMPOSITION;
    ARE_ORTHOGONAL_LSCALAR;CFUN_SUBSPACE_SUB;INSPACE_RSMUL;CFUN_SUBSPACE_SMUL;
    INSPACE_IS_SUBSPACE;INSPACE_LSMUL;COMPLEX_ADD_LDISTRIB]
  THEN REWRITE_TAC[complex_div;CNJ_MUL;CNJ_INV;COMPLEX_MUL_CNJ;GSYM CX_POW;
    Pa.COMPLEX_FIELD "x*(y*inv x)*(z*inv t)*x = (y*z)*((x*x)*inv(x*t))";
    GSYM CX_INV]
  THEN IMP_REWRITE_TAC[REAL_OF_COMPLEX_ADD;REAL_CX;REAL_OF_COMPLEX_MUL;
    REAL_OF_COMPLEX_CX;REAL_MUL;INSPACE_SELF_REAL;CFUN_SUBSPACE_SUB;
    CFUN_SUBSPACE_SMUL;INSPACE_IS_SUBSPACE;GSYM INSPACE_SELF_NORM;
    GSYM REAL_POW_2;REAL_ARITH `x = y /\ &0 <= z ==> x <= y + z`;REAL_LE_MUL;
    NORM_POS_LE]
  THEN CASE_REWRITE_TAC REAL_MUL_RINV
  THEN IMP_REWRITE_TAC[REAL_MUL_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;
    REAL_POW_EQ_0;COMPLEX_NORM_ZERO;INSPACE_ZERO_EQ;INSPACE_LZERO]);;

inner_space_prove_store "SCHWARZ_INEQUALITY_ENHANCED"
  "!x y. x IN s /\ y IN s ==>
      real_of_complex ((inprod x y - inprod y x) / (Cx(&2) * ii)) pow 2
        <= real_of_complex (inprod x x) * real_of_complex (inprod y y)"
  (IMP_REWRITE_TAC [MATCH_MP (MESON[REAL_LE_TRANS]
    `!f g. (P ==> f x y <= g x y) ==> P /\ z <= f x y ==> z <= g x y`)
    (SPEC_ALL INSPACE_SCHWARZ_INEQUALITY);
    MATCH_MP (REAL_ARITH `x=y+z ==> &0<=y /\ t=z ==> t<=x`) COMPLEX_SQNORM;
    REAL_LE_POW_2;MESON[] `(x:real) = y ==> x pow 2 = y pow 2`]
  THEN TARGET_REWRITE_TAC[GSYM CX_INJ] CX_IM_CNJ
  THEN REWRITE_TAC[GSYM COMPLEX_INV_II;complex_div;COMPLEX_INV_MUL]
  THEN IMP_REWRITE_TAC [INSPACE_CNJ;REAL_OF_COMPLEX;SIMPLE_COMPLEX_ARITH
    `x*y*inv ii=inv ii*(x*y)`;COMPLEX_INV_II;GSYM complex_div]
  THEN TARGET_REWRITE_TAC[GSYM INSPACE_CNJ] (GSYM CX_IM_CNJ)
  THEN REWRITE_TAC[REAL_CX]);;


(* ------------------------------------------------------------------------- *)
(* OPERATORS                                                                 *)
(* ------------------------------------------------------------------------- *)

(* "cop" stands for "Complex-valued function OPerator" *)
new_type_abbrev ("cop",`:cfunB->cfun`);;
new_type_abbrev ("copB",`:cfunC->cfunB`);;

List.iter (fun (s,t) -> let s' = "cop_" ^ s in Meta.new_definition s' (s' ^ t))
  [
    "add",  "= fun_map2 (+):cop->cop->cop";
    "sub",  "= fun_map2 (-):cop->cop->cop";
    "neg",  "= (o) (--):cop->cop";
    "mul",  "= (o):cop->copB->(cfunC->cfun)";
    "smul", "= ((o) o (%)):complex->cop->cop";
    "zero", "= (K cfun_zero):cop";
  ];;

let cop_pow = define
  `cop_pow (op:cfun->cfun) 0 = I /\
  cop_pow op (SUC n) = cop_mul op (cop_pow op n)`;;

let COP_SMUL =
  REWRITE_RULE[] (ONCE_REWRITE_RULE[FUN_EQ_THM] (REWRITE_RULE[o_DEF]
    cop_smul));;

let cop_defs = CONJS
  [cop_add;cop_sub;cop_neg;cop_mul;COP_SMUL;cop_zero;I_THM;cop_pow];;

let prioritize_cop () =
  overload_interface("+",`cop_add:cop->cop->cop`);
  overload_interface("-",`cop_sub:cop->cop->cop`);
  overload_interface("--",`cop_neg:cop->cop`);
  overload_interface("**",`cop_mul:cop->copB->(cfunC->cfun)`);
  overload_interface("pow",`cop_pow:(cfun->cfun)->num->(cfun->cfun)`);
  overload_interface("%",`cop_smul:complex->cop->cop`);;

prioritize_cop ();;

(* Intended restriction of FUN_EQ_THM to the type :cop *)
let COP_EQ = prove
  (`!f g:cop. f = g <=> (!x. f x = g x)`,
  REWRITE_TAC[FUN_EQ_THM]);;

let COP_TO_CFUN = CONJS [FUN_MAP_THMS;o_THM;cop_defs;COP_EQ];;

let COP_POW_CONV =
  let th = REWRITE_CONV[cop_pow;cop_mul;I_O_ID] `cop_pow t (SUC 0)` in
  fun t ->
    let (h,_) = strip_comb t in
    if name_of h = "cop_pow"
    then (CHANGED_CONV (RAND_CONV (REDEPTH_CONV num_CONV)
      THENC REWRITE_CONV[cop_pow;th])) t
    else failwith "COP_POW_CONV";;

let COP_ARITH_TAC =
  let lemma = MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)` in
  CONV_TAC (TOP_DEPTH_CONV COP_POW_CONV)
  THEN REWRITE_TAC[COP_TO_CFUN]
  THEN (CFUN_ARITH_TAC
    ORELSE (REPEAT STRIP_TAC THEN CONV_TAC PRENEX_CONV
      THEN MATCH_MP_TAC lemma THEN CFUN_ARITH_TAC));;

let COP_ARITH t = prove(t,COP_ARITH_TAC);;

(* Properties *)

let store_cop_thm,cop_thms = property_db "COP";;
let cop_prove_store s t tac = store_cop_thm s (prove(t,tac));;
let COP_ARITH_store s = store_cop_thm s o COP_ARITH;;

List.iter (uncurry COP_ARITH_store)
  [
    "SMUL",             `!a op. a % op = \x. a * op x`;
    "SMUL_THM",         `!a op x. (a % op) x = a % op x`;
    "SMUL_ALT",         `!a op. a % op = \x. a * op x`;
    "MUL",              `!op1 op2. op1 ** op2 = \x. op1 (op2 x)`;
    "ADD",              `!op1 op2. op1 + op2 = \x. op1 x + op2 x`;
    "NEG",              `!op. --op = \x. --op x`;
    "SUB_THM",          `!op1 op2 x. (op1 - op2) x = op1 x - op2 x`;
    "ZERO_THM",         `!x. cop_zero x = cfun_zero`;
    "MUL_LID",          `!op. I ** op = op`;
    "MUL_RID",          `!op. op ** I = op`;
    "MUL_I_SYM",        `!op. op ** I = I ** op`;
    "SMUL",             `!a op. a % op = \x. a % op x`;
    "MUL_THM",          `!x op1 op2. (op1 ** op2) x = op1 (op2 x)`;
    "SMUL_LNEG",        `!a op. --a % op = --(a % op)`;
    "SMUL_RNEG",        `!a op. a % --op = --(a % op)`;
    "SUB",              `!op1 op2. op1 - op2 = op1 + --op2`;
    "NEG_NEG",          `!op. --(--op) = op`;
    "NEG_ADD",          `!op1 op2. --(op1 + op2) = --op1 + --op2`;
    "NEG_SUB",          `!op1 op2. --(op1 - op2) = --op1 + op2`;
    "SMUL_ASSOC",       `!a b op. a % (b % op) = (a * b) % op`;
    "SMUL_SYM",         `!a b op. a % (b % op) = b % (a % op)`;
    "MUL_LSMUL",        `!op1 op2. a % op1 ** op2 = a % (op1 ** op2)`;
    "ADD_SYM",          `!op1 op2. op1 + op2 = op2 + op1 `;
    "ADD_ASSOC",        `!op1 op2 op3. (op1 + op2) + op3 = op1 + op2 + op3`;
    "ADD_LDISTRIB",     `!a op1 op2. a % (op1 + op2) = a % op1 + a % op2`;
    "ADD_RDISTRIB",     `!a b op. (a + b) % op = a % op + b % op`;
    "SMUL_INV_ID",      `!a op. ~(a = Cx (&0)) ==> a % (inv a % op) = op`;
    "SUB_LDISTRIB",     `!a x y. a % (x - y) = a % x - a % y`;
    "SUB_RADD",         `!x y z. x - (y + z) = x - y - z`;
    "ADD_RSUB",         `!x y z. x + (y - z) = (x + y) - z`;
    "SUB_SUB",          `!x y z. x - (y - z) = x - y + z`;
    "ADD_RID",          `!x. x + cop_zero = x`;
    "ADD_LID",          `!x. cop_zero + x = x`;
    "ADD_SYM",          `!op1 op2. op1 + op2 = op2 + op1`;
    "ADD_AC",           `!m n p. m + n = n + m /\ (m + n) + p = m + n + p
                               /\ m + n + p = n + m + p`;
    "MUL_ASSOC",        `!x y z . (x ** y) ** z = x ** y ** z`;
    "SUB_REFL",         `!x. x - x = cop_zero`;
    "SUB_ADD",          `!x y z. (x-y)+z= (x+z)-y`;
    "NEG_INJ",          `!x y. --x = --y <=> x = y`;
    "EQ_ADD_LCANCEL",   `!x y z. x + y = x + z <=> y=z`;
    "EQ_ADD_RCANCEL",   `!x y z. x + z = y + z <=> x=y`;
    "EQ_SUB_LCANCEL",   `!x y z. x - y = x - z <=> y=z`;
    "EQ_LSUB",          `!x y z. x - y = z <=> x = z + y`;
    "EQ_RSUB",          `!x y z. x = y - z <=> x + z = y`;
    "MUL_LZERO",        `!op. cop_zero ** op = cop_zero`;
    "SUB_REFL",         `!op. op - op = cop_zero`;
    "SMUL_LID_NEG",     `!x. (--Cx(&1)) % x = --x`;
    "ADD_RID",          `!op. op + cop_zero = op`;
    "ADD_LID",          `!op. cop_zero + op = op`;
    "SMUL_LID",         `!op. Cx(&1) % op = op`;
    "SMUL_RZERO",       `!op. a % cop_zero = cop_zero`;
    "SUB_LZERO",        `!op. cop_zero - op = --op`;
    "SMUL_LZERO",       `!x. Cx(&0) % x = cop_zero`;
    "ADD_MUL_RDISTRIB", `!op1 op2 op3.
                              (op1 + op2) ** op3 = op1 ** op3 + op2 ** op3`;
    "SUB_MUL_RDISTRIB", `!op1 op2 op3.
                              (op1 - op2) ** op3 = op1 ** op3 - op2 ** op3`;
    "EQ_LSUB_LSUB",     `!x y z. x - y = z <=> x - z = y`;
    "EQ_LSMUL",         `!a x y. a % x = a % y <=> x = y \/ a = Cx(&0)`;
    "POW_2",            `!op. op pow 2 = op ** op`;
    "ADD_2",            `!op. Cx(&2) % op  = op + op`;
    "ENTIRE",           `!a x. a%x = cop_zero <=> a = Cx(&0) \/ x = cop_zero`;
  ];;

(* FIXME Improve COP_ARITH so that it can deal with that 
 * + change the name because it does not represent the same theorem as its cfun
 * counterpart *)
cop_prove_store "EQ_MUL_LCANCEL2"
  `!x y z t:cop. ~(x=Cx(&0)) ==> (x % y = z % t <=> y = (z / x) % t)`
  (REWRITE_TAC[COP_TO_CFUN;CFUN_TO_COMPLEX] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC (MESON[]
    `(!x y. P x y <=> Q x y) ==> (!x y. P x y) = !x y. Q x y`)
  THEN REPEAT GEN_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

store_cop_thm "ZERO_CLAUSES" 
  (CONJS [COP_MUL_LZERO;COP_SUB_REFL;COP_ADD_RID;COP_ADD_LID;COP_SMUL_RZERO]);;

store_cop_thm "I_ID" (CONJ COP_MUL_LID COP_MUL_RID);;

cop_prove_store "ZERO_NEQ_ID"
  `~(I = cop_zero)`
  (REWRITE_TAC[COP_TO_CFUN;CFUN_TO_COMPLEX;NOT_FORALL_THM]
  THEN Pa.EXISTS_TAC "\x. Cx(&1)" THEN CONV_TAC COMPLEX_FIELD);;

cop_prove_store "SMUL_I_ZERO"
  `!a. a % I = cop_zero <=> a = Cx(&0)`
  (REWRITE_TAC[COP_ENTIRE;COP_ZERO_NEQ_ID]);;

cop_prove_store "SMUL_I_ONE"
  `!a. a % I = I <=> a = Cx(&1)`
  (REWRITE_TAC[COP_TO_CFUN;CFUN_TO_COMPLEX] THEN GEN_TAC THEN EQ_TAC
  THENL [DISCH_THEN (MP_TAC o Pa.SPEC "\x.Cx(&1)"); ALL_TAC]
  THEN CONV_TAC COMPLEX_FIELD);;

store_cop_thm "NEG_CLAUSES" 
  (CONJS [COP_NEG_NEG;COP_NEG_ADD;COP_NEG_SUB;COP_SUB]);;


(* ------------------------------------------------------------------------- *)
(* LINEAR OPERATORS                                                          *)
(* ------------------------------------------------------------------------- *)

let is_linear_cop = new_definition
  `is_linear_cop (op:cop) <=>
    !x y. op (x + y) = op x + op y /\ !a. op (a % x) = a % (op x)`;;

let store_linear_thm,linear_thms = property_db "LINCOP";;
let linear_prove_store s t tac = store_linear_thm s (prove(t,tac));;

let _ =
  let ths = zip ["ADD";"SMUL"] (preprocess (EQ_RIMP is_linear_cop)) in
  List.iter (uncurry store_linear_thm) ths;;

let _ = List.iter (fun (s,th) ->
  let tac =
    SIMP_TAC[is_linear_cop;CFUN_SUB;GSYM CFUN_MINUS1_NEG;COP_TO_CFUN;
      GSYM CFUN_SMUL_LZERO] in
  store_linear_thm s (prove(th,tac)))
  [
    "SUB", `!x y op. is_linear_cop op ==> op (x - y) = op x - op y`;
    "NEG", `!x op. is_linear_cop op ==> op (--x) = --(op x)`;
    "MUL_RSMUL", `!a op1 op2. is_linear_cop op2 ==> op2 ** (a % op1) = a % (op2 ** op1)`;
    "ADD_MUL_LDISTRIB", `!op1 op2 op3. is_linear_cop op3 ==>
      op3 ** (op1 + op2) = op3 ** op1 + op3 ** op2`;
    "SUB_MUL_LDISTRIB", `!op1 op2 op3. is_linear_cop op3 ==>
      op3 ** (op1 - op2) = op3 ** op1 - op3 ** op2`;
  ];;

store_linear_thm "SMUL_CLAUSES"
  (CONJS [LINCOP_MUL_RSMUL;COP_ADD_LDISTRIB;COP_SUB_LDISTRIB;COP_MUL_LSMUL;
    COP_MUL_ASSOC;COP_MUL_LID]);;

store_linear_thm "MUL_DISTRIB_CLAUSES"
  (CONJS[COP_ADD_MUL_RDISTRIB;COP_SUB_MUL_RDISTRIB;LINCOP_ADD_MUL_LDISTRIB;
    LINCOP_SUB_MUL_LDISTRIB]);;

store_linear_thm "CFUN_ZERO" (prove
  (`!op. is_linear_cop op ==> op cfun_zero = cfun_zero`,
  MESON_TAC[is_linear_cop;GSYM CFUN_SMUL_LZERO]));;

store_linear_thm "INJECTIVE" (prove
  (`!op. is_linear_cop op ==> 
    ((!x y. op x = op y ==> x=y) <=> !x. op x = cfun_zero ==> x = cfun_zero)`,
  TARGET_REWRITE_TAC[GSYM CFUN_SUB_0] (GSYM LINCOP_SUB)
  THEN MESON_TAC[LINCOP_CFUN_ZERO;CFUN_SUB_0]));;

store_linear_thm "POW_SMUL" (prove
  (`!op. is_linear_cop op ==> !n a. (a % op) pow n = (a pow n) % (op pow n)`,
  REWRITE_TAC[is_linear_cop] THEN REPEAT (INDUCT_TAC ORELSE STRIP_TAC)
  THEN ASM_REWRITE_TAC[COP_TO_CFUN;complex_pow] THEN CFUN_ARITH_TAC));;

store_linear_thm "POW_SMUL2" (prove
  (`!op n a. is_linear_cop op ==>  (a % op) pow n = (a pow n) % (op pow n)`,
  SIMP_TAC[LINCOP_POW_SMUL]));;

(* Congruence properties *)

List.iter (fun (s,t) ->
  let tac =
    SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
    THEN COP_ARITH_TAC
  in
  store_linear_thm ("COMPOSE_" ^ s) (prove (t,tac)))
  [
    "ADD", `!op1 op2.
        is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 + op2)`;
    "SUB", `!op1 op2.
        is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 - op2)`;
    "SMUL", `!a op. is_linear_cop op ==> is_linear_cop (a % op)`;
    "NEG", `!op. is_linear_cop op ==> is_linear_cop (--op)`;
    "MUL", `!op1 op2.
        is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 ** op2)`;
  ];;

store_linear_thm "ARITH_CLAUSES" 
  (CONJS [LINCOP_COMPOSE_ADD;LINCOP_COMPOSE_SUB;LINCOP_COMPOSE_SMUL;
    LINCOP_COMPOSE_MUL]);;

let lincompose_thms,add_lincompose_thm,add_lincompose_thms = updatable_thms();;

add_lincompose_thms [LINCOP_COMPOSE_ADD;LINCOP_COMPOSE_SUB;LINCOP_COMPOSE_SMUL;
  LINCOP_COMPOSE_MUL];;

store_linear_thm "I" (prove
  (`is_linear_cop I`,
  REWRITE_TAC[is_linear_cop;I_DEF]));;

add_lincompose_thms [LINCOP_I;REWRITE_RULE[I_DEF] LINCOP_I];;

store_linear_thm "ZERO" (prove
  (`is_linear_cop cop_zero`, 
  REWRITE_TAC[is_linear_cop;COP_ZERO_THM] THEN CFUN_ARITH_TAC));;

add_lincompose_thms [LINCOP_ZERO];;

store_linear_thm "SCALAR" (prove
  (`!a. is_linear_cop \x. a % x`, 
  REWRITE_TAC[is_linear_cop] THEN CFUN_ARITH_TAC));;
  
store_linear_thm "COP_NEG" (prove
  (`is_linear_cop (--)`,
  REWRITE_TAC[is_linear_cop] THEN CFUN_ARITH_TAC));;

store_linear_thm "SUM" (prove
  (`!f g s. is_linear_cop f /\ FINITE s 
    ==> f (cfun_sum s g) = cfun_sum s (f o g)`,
  REWRITE_TAC[TAUT `(A /\ B ==> C) <=> (B ==> B ==> A ==> C)`] 
  THEN REPEAT (MATCH_MP_TAC FINITE_INDUCT ORELSE GEN_TAC)
  THEN IMP_REWRITE_TAC[CFUN_SUM_CLAUSES;LINCOP_CFUN_ZERO;FINITE_INSERT]
  THEN SIMP_TAC[COND_ELIM_THM;LINCOP_ADD;o_THM]));;

let LINEARITY_TAC g = IMP_REWRITE_TAC (lincompose_thms ()) g;;


(* ------------------------------------------------------------------------- *)
(* DUAL SPACE                                                                *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("cfun_dual",`:cfun->complex`);;
new_type_abbrev("cfun_dualB",`:cfunB->complex`);;

(* Note that all the above operations still apply on the dual space since
 * `:cfun_dual` is an instance of `cfun` itself.
 *)

let cfun_dual = new_definition
  `cfun_dual (spc:cfun->bool) =
    { f:cfun_dual | is_linear_cop (cfun_of_complex o f) }`;;

(*
 *let cfun_topological_dual = new_definition
 *  `cfun_topological_dual spc =
 *    { f | f IN cfun_dual spc /\ !x. f continuous (within (:cfun)) }`;;
 *)

let cop_transpose = new_definition
  `cop_transpose (f:cop) :cfun_dual->cfun_dualB = \phi. phi o f`;;


(* ------------------------------------------------------------------------- *)
(* FREQUENTLY USED OPERATORS                                                 *)
(* ------------------------------------------------------------------------- *)

let commutator = new_definition
  `commutator (op1:cfun->cfun) op2 = op1 ** op2 - op2 ** op1`;;

let COMMUTATOR_NEG = prove
  (`!op1 op2. commutator op1 op2 = -- commutator op2 op1`,
  REWRITE_TAC[commutator] THEN COP_ARITH_TAC);;

let COMMUTATOR_ZERO_SYM = prove
  (`!op1 op2. commutator op1 op2 = cop_zero <=> commutator op2 op1 = cop_zero`, 
  REWRITE_TAC[commutator;COP_EQ_LSUB;COP_ADD_LID] THEN MESON_TAC[]);;

let LINCOP_COMMUTATOR = prove
  (`!op1 op2. is_linear_cop op1 /\ is_linear_cop op2
    ==> is_linear_cop (commutator op1 op2)`,
  REWRITE_TAC[commutator] THEN LINEARITY_TAC);;

add_lincompose_thm LINCOP_COMMUTATOR;;

let expectation = new_definition
  `expectation (inprod:inprod) f op = inprod f (op f)`;;  

let deviation = new_definition
  `deviation (inprod:inprod) f op = op - (\x. expectation inprod f op % x)`;;

let DEVIATION_ALT = prove
  (`!inprod f op. deviation inprod f op = op - expectation inprod f op % I`,
  REWRITE_TAC[deviation] THEN COP_ARITH_TAC);;

let LINCOP_DEVIATION = prove
  (`!inprod state op. is_linear_cop op
    ==> is_linear_cop (deviation inprod state op)`,
  REWRITE_TAC[deviation;GSYM COP_SMUL] THEN LINEARITY_TAC);;

add_lincompose_thm LINCOP_DEVIATION;;

let variance = new_definition
  `variance  (inprod:inprod) f op = 
    expectation inprod f (deviation inprod f op ** deviation inprod f op)`;;  

let DEVIATION_COMMUTATOR = prove
  (`!inprod op1 op2 state. is_linear_cop op1 /\ is_linear_cop op2
    ==> commutator (deviation inprod state op1) (deviation inprod state op2)
      = commutator op1 op2`,
  IMP_REWRITE_TAC [DEVIATION_ALT;commutator;LINCOP_SUB_MUL_LDISTRIB]
  THEN LINEARITY_TAC
  THEN SIMP_TAC[LINCOP_MUL_DISTRIB_CLAUSES;COP_MUL_LSMUL;COP_I_ID;
    LINCOP_MUL_RSMUL;MESON[COP_SMUL_SYM]
      `f (a % (b % op)) (b % (a % op)) = f (a % (b % op)) (a % (b % op))`]
  THEN COP_ARITH_TAC);;

let EXPEC_ZERO_STATE = prove
  (`!s inprod op. is_linear_cop op /\ is_inner_space (s,inprod)
    ==> expectation inprod cfun_zero op = Cx(&0)`,
  IMP_REWRITE_TAC[expectation;INSPACE_LZERO;LINCOP_CFUN_ZERO;
    CFUN_SUBSPACE_ZERO;INSPACE_IS_SUBSPACE]);;


(* ------------------------------------------------------------------------- *)
(* CLOSURE                                                                   *)
(* ------------------------------------------------------------------------- *)

let is_closed_by = new_definition
  `is_closed_by s f <=> !x. x IN s ==> f x IN s`;;

let IS_CLOSED_BY_COMPOSE = prove
  (`!s f g. is_closed_by s f /\ is_closed_by s g ==> is_closed_by s (f o g)`,
  REWRITE_TAC[is_closed_by;o_DEF] THEN MESON_TAC[]);;

let IS_CLOSED_BY_I = prove
  (`!s. is_closed_by s I`,
  REWRITE_TAC[is_closed_by;I_THM]);;

let IS_CLOSED_BY_COP_ADD = prove
  (`!s op1 op2.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (op1+op2)`,
  IMP_REWRITE_TAC[is_closed_by;COP_TO_CFUN;CFUN_SUBSPACE_ADD]);;

let IS_CLOSED_BY_COP_SUB = prove
  (`!s op1 op2.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (op1-op2)`,
  IMP_REWRITE_TAC[is_closed_by;COP_TO_CFUN;CFUN_SUBSPACE_SUB]);;

let IS_CLOSED_BY_COP_MUL = prove
  (`!s op1 op2.
      is_closed_by s op1 /\ is_closed_by s op2 ==> is_closed_by s (op1**op2)`,
  IMP_REWRITE_TAC[is_closed_by;COP_TO_CFUN]);;

let IS_CLOSED_SCALAR = prove
  (`!s a. is_cfun_subspace s ==> is_closed_by s (a % I)`, 
  SIMP_TAC[is_closed_by;is_cfun_subspace;COP_TO_CFUN]);;

let IS_CLOSED_INPROD_SCALAR = inner_space_prove
  ("!a. is_closed_by s (a % I)", 
  SIMP_TAC[is_closed_by;is_inner_space;IS_CLOSED_SCALAR]);;

let IS_CLOSED_BY_COP_SMUL = prove
  (`!s a op.
      is_cfun_subspace s /\ is_closed_by s op ==> is_closed_by s (a % op)`,
  IMP_REWRITE_TAC[is_closed_by;COP_TO_CFUN;CFUN_SUBSPACE_SMUL]);;

let IS_CLOSED_BY_COMMUTATOR = prove
  (`!s a op.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (commutator op1 op2)`,
  IMP_REWRITE_TAC[commutator;IS_CLOSED_BY_COP_MUL;IS_CLOSED_BY_COP_SUB]);;


(* ------------------------------------------------------------------------- *)
(* HERMITIAN                                                                 *)
(* ------------------------------------------------------------------------- *)

let is_hermitian = new_definition
  `is_hermitian ((s,inprod):inner_space) op1 op2 <=>
    is_inner_space (s,inprod) ==>
      is_closed_by s op1 /\ is_closed_by s op2
      /\ is_linear_cop op1 /\ is_linear_cop op2
      /\ !x y. x IN s /\ y IN s ==> inprod x (op1 y) = inprod (op2 x) y`;;

let [HERM_IS_CLOSED_BY_L;HERM_IS_CLOSED_BY_R;HERM_LINCOP_L;HERM_LINCOP_R;_] =
  preprocess (EQ_RIMP is_hermitian);;

let HERM_LINCOP_L,HERM_LINCOP_R =
  let f = GEN_ALL o REWRITE_RULE[GSYM FORALL_INSPACE_THM] o GENL
    [`s:cfun->bool`;`inprod:inprod`] o SPEC_ALL in
  f HERM_LINCOP_L,f HERM_LINCOP_R;;

let ADD_HERM = full_inner_space_prove
  ("!op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
    ==> is_hermitian is (op1+op3) (op2+op4)",
  REWRITE_TAC[FORALL_INSPACE_THM;is_hermitian;is_closed_by]
  THEN IMP_REWRITE_TAC (lincompose_thms ()) THEN REWRITE_TAC[COP_TO_CFUN]
  THEN IMP_REWRITE_TAC[CFUN_SUBSPACE_ADD;INSPACE_IS_SUBSPACE;
    INSPACE_ADD_LDIST;INSPACE_ADD_RDIST]);;

let SUB_HERM = full_inner_space_prove
  ("!op1 op2 op3 op4. 
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
      ==> is_hermitian is (op1-op3) (op2-op4)",
  REWRITE_TAC[FORALL_INSPACE_THM;is_hermitian;is_closed_by]
  THEN IMP_REWRITE_TAC (lincompose_thms ()) THEN REWRITE_TAC[COP_TO_CFUN]
  THEN IMP_REWRITE_TAC[CFUN_SUBSPACE_SUB;INSPACE_IS_SUBSPACE;
    INSPACE_SUB_LDIST;INSPACE_SUB_RDIST]);;

let MUL_HERM = full_inner_space_prove
  ("!op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4  
      ==> is_hermitian is (op1**op3) (op4**op2)",
  REWRITE_TAC[FORALL_INSPACE_THM;is_hermitian;is_closed_by]
  THEN IMP_REWRITE_TAC (lincompose_thms () @ [COP_TO_CFUN;cop_mul;o_DEF]));;

let SMUL_HERM = full_inner_space_prove
  ("!a op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
      ==> is_hermitian is (a % op1) (cnj a % op2)",
  REWRITE_TAC[FORALL_INSPACE_THM;is_hermitian;is_closed_by]
  THEN IMP_REWRITE_TAC (lincompose_thms ()) THEN REWRITE_TAC[COP_TO_CFUN]
  THEN IMP_REWRITE_TAC[CFUN_SUBSPACE_SMUL;INSPACE_IS_SUBSPACE;INSPACE_LSMUL;
    INSPACE_RSMUL;CNJ_CNJ]);;

let ZERO_HERM = prove
  (`!is. is_hermitian is cop_zero cop_zero`,
  REWRITE_TAC[FORALL_INSPACE_THM;is_hermitian;is_closed_by;LINCOP_ZERO]
  THEN IMP_REWRITE_TAC[COP_ZERO_THM;CFUN_SUBSPACE_ZERO;INSPACE_IS_SUBSPACE;
    INSPACE_RZERO;INSPACE_LZERO]);;
  
let ARITH_HERM_CLAUSES =
  CONJS [ZERO_HERM;ADD_HERM;SUB_HERM;MUL_HERM;SMUL_HERM];;

let HERM_SYM = prove
  (`!is op1 op2.
    is_hermitian is op1 op2 <=> is_hermitian is op2 op1`,
  REWRITE_TAC[FORALL_INSPACE_THM;is_hermitian;is_closed_by]
  THEN MESON_TAC[CX_INJ;INSPACE_CNJ]);;

let HERM_UNIQUENESS = prove
  (`!s inprod op1 op2 op3.
      is_inner_space (s,inprod)
      /\ is_hermitian (s,inprod) op1 op2 /\ is_hermitian (s,inprod) op1 op3
        ==> !x. x IN s ==> op2 x = op3 x`,
  IMP_REWRITE_TAC[is_hermitian;is_closed_by;GSYM INSPACE_INJ_ALT]);;

let HERM_UNIQUENESS_ALT = prove
  (`!s inprod op1 op2 op3. 
    is_inner_space (s,inprod) /\
    is_hermitian (s,inprod) op2 op1 /\ is_hermitian (s,inprod) op3 op1
      ==> !x. x IN s ==> op2 x = op3 x`,
  MESON_TAC[HERM_SYM;HERM_UNIQUENESS]);;

let HERM_PROP_ADVANCED = inner_space_prove
  ("!a b op1 op2 op3 op4 op5.
    is_hermitian (s,inprod) op1 op2 /\ is_hermitian (s,inprod) op3 op4
    /\ is_hermitian (s,inprod) op5 (a % op1 + b % op3)
      ==> !x. x IN s ==> op5 x = (cnj a % op2 + cnj b % op4) x",
  IMP_REWRITE_TAC[HERM_UNIQUENESS_ALT]
  THEN TARGET_REWRITE_TAC[ADD_HERM;HERM_SYM] SMUL_HERM);;


(* ------------------------------------------------------------------------- *)
(* SELF ADJOINT                                                              *)
(* ------------------------------------------------------------------------- *)

let is_self_adjoint = new_definition
  `is_self_adjoint is op <=> is_hermitian is op op`;;

let IS_SELF_ADJOINT =
  REWRITE_RULE[FORALL_INSPACE_THM;is_hermitian] is_self_adjoint;;

let SELF_ADJ_IS_LINCOP = full_inner_space_prove
  ("!op. is_self_adjoint is op ==> is_linear_cop op",
  IMP_REWRITE_TAC[is_self_adjoint;HERM_LINCOP_L]);;

let SELF_ADJ_IS_CLOSED_BY = inner_space_prove
  ("!op. is_self_adjoint (s,inprod) op ==> is_closed_by s op",
  IMP_REWRITE_TAC[is_self_adjoint;HERM_IS_CLOSED_BY_L]);;

let SELF_ADJ_INPROD = inner_space_prove
  ("!op1 op2. is_self_adjoint (s,inprod) op1 /\ is_closed_by s op2
    ==> !x y. x IN s /\ y IN s
      ==> inprod x ((op1 ** op2) y) = inprod (op1 x) (op2 y)",
  IMP_REWRITE_TAC[IS_SELF_ADJOINT;COP_MUL;is_closed_by]);;
  
List.iter (fun (s,t) -> Meta.let_ ~suffix:"_SELF_ADJ" s
  ("full_inner_space_prove(\"" ^ t
    ^ "\",MESON_TAC[is_self_adjoint;ARITH_HERM_CLAUSES;REAL_CNJ]);;"))
  [
    "ADD",  "!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
      ==> is_self_adjoint is (op1 + op2)";
    "SUB",  "!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
      ==> is_self_adjoint is (op1 - op2)";
    "SMUL", "!a op. real a /\ is_self_adjoint is op
      ==> is_self_adjoint is (a % op)";
    "MUL", "!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
      /\ op1 ** op2 = op2 ** op1
      ==> is_self_adjoint is (op1 ** op2)";
  ];;

let I_SELF_ADJ = prove
  (`!is. is_self_adjoint is I`,
  REWRITE_TAC[FORALL_INSPACE_THM;IS_SELF_ADJOINT;LINCOP_I;I_THM;
    IS_CLOSED_BY_I]);;

let ZERO_SELF_ADJ = prove
  (`!is. is_self_adjoint is cop_zero`,
  REWRITE_TAC[is_self_adjoint;ZERO_HERM]);;

let selfadj_thms,add_selfadj_thm,add_selfadj_thms = updatable_thms ();; 
let SELF_ADJOINT_TAC g = IMP_REWRITE_TAC (selfadj_thms ()) g;;

add_selfadj_thms [ADD_SELF_ADJ;SUB_SELF_ADJ;SMUL_SELF_ADJ;
  REWRITE_RULE[COP_SMUL] SMUL_SELF_ADJ;MUL_SELF_ADJ;I_SELF_ADJ;ZERO_SELF_ADJ];;

let ANTI_COMMUTATOR_SELF_ADJ = full_inner_space_prove
  ("!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (op1 ** op2 + op2 ** op1)",
  REWRITE_TAC[FORALL_INSPACE_THM;IS_SELF_ADJOINT]
  THEN IMP_REWRITE_TAC (lincompose_thms () @ [IS_CLOSED_BY_COP_ADD;
    IS_CLOSED_BY_COP_MUL;IS_CLOSED_BY_COP_MUL])
  THEN REWRITE_TAC[COP_MUL;COP_ADD;is_closed_by]
  THEN IMP_REWRITE_TAC[INSPACE_IS_SUBSPACE;INSPACE_ADD_LDIST;
    INSPACE_ADD_RDIST]
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

add_selfadj_thm ANTI_COMMUTATOR_SELF_ADJ;;

let NEG_SELF_ADJ = full_inner_space_prove
  ("!op. is_linear_cop op /\ is_self_adjoint is op
    ==> is_self_adjoint is (--op)",
  TARGET_REWRITE_TAC[GSYM COP_SUB_LZERO] SUB_SELF_ADJ THEN SELF_ADJOINT_TAC);;

add_selfadj_thm NEG_SELF_ADJ;;

let SCALAR_II_HERM = inner_space_prove
  ("!op. is_linear_cop op /\ (!x y. inprod (op x) y = -- (inprod x (op y)))
      /\ is_closed_by s op
        ==> is_self_adjoint (s,inprod) (ii % op)",
  IMP_REWRITE_TAC ([IS_SELF_ADJOINT;COP_SMUL_THM;IS_CLOSED_BY_COP_SMUL;
    is_closed_by;INSPACE_IS_SUBSPACE;INSPACE_LSMUL;INSPACE_RSMUL;CNJ_II]
    @ lincompose_thms ())
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

add_selfadj_thm SCALAR_II_HERM;;

let COMMUTATOR_ANTI_HERM = inner_space_prove
  ("!op1 op2. is_self_adjoint (s,inprod) op1 /\ is_self_adjoint (s,inprod) op2
    ==> !x y. x IN s /\ y IN s
      ==> inprod (commutator op1 op2 x) y = --(inprod x (commutator op1 op2 y))",
  IMP_REWRITE_TAC[commutator;IS_SELF_ADJOINT;COP_MUL_THM;COP_SUB_THM;is_closed_by;
    INSPACE_SUB_LDIST;INSPACE_SUB_RDIST;COMPLEX_NEG_SUB]
  THEN REPEAT STRIP_TAC THEN ASM_IMP_REWRITE_TAC[]);;

add_selfadj_thm COMMUTATOR_ANTI_HERM;;

let II_COMMUTATOR_HERM = full_inner_space_prove
  ("!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (ii % commutator op1 op2)",
  REWRITE_TAC[FORALL_INSPACE_THM]
  THEN IMP_REWRITE_TAC[IS_SELF_ADJOINT;COP_SMUL_THM;INSPACE_RSMUL;
    INSPACE_LSMUL;IS_CLOSED_BY_COMMUTATOR;IS_CLOSED_BY_COP_SMUL;CNJ_II;II_NZ;
    INSPACE_IS_SUBSPACE;COMPLEX_MUL_LNEG;GSYM COMPLEX_MUL_RNEG;
    COMPLEX_EQ_MUL_LCANCEL]
  THEN TARGET_REWRITE_TAC[COMPLEX_FIELD `x = --y <=> y = --x:complex`]
    COMMUTATOR_ANTI_HERM
  THEN IMP_REWRITE_TAC ([is_self_adjoint;is_hermitian;
    is_closed_by;REWRITE_RULE[is_closed_by] IS_CLOSED_BY_COMMUTATOR;
    INSPACE_IS_SUBSPACE] @ lincompose_thms ()));;
 
add_selfadj_thm II_COMMUTATOR_HERM;;

let EXPEC_HERM_REAL = inner_space_prove
  ("!op state. is_self_adjoint (s,inprod) op /\ state IN s
    ==> real (expectation inprod state op)", 
  IMP_REWRITE_TAC[IS_SELF_ADJOINT;expectation;is_closed_by;REAL_CNJ;
    INSPACE_CNJ]
  THEN SIMP_TAC[]);;

add_real_thms [EXPEC_HERM_REAL;REWRITE_RULE[expectation] EXPEC_HERM_REAL];;

let DEVIATION_HERM = inner_space_prove
  ("!op state. is_self_adjoint (s,inprod) op /\ state IN s
    ==> is_self_adjoint (s,inprod) (deviation inprod state op)",
  REWRITE_TAC[DEVIATION_ALT] THEN SELF_ADJOINT_TAC THEN REAL_TAC);;

add_selfadj_thms [DEVIATION_HERM;REWRITE_RULE[deviation] DEVIATION_HERM];;

let VARIANCE_REAL = inner_space_prove
  ("!op state.  state IN s /\ is_self_adjoint (s,inprod) op
    ==> real (variance inprod state op)", 
  REWRITE_TAC[variance] THEN REAL_TAC THEN SELF_ADJOINT_TAC);;

add_real_thm VARIANCE_REAL;;


(* ------------------------------------------------------------------------- *)
(* EIGEN VALUES AND VECTORS                                                  *)
(* ------------------------------------------------------------------------- *)

let is_eigen_pair = new_definition
  `is_eigen_pair (op:cfun->cfun) (x,a) <=>
    is_linear_cop op ==> op x = a % x /\ ~(x = cfun_zero)`;;

let EIGEN_PAIR_SMUL = prove
  (`!op v x. is_eigen_pair op (x,v)
    ==> !a. ~(a = Cx(&0)) ==> is_eigen_pair op (a % x,v)`,
  SIMP_TAC[is_eigen_pair;CFUN_ENTIRE;LINCOP_SMUL;CFUN_SMUL_SYM]);;

let EIGEN_PAIR_ADD = prove
  (`!op v x y. is_eigen_pair op (x,v) /\ is_eigen_pair op (y,v)
        /\ ~(x + y = cfun_zero)
          ==> is_eigen_pair op (x+y,v)`,
  SIMP_TAC[is_eigen_pair;LINCOP_ADD;CFUN_ADD_LDISTRIB]);;

let EIGEN_SPACE_THM = prove
  (`!op. is_linear_cop op ==>
    !a. is_cfun_subspace ({ x | is_eigen_pair op (x,a) } UNION { cfun_zero })`,
  SIMP_TAC[is_cfun_subspace;IN_ELIM_THM;IN_UNION;IN_SING;CFUN_ENTIRE]
  THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CFUN_ADD_RID;CFUN_ADD_LID]
  THEN ASM_MESON_TAC[EIGEN_PAIR_SMUL;EIGEN_PAIR_ADD]);;

let is_eigen_val = new_definition
  `is_eigen_val (op:cfun->cfun) a <=> ?x. is_eigen_pair op (x,a)`;;

let is_eigen_fun = new_definition
  `is_eigen_fun (op:cfun->cfun) x <=> ?a. is_eigen_pair op (x,a)`;;
