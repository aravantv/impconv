(* ========================================================================= *)
(*                                                                           *)
(*       Library of complex function vector spaces: utility functions.       *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


let EQ_TO_IMP = TAUT `!P Q. (P <=> Q) <=> (P ==> Q) /\ (Q==>P)`;;

let LET_DEFS = CONJ LET_DEF LET_END_DEF;;

module Pa :
  sig
    val CONTEXT_TAC : ((string * pretype) list -> tactic) -> tactic
    val PARSE_IN_CONTEXT : (term -> tactic) -> (string -> tactic)
    val EXISTS_TAC : string -> tactic
    val SUBGOAL_THEN : string -> thm_tactic -> tactic
    val SUBGOAL_TAC : string -> string -> tactic list -> tactic
    val ASM_CASES_TAC : string -> tactic
    val BOOL_CASES_TAC : string -> tactic
    val SPEC_TAC : string * string -> tactic
    val SPEC : string -> thm -> thm
    val SPECL : string list -> thm -> thm
    val GEN : string -> thm -> thm
    val GENL : string list -> thm -> thm
    val X_GEN_TAC : string -> tactic
    val REAL_ARITH : string -> thm
    val REAL_FIELD : string -> thm
    val REAL_RING : string -> thm
    val ARITH_RULE : string -> thm
    val NUM_RING : string -> thm
    val INT_ARITH : string -> thm
    val call_with_interface : (unit -> 'a) -> (term -> 'b) -> string -> 'b
  end
  =
  struct
    let parse_preterm = fst o parse_preterm o lex o explode

    let CONTEXT_TAC ttac (asms,c as g) =
      let vs = frees c @ freesl (map (concl o snd) asms) in
      ttac (map (fun x -> name_of x,pretype_of_type(type_of x)) vs) g

    let PARSE_IN_CONTEXT ttac s =
      CONTEXT_TAC (fun env ->
        ttac (term_of_preterm (retypecheck env (parse_preterm s))))

    let type_of_forall = type_of o fst o dest_forall

    let force_type ?(env=[]) s ty =
      let pty = pretype_of_type ty in
      term_of_preterm (retypecheck env (Typing(parse_preterm s,pty)))

    let BOOL_CONTEXT_TAC ttac s =
      CONTEXT_TAC (fun env -> ttac (force_type ~env s bool_ty))

    let SUBGOAL_THEN s ttac = BOOL_CONTEXT_TAC (C SUBGOAL_THEN ttac) s
    let SUBGOAL_TAC l s tacs = BOOL_CONTEXT_TAC (C (SUBGOAL_TAC l) tacs) s

    let ASM_CASES_TAC = BOOL_CONTEXT_TAC ASM_CASES_TAC
    let BOOL_CASES_TAC = BOOL_CONTEXT_TAC BOOL_CASES_TAC

    let EXISTS_TAC s (_,c as g) =
      CONTEXT_TAC (fun env ->
        EXISTS_TAC (force_type ~env s (type_of (fst (dest_exists c))))) g
        
    let SPEC_TAC (u,x) =
      PARSE_IN_CONTEXT (fun u' -> SPEC_TAC (u',force_type x (type_of u'))) u

    let SPEC s th = SPEC (force_type s (type_of_forall (concl th))) th

    let SPECL tms th =
      try rev_itlist SPEC tms th with Failure _ -> failwith "SPECL"

    let GEN s th =
      GEN (try find ((=) s o name_of) (frees (concl th)) with _ -> parse_term s)
        th

    let GENL = itlist GEN

    let X_GEN_TAC s (_,c as g) = X_GEN_TAC (force_type s (type_of_forall c)) g

    let call_with_interface p f s =
      let i = !the_interface in
      p ();
      let res = f (parse_term s) in
      the_interface := i;
      res

    let [REAL_ARITH;REAL_FIELD;REAL_RING] =
      map (call_with_interface prioritize_real) [REAL_ARITH;REAL_FIELD;REAL_RING]
    let [ARITH_RULE;NUM_RING] =
      map (call_with_interface prioritize_num) [ARITH_RULE;NUM_RING]
    let INT_ARITH = call_with_interface prioritize_int INT_ARITH
  end;;

module Pa =
  struct
    include Pa
    let COMPLEX_FIELD = call_with_interface prioritize_complex COMPLEX_FIELD;;
    let SIMPLE_COMPLEX_ARITH =
      call_with_interface prioritize_complex SIMPLE_COMPLEX_ARITH;
  end;;

let wrap f x = f [x];;

let rec fixpoint f x =
  let y = f x in
  if y = x then y else fixpoint f y;;

let rec SPEC_VARS th =
  try
    let v,th' = SPEC_VAR th in
    let vs,th'' = SPEC_VARS th' in
    v::vs,th''
  with _ -> [],th;;

let MAP_FORALL_BODY f th =
  let vs,th = SPEC_VARS th in
  GENL vs (f th);;

let GCONV_TAC = CONV_TAC o DEPTH_CONV o CHANGED_CONV;;

let CONJS xs = end_itlist CONJ xs;;

let EQ_RIMP = MAP_FORALL_BODY (fst o EQ_IMP_RULE);;
let EQ_LIMP = MAP_FORALL_BODY (snd o EQ_IMP_RULE);;

let gimp_imp =
  let rec self vars premisses t =
    try
      let v,b = dest_forall t in
      self (v::vars) premisses b
    with _ ->
      try
        let p,c = dest_imp t in
        self vars (p::premisses) c
      with _ ->
        let body =
          match premisses with
          |[] -> t
          |_::_ -> mk_imp(list_mk_conj (rev premisses),t)
        in
        list_mk_forall(rev vars,body)
  in
  self [] [];;

let MATCH_TRANS thm1 thm2 =
  GEN_ALL (DISCH_ALL (MATCH_MP thm2 (UNDISCH (SPEC_ALL thm1))));;

let GCONV_TAC = CONV_TAC o DEPTH_CONV o CHANGED_CONV;;

(*
let THEN1 = ...*)

let rt = REWRITE_TAC;;
let rr = REWRITE_RULE;;
let (!!) t = REPEAT t;;
let (!?) t xs = REPEAT (MAP_FIRST (CHANGED_TAC o t) xs);;

(* Toploop related *)

module Meta =
  struct
    let exec =
      ignore o Toploop.execute_phrase false Format.std_formatter
        o !Toploop.parse_toplevel_phrase o Lexing.from_string

    let name ?(prefix="") ?(suffix="") s = prefix ^ s ^ suffix

    let let_ ?prefix ?suffix s v =
      exec ("let " ^ name ?prefix ?suffix s ^ " = " ^ v ^ ";;")

    let get = Obj.magic o Toploop.getvalue

    let wrap f t = f ^ "(parse_term(\"" ^ t ^ "\"))"
    let prove ?prefix ?suffix s t tac =
      print_endline ("Proved " ^ name ?prefix ?suffix s);
      let_ ?prefix ?suffix s (wrap ("C (curry prove) (" ^ tac ^ ")") t)
    let new_definition s t =
      print_endline ("Defined " ^ s);
      let_ s (wrap "new_definition" t)
  end;;

let updatable_thms () =
  let ths = ref [] in
  (fun () -> !ths),
  (fun t -> ths := t :: !ths),
  (fun ts -> ths := ts @ !ths);;

let property_db_temp = ref TRUTH;;

let property_db prefix =
  let properties = ref [] in
  let store_thm s th =
    let s' = prefix ^ "_" ^ s in
    property_db_temp := th;
    print_endline ("Stored theorem " ^ s');
    Meta.let_ s' "!property_db_temp";
    properties := (s,th) :: !properties
  in
  store_thm,fun () -> !properties;;

let prime_prefix s =
  let rec self n =
    if n < 0
    then failwith "prime_prefix"
    else
      if s.[n] = '\''
      then self (n-1)
      else String.sub s 0 (n+1)
  in
  self (String.length s - 1);;

let assoc_list x = snd o unzip o filter (fun (y,_) -> y = x);;

let group_by_prefix vs =
  let ord ((x:string),_) (y,_) = x < y in
  let xs = sort ord (map (fun v -> prime_prefix (name_of v),v) vs) in
  let prefixes = uniq (fst (unzip xs)) in
  map (fun p -> p,assoc_list p xs) prefixes;;

let mapi f = 
  let rec self i = function
  |[] -> []
  |a::l ->
      let r = f i a in
      r :: self (i + 1) l
  in
  self 0;;

let alt_names_by_prefix pfx = function
  |[_] as vs -> vs
  |_ as vs ->
      mapi (fun i v -> mk_var(pfx ^ string_of_int (i+1),type_of v)) vs;;

let alt_names =
  flat o map (fun (pfx,vs) -> zip vs (alt_names_by_prefix pfx vs))
    o group_by_prefix;;

let UNIQUE_NAME_CONV t =
  let vs = variables t in
  let mapping = filter (fun (x,y) -> x <> y) (alt_names vs) in
  DEPTH_CONV (fun u -> ALPHA_CONV (assoc (bndvar u) mapping) u) t;;

let UNIQUE_NAME_RULE = CONV_RULE UNIQUE_NAME_CONV;;


(* The following originally comes from tacticlib.ml *)

let CHANGED_RULE r thm =
  let thm' = r thm in
  if equals_thm thm thm' then failwith "CHANGED_RULE" else thm';;

let MAP_ASSUMPTIONS f =
  REPEAT (POP_ASSUM (MP_TAC o f)) THEN REPEAT DISCH_TAC;;

let REWRITE_ASSUMPTIONS xs = MAP_ASSUMPTIONS (REWRITE_RULE xs);;

let ON_FIRST_GOAL ?(out_of=2) x =
  let rec ( * ) n x = if n<=1 then [] else x :: (n-1) * x in
  x :: out_of * ALL_TAC;;

let MAP_ANTECEDENT f = DISCH_THEN (MP_TAC o f);;

let exn_to_bool f x = try ignore (f x); true with _ -> false;;

let strip_parentheses s =
  if s.[0] = '(' && s.[String.length s-1] = ')'
  then String.sub s 1 (String.length s-2) else s;;

let contains_sub_term_name name =
  exn_to_bool
    (find_term (fun x -> ((=) name o strip_parentheses o string_of_term) x));;

let try_or_id f x = try f x with _ -> x;;

let ASSUME_CONSEQUENCES x =
  ASM (MAP_EVERY (fun y -> try ASSUME_TAC (MATCH_MP x y) with _ -> ALL_TAC))
    [];;

let ASM_CSQ_THEN ?(remove=false) ?(match_=true) x ttac =
  (if remove then FIRST_X_ASSUM else FIRST_ASSUM)
    (ttac o (if match_ then MATCH_MP else MP) x);;

let ASM_CSQS_THEN x ttac =
  (* looks absurd, eh? But needed in order to control the execution flow *)
  let ttac x y = ttac x y in 
  REPEAT_TCL (fun y z -> ASM_CSQ_THEN z y ORELSE ttac z) ttac x;;

let distrib fs x = map (fun f -> f x) fs;;

let DISTRIB ttacs x = EVERY (distrib ttacs x);;

let LET_DEFs = CONJ LET_DEF LET_END_DEF;;

let GEQ_IMP x = GEN_ALL (MATCH_MP EQ_IMP (SPEC_ALL x));;

