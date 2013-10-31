(* ========================================================================= *)
(*                                                                           *)
(*           First-order matching and nets.                                  *)
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


(* ------------------------------------------------------------------------- *)
(* First-order matching of terms.                                            *)
(*                                                                           *)
(* Same note as in [drule.ml]:                                               *)
(* in the event of spillover patterns, this may return false results;        *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

let fo_term_match lcs p t =
  let fail () = failwith "fo_term_match" in
  let rec self bnds (tenv,tyenv as env) p t =
    match p,t with
    |Comb(p1,p2),Annot.Comb_(t1,t2,_) -> self bnds (self bnds env p1 t1) p2 t2
    |Abs(v,p),Annot.Abs_(v',t,_) ->
        let tyenv' = type_match (type_of v) (Annot.type_of v') tyenv in
        self ((v',v)::bnds) (tenv,tyenv') p t
    |Const(n,ty),Annot.Const_(n',ty',_) ->
        if n <> n' then fail ()
        else
          let tyenv' = type_match ty ty' tyenv in
          tenv,tyenv'
    |Var(n,ty) as v,t -> 
        (* Is [v] bound? *)
        (try if Annot.equal t (rev_assoc v bnds) then env else fail ()
        (* No *)
        with Failure _ ->
          if mem v lcs
          then
            match t with
            |Annot.Var_(n',ty') when n' = n & ty' = ty -> env
            |_ -> fail ()
          else
            let tyenv' = type_match ty (Annot.type_of t) tyenv in
            let t' = try Some (rev_assoc v tenv) with Failure _ -> None in
            match t' with
            |Some t' -> if t = t' then tenv,tyenv' else fail ()
            |None -> (t,v)::tenv,tyenv')
    |_ -> fail ()
  in
  let tenv,tyenv = self [] ([],[]) p (Annot.of_term t) in
  let inst = inst tyenv in
  List.rev_map (fun t,v -> Annot.to_term t,inst v) tenv,tyenv;;

let GEN_PART_MATCH_ALL =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc
  in
  fun partfn th ->
    let sth = SPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lcs = intersect (frees (concl th)) (freesl(hyp th)) in
    let fvs = subtract (subtract (frees bod) (frees pbod)) lcs in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = EQ_MP (ALPHA bod abod) sth in
      let insts,tyinsts = fo_term_match lcs (partfn abod) tm in
      let eth = INSTANTIATE_ALL ([],insts,tyinsts) (GENL fvs ath) in
      let fth = itlist (fun v th -> snd(SPEC_VAR th)) fvs eth in
      let tm' = partfn (concl fth) in
      if Pervasives.compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure";;

let exists_subterm p t =
  try ignore (find_term p t);true with Failure _ -> false;;

module Fo_nets =
  struct
    type term_label =
      |Vnet of int
      |Lcnet of string * int
      |Cnet of string * int
      |Lnet of int

    type 'a t = Netnode of (term_label * 'a t) list * 'a list

    let empty_net = Netnode([],[])

    let enter =
      let label_to_store lcs t =
        let op,args = strip_comb t in
        let nargs = length args in
        match op with
        |Const(n,_) -> Cnet(n,nargs),args
        |Abs(v,b) ->
          let b' = if mem v lcs then vsubst [genvar(type_of v),v] b else b in
          Lnet nargs,b'::args
        |Var(n,_) when mem op lcs -> Lcnet(n,nargs),args
        |Var(_,_) -> Vnet nargs,args
        |_ -> assert false
      in
      let rec net_update lcs elem (Netnode(edges,tips)) = function
        |[] -> Netnode(edges,elem::tips)
        |t::rts ->
            let label,nts = label_to_store lcs t in
            let child,others =
              try (snd F_F I) (remove (fun (x,y) -> x = label) edges)
              with Failure _ -> empty_net,edges in
            let new_child = net_update lcs elem child (nts@rts) in
            Netnode ((label,new_child)::others,tips)
      in
      fun lcs (t,elem) net -> net_update lcs elem net [t]

    let lookup =
      let label_for_lookup t =
        let op,args = strip_comb t in
        let nargs = length args in
        match op with
        |Const(n,_) -> Cnet(n,nargs),args
        |Abs(_,b) -> Lnet nargs,b::args
        |Var(n,_) -> Lcnet(n,nargs),args
        |Comb _ -> assert false
      in
      let rec follow (Netnode(edges,tips)) = function
        |[] -> tips
        |t::rts ->
            let label,nts = label_for_lookup t in
            let collection =
              try follow (assoc label edges) (nts@rts) with Failure _ -> []
            in
            let rec support = function
              |[] -> [0,rts]
              |t::ts ->
                  let ((k,nts')::res') as res = support ts in
                  (k+1,(t::nts'))::res
            in
            let follows =
              let f (k,nts) =
                try follow (assoc (Vnet k) edges) nts with Failure _ -> []
              in
              map f (support nts)
            in
            collection @ flat follows
      in
      fun t net -> follow net [t]

    let rec filter p (Netnode(edges,tips)) =
      Netnode(
        List.map (fun l,n -> l,filter p n) edges,
        List.filter p tips)
  end;;
