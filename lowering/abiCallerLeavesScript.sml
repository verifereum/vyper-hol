(* Checked construction supplies flag counts, including during semantic
   environment descent. Base-type coherence is reused from the primitive
   caller theory and needs no struct-map invariant. *)
Theory abiCallerLeaves
Ancestors
  abiCallerHeader abiCallerTypeEnv abiDecoderCallerFlags abiDecoderPrimitiveCaller
  abiDecoderCoherence compileVyper compileEnv vyperContext vyperValue
  finite_map pair

Theorem abi_caller_flag_namespace:
  FLOOKUP (type_env tops) nsid = SOME (FlagArgs n) ==>
  FST nsid = NONE
Proof
  Cases_on `nsid` >> simp[type_env_def] >> strip_tac >>
  drule (Q.INST [`src` |-> `NONE:num option`] type_env_flag_declaration) >> simp[]
QED

Theorem abi_caller_flag_count:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  FLOOKUP (type_env tops) nsid = SOME (FlagArgs n) ==>
  (build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans).ce_flag_n_members (nsid_to_string nsid) = n
Proof
  strip_tac >> drule abi_caller_flag_namespace >> strip_tac >>
  Cases_on `nsid` >> gvs[] >>
  drule_all decoder_caller_flag_count >> simp[nsid_to_string_def]
QED

Theorem abi_caller_flag_coherent:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\ evaluate_type env (FlagT nsid) = SOME tv ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) env sf (FlagT nsid) tv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (FlagT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP env nsid = SOME (FlagArgs members)` >>
  `FLOOKUP (type_env tops) nsid = SOME (FlagArgs members)` by
    (irule FLOOKUP_SUBMAP >> qexists_tac `env` >> simp[]) >>
  drule_all abi_caller_flag_count >> strip_tac >>
  drule_all abi_caller_header >> strip_tac >>
  simp[abi_decoder_coherent_flag_iff]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_LEAVES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller leaf metadata not kernel closed: " ^ n)
  end) (DB.thms "abiCallerLeaves");
