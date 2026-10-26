(* Actual checked construction supplies tuple staging layout directly from
   source type evaluation. Complete argument memory remains a producer fact. *)
Theory abiCallerTupleLayout
Ancestors
  abiCallerHeader abiTupleEncodeSourceLayout abiTupleEncodeLayout
  compileVyper compileEnv vyperContext vyperValue vyperABI
  finite_map list

Theorem abi_caller_tuple_layout:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  LENGTH ops = LENGTH tys /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) tys tvs ==>
  abi_tuple_encode_layout
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans)
    (ZIP (ops,tys)) (vyper_to_abi_types (type_env tops) tys)
Proof
  strip_tac >>
  `LIST_REL (abi_decoder_header
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)) tys tvs` by
    (irule LIST_REL_mono >>
     qexists_tac `\ty tv. evaluate_type (type_env tops) ty = SOME tv` >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     irule abi_caller_header >> simp[] >> qexists_tac `in_deploy` >> simp[]) >>
  drule_all abi_tuple_encode_layout_headers >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_TUPLE_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller tuple layout not kernel closed: " ^ n)
  end) (DB.thms "abiCallerTupleLayout");
