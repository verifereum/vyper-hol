(* Singleton wrapping preserves source type evaluation and actual caller
   coherence, with no extra slot-size assumption. *)
Theory abiCallerWrapped
Ancestors
  abiCallerCoherence compileVyper compileEnv vyperTypeSystem vyperValue
  vyperTyping vyperContext list

Theorem abi_caller_singleton_type:
  evaluate_type env ty = SOME tv ==>
  evaluate_type env (TupleT [ty]) = SOME (TupleTV [tv])
Proof
  strip_tac >> drule (cj 1 evaluate_type_well_formed) >> strip_tac >>
  drule well_formed_type_value_slot_size >>
  simp[evaluate_type_def, type_slot_size_def]
QED

Theorem abi_caller_wrapped_coherent:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type
      code_stmts use_trans).ce_struct_fields
    (if wrapped then TupleT [ty] else ty) (if wrapped then TupleTV [tv] else tv)
Proof
  strip_tac >> drule abi_caller_singleton_type >> strip_tac >>
  `assignable_type (type_env tops) (TupleT [ty])` by
    simp[Once assignable_type_def, well_formed_type_def] >>
  Cases_on `wrapped` >> irule abi_caller_coherent >> simp[] >>
  qexists_tac `in_deploy` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_WRAPPED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller wrapped type not kernel closed: " ^ n)
  end) (DB.thms "abiCallerWrapped");
