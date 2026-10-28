(* TOP-LEVEL: the actual typed scalar copy loads through the source pointer
   and stores its encoded word. Its single temporary comes from the real
   compiler result, and previously defined output names are permitted. *)
Theory typedCopyWordContract
Ancestors
  typedCopyContract typedWordStoreProps typedSArrayDynInvariant abiEncoderPathProps
  localValueStoreProps abiBytestringCode memoryValueDefs valueEncoding
  context compileEnv fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem compile_store_memory_typed_word_contract:
  !tenv ctx func cenv dst ty tv src src_ty cs ret cs'.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    compile_store_memory_typed cenv dst ty src src_ty cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src tv tv cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_typed_word_abi_code >> strip_tac >>
  drule compile_abi_encode_static_code >> strip_tac >>
  `type_memory_size tv = 32` by (drule_all evaluated_word_memory_size >> simp[]) >>
  asm_simp_tac (srw_ss()) [typed_copy_contract_def, compiler_var_names_def, GENLIST_CONS] >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `ty`, `tv`, `v`, `dst`, `src`, `src_ty`,
    `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`] compile_store_memory_typed_word_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> asm_simp_tac (srw_ss()) [array_copy_frame_def] >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed scalar typed copy contract: " ^ name)
  end) (DB.thms "typedCopyWordContract")
