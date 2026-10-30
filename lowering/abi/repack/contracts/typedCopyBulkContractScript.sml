(* TOP-LEVEL: the actual constant-size memory copy supplies the typed copy
   contract for every complete layout, including zero-sized values. *)
Theory typedCopyBulkContract
Ancestors
  typedCopyContract typedSArrayDynInvariant memoryStoreCode memoryStoreProps
  memoryValueDefs memoryValueTyping valueEncoding compileEnv fragBlockPath fragExec
  instIdxIndep venomState venomInst list words arithmetic

Theorem compile_copy_memory_contract:
  !ctx func dst src tv cs ret cs'.
    compile_copy_memory dst src (type_memory_size tv) cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src tv tv cs cs'
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `type_memory_size tv < dimword(:256)` by decide_tac >>
  `val_wf tv v` by (irule value_has_type_val_wf >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) compile_copy_memory_path >>
  `memory_value_rel tv v (w2n dst_addr)
    (memory_copy_result (type_memory_size tv) dst_addr src_addr ss).vs_memory` by
    (irule memory_copy_result_layout >> simp[]) >>
  qexists_tac `(memory_copy_result (type_memory_size tv) dst_addr src_addr ss)
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx, array_copy_frame_def] >> rpt gen_tac >> DISCH_TAC >>
  irule memory_copy_result_frame >> simp[]
QED
