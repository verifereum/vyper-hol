Theory immutableDeployStoreLength
Ancestors
  exprLoweringProps venomExecSemantics venomState venomInst venomMemProps
  immutableDeployAssignExecution

Theorem immutable_store_step_memory_length[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\
  step_inst_base i s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  simp[listTheory.MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base i s = OK t` mp_tac >>
  simp[Once step_inst_base_def] >>
  simp[exec_pure2_def, exec_read1_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def, istore_def,
    LENGTH_mstore_eq]
QED

Theorem immutable_store_seq_memory_length:
  !code s t.
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) code /\
  run_inst_seq code s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  `LENGTH s.vs_memory <= LENGTH v.vs_memory` by
    (irule immutable_store_step_memory_length >>
     goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem immutable_store_words_memory_length:
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule immutable_store_words_insts >> strip_tac >>
  drule_all immutable_store_seq_memory_length >> simp[]
QED
