(* Operand-general counted paths for the storage/transient nested-pop suffix. *)
Theory popNestedStorageSuffixMemory
Ancestors
  exprSimPopNestedBase fragGasSeqMem fragGasSeqAbort fragExecMem
  instMemFrontier storageCopyGasPath allocaHistoryFragment bodyUnopFragMemory
  venomMemProofs venomInstProofs venomExecSemantics venomState venomInst
  emitHelper exprLoweringProps compileEnv fragExec list rich_list

Theorem nested_pop_suffix_mem_checks[local]:
  run_inst_seq_mem_ok
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s
Proof
  irule run_inst_seq_mem_ok_every >> Cases_on `tr` >>
  simp[nested_pop_suffix_def, mk_inst_def, below_frontier_no_ranges]
QED

Theorem nested_pop_suffix_path_mem:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  code = nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq_mem_ok code s` by simp[nested_pop_suffix_mem_checks] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (Cases_on `tr` >> simp[nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_mem >>
  Cases_on `tr` >> simp[nested_pop_suffix_def, mk_inst_def]
QED

Theorem nested_pop_suffix_abort_path_mem:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  code = nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = Abort a t ==>
  ?j. gas_marked_path T ctx func s 0 (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq_mem_ok code s` by simp[nested_pop_suffix_mem_checks] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) code` by
    (Cases_on `tr` >> simp[nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  irule run_inst_seq_abort_zero_path_mem >> metis_tac[]
QED

Theorem nested_pop_suffix_run_alloca_fields:
  run_inst_seq (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> conj_tac
  >- (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_allocas` run_inst_seq_preserves_field)) >>
      goal_assum (drule_at Any) >> rpt strip_tac >>
      irule step_inst_base_preserves_allocas >> qexists_tac `i` >>
      Cases_on `tr` >> gvs[nested_pop_suffix_def, mk_inst_def]) >>
  irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_alloca_next` run_inst_seq_preserves_field)) >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  irule step_inst_base_preserves_alloca_next >> qexists_tac `i` >>
  Cases_on `tr` >> gvs[nested_pop_suffix_def, mk_inst_def]
QED

Theorem nested_pop_suffix_run_history:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  code = nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = code ++ rest` by
    metis_tac[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (Cases_on `tr` >> simp[nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED
