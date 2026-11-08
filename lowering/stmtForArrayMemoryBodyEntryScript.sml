Theory stmtForArrayMemoryBodyEntry
Ancestors
  stmtForArrayMemoryCopy loweringPosts compileEnv venomState
  exprLoweringProps fragGasSeqMem allocaHistoryFragment
  words arithmetic list rich_list

Theorem array_prefix_return_buf_frame:
  return_buf_frame d ce sa s /\ ce'.ce_return_buf = ce.ce_return_buf /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> x <> ov /\ x <> ep) /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==> lookup_var x t = lookup_var x s) /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  return_buf_frame d ce' sb (t with vs_inst_idx := j)
Proof
  Cases_on `d` >> simp[return_buf_frame_def] >>
  PairCases_on `x` >> simp[return_buf_frame_def] >> rpt strip_tac >>
  qexistsl_tac [`x`, `slot_size`] >>
  simp[lookup_var_def] >>
  conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
  fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem array_prefix_counted_history:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  gas_path_mem ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
  alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  strip_tac >> conj_tac
  >- (irule run_inst_seq_gas_path_mem >> goal_assum (drule_at Any) >> simp[]) >>
  irule alloca_history_run_inst_seq >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  gvs[IS_PREFIX_APPEND, EVERY_MEM] >>
  goal_assum (drule_at Any) >> simp[]
QED
