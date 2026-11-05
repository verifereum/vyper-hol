Theory stmtForArrayMemoryBodyEntry
Ancestors
  stmtForArrayMemoryCopy loweringPosts compileEnv venomState
  exprLoweringProps fragGasSeqMem allocaHistoryFragment
  words arithmetic list

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
