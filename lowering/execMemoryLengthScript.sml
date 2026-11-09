Theory execMemoryLength
Ancestors
  execMemoryLengthBase calleeTransport o1LowerDloadJointRestore
  venomExecProofs venomExecSemantics

Theorem execution_memory_length_joint[local]:
  (!fuel ctx inst s.
    (!t. step_inst fuel ctx inst s = OK t ==>
         LENGTH s.vs_memory <= LENGTH t.vs_memory) /\
    (!ret t. step_inst fuel ctx inst s = IntRet ret t ==>
         LENGTH s.vs_memory <= LENGTH t.vs_memory)) /\
  (!fuel ctx bb s.
    (!t. exec_block fuel ctx bb s = OK t ==>
         LENGTH s.vs_memory <= LENGTH t.vs_memory) /\
    (!ret t. exec_block fuel ctx bb s = IntRet ret t ==>
         LENGTH s.vs_memory <= LENGTH t.vs_memory)) /\
  (!fuel ctx fn s.
    (!t. run_blocks fuel ctx fn s = OK t ==>
         LENGTH s.vs_memory <= LENGTH t.vs_memory) /\
    (!ret t. run_blocks fuel ctx fn s = IntRet ret t ==>
         LENGTH s.vs_memory <= LENGTH t.vs_memory))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume execution_memory_length_joint[step]:
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (once_rewrite_tac[step_inst_def] >> simp[] >>
      conj_tac >> rpt gen_tac >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      imp_res_tac setup_callee_shared_fields >>
      drule ld_bind_outputs_vars_only >> strip_tac >>
      gvs[adopt_return_fmp_def, merge_callee_state_def] >>
      Cases_on `ret.iret_adopt_fmp` >> gvs[] >>
      qpat_x_assum `t = _` (mp_tac o Q.AP_TERM `\u. u.vs_memory`) >>
      simp[] >> metis_tac[]) >>
  once_rewrite_tac[step_inst_def] >>
  simp[] >> metis_tac[step_base_memory_length, step_base_intret_memory_length]
QED

Resume execution_memory_length_joint[block]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[exec_block_def] >>
  conj_tac >> rpt gen_tac >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Resume execution_memory_length_joint[blocks]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[run_blocks_def] >>
  Cases_on `fuel` >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >>
  conj_tac >> rpt gen_tac >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  qpat_x_assum `_ = _ with vs_vars := _` (mp_tac o Q.AP_TERM `\u. u.vs_memory`) >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise execution_memory_length_joint

Theorem step_inst_memory_length:
  step_inst fuel ctx inst s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  metis_tac[execution_memory_length_joint]
QED
