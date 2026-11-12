Theory deployOutcomesFreeStmtExitCases
Ancestors
  deployOutcomesFreeLowering stmtLowering compileEnv emitHelper venomInst
  loweringShapeDefs

Theorem outcomes_free_stmt_assert_simple:
  P JNZ /\ P REVERT /\ P INVALID /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value compile_expr ce (BaseT BoolT) e s)))) ==>
  !lc ty reason s.
    (reason = AssertBare \/ reason = AssertUnreachable) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Assert e reason) s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_fresh, outcomes_free_new_block,
                    outcomes_free_emit_ops, outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac, first_assum irule]) >>
  simp[outcomes_free_fresh, outcomes_free_new_block,
       outcomes_free_emit_ops, outcomes_free_return] >> metis_tac[]
QED

Theorem outcomes_free_stmt_assert_reason:
  P JNZ /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value compile_expr ce (BaseT BoolT) e s)))) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_reason_message ce reason s)))) /\
  (!op ty n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_revert_with_reason ce op (ty : type) n s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Assert e (AssertReason reason)) s)))
Proof
  strip_tac >> rpt gen_tac >>
  simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_fresh, outcomes_free_new_block,
                    outcomes_free_emit_ops, outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac, first_assum irule]) >>
  simp[outcomes_free_fresh, outcomes_free_new_block,
       outcomes_free_emit_ops, outcomes_free_return] >> metis_tac[]
QED

Theorem outcomes_free_stmt_raise:
  P REVERT /\ P INVALID /\
  (!e s. reason = RaiseReason e /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_reason_message ce e s)))) /\
  (!op ty n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_revert_with_reason ce op (ty : type) n s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Raise reason) s)))
Proof
  strip_tac >> Cases_on `reason` >> gvs[] >> rpt gen_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_fresh, outcomes_free_new_block,
                    outcomes_free_emit_ops, outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac, first_assum irule]) >>
  simp[outcomes_free_emit_ops, outcomes_free_return]
QED

Theorem outcomes_free_stmt_return_none:
  P MLOAD /\ P RET /\ P JMP /\ P STOP /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_return_unlock ce s)))) /\
  (!key transient view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_nonreentrant_unlock key transient view s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Return NONE) s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `ce.ce_ctor_exit_label` >>
  Cases_on `ce.ce_nonreentrant` >> rename1 `ce.ce_nonreentrant = (nr, rest)` >>
  PairCases_on `rest` >> Cases_on `nr` >>
  Cases_on `ce.ce_return_pc` >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac, first_assum irule]) >>
  rename1 `ce.ce_return_pc = SOME loc` >> Cases_on `loc` >>
  simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac, first_assum irule])
QED

Theorem outcomes_free_stmt_log:
  P INVALID /\ P LOG /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_eval_all ce args s)))) /\
  (!topics s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_topic_ops topics s)))) /\
  (!ops tys buf off s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_store_data ce ops tys buf off s)))) /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!buf op info s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_to_buf buf op info s)))) ==>
  !id lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Log id args) s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `ce.ce_event_info (nsid_to_string id)` >>
  simp[compile_stmt_def, outcomes_free_emit_ops] >>
  rename1 `ce.ce_event_info _ = SOME info` >> PairCases_on `info` >>
  simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac, IF_CASES_TAC, first_assum irule])
QED

Theorem outcomes_free_stmt_return_some:
  P MLOAD /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value compile_expr ce ty e s)))) /\
  (!value rpc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_internal_return_from_env ce ty
        (lowered_value_type ce e) value rpc s)))) /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ptr value sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory_typed ce ptr ty value sty s)))) /\
  (!key transient view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_nonreentrant_unlock key transient view s)))) /\
  (!value prim raw nr key transient view s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_external_return value prim raw
        ce.ce_ret_enc_info ce.ce_max_return_size nr key transient view s)))) ==>
  !lc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Return (SOME e)) s)))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_stmt_def] >>
  strip_tac >> irule outcomes_free_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> Cases_on `ce.ce_return_pc` >-
   (simp[] >>
    rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
                irule outcomes_free_ignore_bind >> conj_tac,
                irule outcomes_free_bind >> conj_tac,
                gen_tac, disch_tac, IF_CASES_TAC, first_assum irule])) >>
  rename1 `ce.ce_return_pc = SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac, IF_CASES_TAC, first_assum irule])
QED
