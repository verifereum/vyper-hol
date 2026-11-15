Theory deployOutcomesFreeCustomErrors
Ancestors
  deployOutcomesFreeLowering stmtLowering compileEnv emitHelper venomInst list

Theorem outcomes_free_compile_custom_error_store_args:
  !es tys dst off s.
  P ADD /\
  (!e st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce (expr_type e) e st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v st)))) /\
  (!a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce a b ty sty st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_custom_error_store_args ce es tys dst off s)))
Proof
  Induct_on `es` >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >> simp[compile_custom_error_store_args_def, outcomes_free_return] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, gen_tac, strip_tac, IF_CASES_TAC, first_assum irule]) >> simp[]
QED

Theorem outcomes_free_compile_revert_with_custom_error:
  P INVALID /\ P ADD /\ P MSTORE /\ P REVERT /\
  (!e st. MEM e (custom_error_exprs err) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce (expr_type e) e st)))) /\
  (!n st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v st)))) /\
  (!a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce a b ty sty st)))) /\
  (!a b info st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_abi_encode_to_buf a b info st)))) ==>
  !s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_revert_with_custom_error ce err s)))
Proof
  strip_tac >> Cases_on `err` >> rpt strip_tac >>
  simp[compile_revert_with_custom_error_def] >>
  Cases_on `ce.ce_error_info (nsid_to_string p)` >> simp[outcomes_free_emit_ops] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
      outcomes_free_compile_custom_error_store_args]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, gen_tac, strip_tac, IF_CASES_TAC, first_assum irule])
QED

Theorem outcomes_free_stmt_assert_custom:
  P JNZ /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value compile_expr ce (BaseT BoolT) e s)))) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_revert_with_custom_error ce err s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Assert e (AssertCustomError err)) s)))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_fresh, outcomes_free_new_block,
      outcomes_free_emit_ops, outcomes_free_return]),
    irule outcomes_free_ignore_bind >> conj_tac,
    irule outcomes_free_bind >> conj_tac,
    gen_tac, disch_tac, first_assum irule])
QED

Theorem outcomes_free_stmt_raise_custom:
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_revert_with_custom_error ce err s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Raise (RaiseCustomError err)) s)))
Proof
  simp[compile_stmt_def]
QED
