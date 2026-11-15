Theory deployOutcomesFreeStmtFlowCases
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeStmtControl stmtLowering compileEnv emitHelper venomInst

Theorem outcomes_free_emit_jmp_if_not_terminated:
  P JMP ==>
  !lbl s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (emit_jmp_if_not_terminated lbl s)))
Proof
  rpt strip_tac >>
  simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def] >>
  IF_CASES_TAC >> simp[outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_stmt_if:
  P JNZ /\ P JMP /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value compile_expr cenv (BaseT BoolT) cond s)))) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts cenv lctx ty yes s)))) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts cenv lctx ty no s)))) ==>
  !s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt cenv lctx ty (If cond yes no) s)))
Proof
  strip_tac >> pure_rewrite_tac[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_get,
                outcomes_free_fresh, outcomes_free_new_block,
                outcomes_free_emit_ops, outcomes_free_emit_jmp_if_not_terminated]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              CHANGED_TAC BETA_TAC, gen_tac, disch_tac,
              IF_CASES_TAC])
QED

Theorem outcomes_free_stmt_range:
  P JMP /\ P JNZ /\ P ASSIGN /\ P SUB /\ P ADD /\ P EQ /\
  P MSTORE /\ P INVALID /\ P ALLOCA /\
  (!e s. (e = start_e \/ e = end_e) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value compile_expr cenv fty e s)))) /\
  (!a b c n signed s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_range_bound_checks a b c n signed s)))) /\
  (!env exit incr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts env (InLoop exit incr) ty stmts s)))) ==>
  !s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND
        (compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound stmts) s)))
Proof
  strip_tac >>
  `!a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      ((case (start_e,end_e) of
          (Literal _ (IntL x), Literal _ (IntL y)) => comp_return (Lit (i2w y - i2w x))
        | _ => emit_op SUB [b;a]) s)))` by
    (Cases_on `start_e` >> simp[outcomes_free_return, outcomes_free_emit_ops] >>
     Cases_on `end_e` >> simp[outcomes_free_return, outcomes_free_emit_ops] >>
     rpt gen_tac >> strip_tac >>
     BasicProvers.TOP_CASE_TAC >> simp[outcomes_free_return, outcomes_free_emit_ops] >>
     BasicProvers.TOP_CASE_TAC >> simp[outcomes_free_return, outcomes_free_emit_ops]) >>
  `!a b c s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      ((case (start_e,end_e) of
          (Literal _ (IntL x), Literal _ (IntL y)) => comp_return ()
        | _ => compile_range_bound_checks a b c bound (is_signed_type fty)) s)))` by
    (Cases_on `start_e` >> simp[outcomes_free_return] >>
     Cases_on `end_e` >> simp[outcomes_free_return] >>
     BasicProvers.TOP_CASE_TAC >> simp[outcomes_free_return] >>
     BasicProvers.TOP_CASE_TAC >> simp[outcomes_free_return]) >>
  fs[] >> pure_rewrite_tac[compile_stmt_def] >> BETA_TAC >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_get,
                outcomes_free_fresh, outcomes_free_new_block,
                outcomes_free_emit_ops, outcomes_free_emit_jmp_if_not_terminated,
                outcomes_free_declare_local, outcomes_free_emit_local_alloca]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              CHANGED_TAC BETA_TAC, gen_tac, disch_tac,
              IF_CASES_TAC]) >>
  rpt (BasicProvers.TOP_CASE_TAC >>
    simp[outcomes_free_return, outcomes_free_emit_ops])
QED

Theorem outcomes_free_stmt_array:
  P JMP /\ P JNZ /\ P ASSIGN /\ P ADD /\ P MUL /\ P EQ /\
  P GT /\ P ISZERO /\ P ASSERT /\ P INVALID /\ P ALLOCA /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr cenv (expr_type arr_e) arr_e s)))) /\
  (!ctor alloc loc ptr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_ptr_load ctor alloc loc ptr s)))) /\
  (!env src dst n loc slots ity sty s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_iter_elem_copy env src dst n loc slots ity sty s)))) /\
  (!env exit incr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts env (InLoop exit incr) ty stmts s)))) ==>
  !s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND
        (compile_stmt cenv lctx ty (For id fty (Array arr_e) bound stmts) s)))
Proof
  strip_tac >> pure_rewrite_tac[compile_stmt_def] >> BETA_TAC >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_get,
                outcomes_free_fresh, outcomes_free_new_block,
                outcomes_free_emit_ops, outcomes_free_emit_jmp_if_not_terminated,
                outcomes_free_declare_local, outcomes_free_emit_local_alloca]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              CHANGED_TAC BETA_TAC, gen_tac, disch_tac,
              IF_CASES_TAC]) >>
  rpt (BasicProvers.TOP_CASE_TAC >>
    simp[outcomes_free_return, outcomes_free_emit_ops])
QED
