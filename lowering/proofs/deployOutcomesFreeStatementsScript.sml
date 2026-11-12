Theory deployOutcomesFreeStatements
Ancestors
  deployOutcomesFreeStmtLog deployOutcomesFreeStmtValues
  deployOutcomesFreeStmtControl deployOutcomesFreeTyping
  deployOutcomesFreeExprBody deployOutcomesFreeLowering stmtLowering
  e2eDeployDefs supportedStmtTraverse supportedExprTraverse exprLowering

Theorem outcomes_free_compile_reason_message:
  (!env ce ty e s. ~supported_expr_exists constructor_call_root e /\
     (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e s)))) /\
  (!bs n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_bytelike_literal bs n s)))) ==>
  !env ce e s. ~supported_expr_exists constructor_call_root e /\
    well_typed_expr env e /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_reason_message ce e s)))
Proof
  strip_tac >> gen_tac >> recInduct compile_reason_message_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_reason_message_def]
  >- (irule outcomes_free_bind >> simp[outcomes_free_return]) >>
  metis_tac[]
QED

Theorem outcomes_free_compile_log_eval_all:
  (!env ce ty e s. ~supported_expr_exists constructor_call_root e /\
     (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e s)))) /\
  (!ce vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce vv s)))) /\
  (!ce ty op es s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_log_save_arg ce ty op es s)))) ==>
  !es env ce s. ~supported_exprs_exists constructor_call_root es /\
    EVERY (well_typed_expr env) es /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_eval_all ce es s)))
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, outcomes_free_return,
    supported_expr_exists_def] >> rpt strip_tac >>
  irule outcomes_free_bind >> reverse conj_tac
  >- (rpt strip_tac >> simp[lower_value_def] >>
      irule outcomes_free_bind >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[outcomes_free_return] >> metis_tac[]
QED
