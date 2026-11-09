(* Zero-read reason encoder boundary, independent of expression simulation. *)
Theory bodyIntCallFamStmtExitReason
Ancestors
  stmtSimReason stmtSimReasonExpr stmtSimReasonStorage stmtSimReasonCode
  exprReasonOperand loweringPosts compileEnv context venomState venomExecSemantics

Theorem reason_encoder_abort_path:
  (reason_vv_ok vv \/ reason_storage_vv vv \/ reason_code_vv vv) /\
  compile_revert_with_reason ce vv mt ms sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  eval_operand (vv_operand vv) s = SOME a /\
  (ce.ce_is_ctor ==>
     immutable_base_zero ce s /\
     !x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac
  >- (gvs[reason_vv_ok_def] >>
      `vv_operand vv = op` by
        (Cases_on `vv` >> gvs[reason_vv_def, vv_operand_def, AllCaseEqs()]) >>
      irule compile_revert_reason_path >>
      simp[] >> qexistsl_tac [`ce`, `reason_ds op`] >>
      qexistsl_tac [`ms`, `mt`, `vv`, `op`, `sa`, `sb`] >> simp[] >>
      Cases_on `op` >>
      gvs[reason_ds_def, reason_operand_def, reason_known_def,
          eval_operand_def])
  >- (gvs[reason_storage_vv_def, vv_operand_def] >>
      irule compile_revert_storage_reason_path >>
      goal_assum (drule_at Any) >> simp[reason_storage_vv_def] >>
      metis_tac[]) >>
  gvs[reason_code_vv_def, vv_operand_def] >>
  irule compile_revert_code_reason_path >>
  goal_assum (drule_at Any) >> simp[reason_code_vv_def] >> metis_tac[]
QED
