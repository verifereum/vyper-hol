(* Expose ordinary intermediate states for checked append certificates. *)
Theory appendStorageStageRuns
Ancestors stmtSimAppendStorage emitHelperProps exprLoweringProps venomInst
  venomState stateFrame words arithmetic venomExecSemantics

Theorem append_storage_load_stage:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  eval_operand bop s = SOME slot /\ fresh_vars_wrt st0 s ==>
  ?s1. run_inst_seq (emitted_insts st0 st1) s = OK s1 /\
    eval_operand lop s1 = SOME (if tr then tload slot s else sload slot s) /\
    fresh_vars_wrt st1 s1 /\ state_frame s1 = state_frame s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op s1 = SOME w)
Proof
  strip_tac >>
  `?s1. run_inst_seq (emitted_insts st0 st1) s = OK s1 /\
    eval_operand lop s1 = SOME (if tr then tload slot s else sload slot s) /\
    fresh_vars_wrt st1 s1 /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op s1 = SOME w)` by
    (reverse (Cases_on `tr`) >> gvs[]
     >- (drule_all emit_op_SLOAD_correct >> metis_tac[]) >>
     qspecl_then [`TLOAD`, `tload`] mp_tac emit_op_read1_correct >>
     disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[step_inst_base_def, exec_read1_def] >> strip_tac >>
     first_x_assum (qspecl_then [`slot`, `s`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `state_frame s1 = state_frame s` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st0 st1` >> simp[] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def] >>
     Cases_on `tr` >> simp[]) >>
  metis_tac[]
QED

Theorem append_storage_check_stages:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  eval_operand bop s = SOME slot /\ fresh_vars_wrt st0 s /\
  cap < dimword (:256) ==>
  ?s1 s2.
    run_inst_seq (emitted_insts st0 st1) s = OK s1 /\
    run_inst_seq (emitted_insts st1 st2) s1 = OK s2 /\
    state_frame s1 = state_frame s /\ state_frame s2 = state_frame s1 /\
    fresh_vars_wrt st1 s1 /\ fresh_vars_wrt st2 s2 /\
    eval_operand lop s2 = SOME (if tr then tload slot s else sload slot s) /\
    eval_operand valid s2 =
      SOME (bool_to_word (w2n (if tr then tload slot s else sload slot s) < cap)) /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op s1 = SOME w) /\
    (!op w. eval_operand op s1 = SOME w ==> eval_operand op s2 = SOME w)
Proof
  strip_tac >> drule_all append_storage_load_stage >> strip_tac >>
  `eval_operand (Lit (n2w cap)) s1 = SOME (n2w cap)` by
    simp[eval_operand_def] >>
  drule_all emit_op_LT_correct >> strip_tac >>
  `state_frame ss' = state_frame s1` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st1 st2` >> simp[] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  qexistsl_tac [`s1`, `ss'`] >>
  gvs[wordsTheory.w2n_n2w] >> metis_tac[]
QED

Theorem append_storage_assert_success_stage:
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand valid s2 = SOME (bool_to_word b) /\ b /\
  fresh_vars_wrt st2 s2 ==>
  run_inst_seq (emitted_insts st2 st3) s2 = OK s2 /\
  fresh_vars_wrt st3 s2
Proof
  strip_tac >> gvs[bool_to_word_def] >>
  `((1w:bytes32) <> 0w)` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[]
QED

Theorem append_storage_assert_abort_stage:
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand valid s2 = SOME (bool_to_word b) /\ ~b ==>
  run_inst_seq (emitted_insts st2 st3) s2 =
    Abort Revert_abort (revert_state (set_returndata [] s2))
Proof
  strip_tac >> gvs[bool_to_word_def] >>
  irule emit_void_ASSERT_revert_full >> metis_tac[]
QED
