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

Theorem append_storage_address_stages:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop s3 = SOME slot /\ eval_operand lop s3 = SOME len /\
  fresh_vars_wrt st3 s3 ==>
  ?s4 s5 s6.
    run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\
    run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\
    run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\
    state_frame s4 = state_frame s3 /\ state_frame s5 = state_frame s4 /\
    state_frame s6 = state_frame s5 /\
    fresh_vars_wrt st4 s4 /\ fresh_vars_wrt st5 s5 /\ fresh_vars_wrt st6 s6 /\
    eval_operand pop s6 = SOME (slot+1w+len) /\
    (!op w. eval_operand op s3 = SOME w ==> eval_operand op s4 = SOME w) /\
    (!op w. eval_operand op s4 = SOME w ==> eval_operand op s5 = SOME w) /\
    (!op w. eval_operand op s5 = SOME w ==> eval_operand op s6 = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit 1w) s3 = SOME 1w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st4) s3 = OK s4` >>
  `eval_operand lop s4 = SOME len /\ eval_operand (Lit 1w) s4 = SOME 1w` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 st5) s4 = OK s5` >>
  `eval_operand dop s5 = SOME (slot+1w)` by metis_tac[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st5 st6) s5 = OK s6` >>
  `state_frame s4 = state_frame s3` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st3 st4` >> simp[] >>
     qpat_assum `emit_op ADD [bop; _] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  `state_frame s5 = state_frame s4` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st4 st5` >> simp[] >>
     qpat_assum `emit_op MUL _ _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  `state_frame s6 = state_frame s5` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st5 st6` >> simp[] >>
     qpat_assum `emit_op ADD [dop; off] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  qexistsl_tac [`s4`, `s5`, `s6`] >>
  gvs[WORD_MULT_CLAUSES] >> metis_tac[]
QED

Theorem append_storage_store_tail_stages:
  emit_void (if tr then TSTORE else SSTORE) [pop; vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop; nop] st8 = ((),st9) /\
  eval_operand pop s6 = SOME addr /\ eval_operand vop s6 = SOME w /\
  eval_operand lop s6 = SOME len /\ eval_operand bop s6 = SOME slot /\
  fresh_vars_wrt st6 s6 /\ ~s6.vs_call_ctx.cc_static ==>
  ?s7 s8 s9.
    run_inst_seq (emitted_insts st6 st7) s6 = OK s7 /\
    run_inst_seq (emitted_insts st7 st8) s7 = OK s8 /\
    run_inst_seq (emitted_insts st8 st9) s8 = OK s9 /\
    s7 = (if tr then tstore addr w s6 else sstore addr w s6) /\
    state_frame s8 = state_frame s7 /\
    s9 = (if tr then tstore slot (len+1w) s8 else sstore slot (len+1w) s8) /\
    fresh_vars_wrt st7 s7 /\ fresh_vars_wrt st8 s8 /\ fresh_vars_wrt st9 s9 /\
    eval_operand bop s8 = SOME slot /\
    (!op x. eval_operand op s6 = SOME x ==> eval_operand op s7 = SOME x) /\
    (!op x. eval_operand op s7 = SOME x ==> eval_operand op s8 = SOME x) /\
    (!op x. eval_operand op s8 = SOME x ==> eval_operand op s9 = SOME x)
Proof
  strip_tac >>
  qpat_assum `emit_void _ [pop; vop] _ = _`
    (mp_then Any mp_tac append_storage_store_run) >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `fresh_vars_wrt st7 s7` >>
  `eval_operand lop s7 = SOME len /\ eval_operand (Lit 1w) s7 = SOME 1w` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st7 st8) s7 = OK s8` >>
  `eval_operand bop s8 = SOME slot` by metis_tac[] >>
  `state_frame s8 = state_frame s7` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st7 st8` >> simp[] >>
     drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `~s8.vs_call_ctx.cc_static` by
    (qpat_x_assum `state_frame s8 = state_frame s7`
       (mp_tac o Q.AP_TERM `\x. x.vs_call_ctx`) >>
     qunabbrev_tac `s7` >> Cases_on `tr` >>
     simp[state_frame_def, sstore_def, tstore_def, LET_THM]) >>
  qpat_assum `emit_void _ [bop; nop] _ = _`
    (mp_then Any mp_tac append_storage_store_run) >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`s7`, `s8`,
    `if tr then tstore slot (len+1w) s8 else sstore slot (len+1w) s8`] >>
  metis_tac[]
QED

Theorem append_storage_suffix_stages:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  emit_void (if tr then TSTORE else SSTORE) [pop; vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop; nop] st8 = ((),st9) /\
  eval_operand bop s3 = SOME slot /\ eval_operand lop s3 = SOME len /\
  eval_operand vop s3 = SOME w /\ fresh_vars_wrt st3 s3 /\
  ~s3.vs_call_ctx.cc_static ==>
  ?s4 s5 s6 s7 s8 s9.
    run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\
    run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\
    run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\
    run_inst_seq (emitted_insts st6 st7) s6 = OK s7 /\
    run_inst_seq (emitted_insts st7 st8) s7 = OK s8 /\
    run_inst_seq (emitted_insts st8 st9) s8 = OK s9 /\
    state_frame s4 = state_frame s3 /\ state_frame s5 = state_frame s4 /\
    state_frame s6 = state_frame s5 /\ state_frame s8 = state_frame s7 /\
    s7.vs_allocas = s6.vs_allocas /\ s7.vs_fmp = s6.vs_fmp /\
    s7.vs_requests = s6.vs_requests /\
    s9.vs_allocas = s8.vs_allocas /\ s9.vs_fmp = s8.vs_fmp /\
    s9.vs_requests = s8.vs_requests /\
    fresh_vars_wrt st4 s4 /\ fresh_vars_wrt st5 s5 /\ fresh_vars_wrt st6 s6 /\
    fresh_vars_wrt st7 s7 /\ fresh_vars_wrt st8 s8 /\ fresh_vars_wrt st9 s9 /\
    eval_operand pop s6 = SOME (slot+1w+len) /\ eval_operand bop s8 = SOME slot /\
    state_frame s9 = state_frame
      (if tr then tstore slot (len+1w) (tstore (slot+1w+len) w s3)
       else sstore slot (len+1w) (sstore (slot+1w+len) w s3)) /\
    (!op x. eval_operand op s3 = SOME x ==> eval_operand op s9 = SOME x)
Proof
  strip_tac >> drule_all append_storage_address_stages >> strip_tac >>
  `eval_operand bop s6 = SOME slot /\ eval_operand lop s6 = SOME len /\
   eval_operand vop s6 = SOME w` by metis_tac[] >>
  `state_frame s6 = state_frame s3` by metis_tac[] >>
  `~s6.vs_call_ctx.cc_static` by
    fs[state_frame_def, venom_state_component_equality] >>
  drule_all append_storage_store_tail_stages >> strip_tac >>
  `state_frame s7 = state_frame
     (if tr then tstore (slot+1w+len) w s3 else sstore (slot+1w+len) w s3)` by
    (qpat_x_assum `s7 = _` (fn th => once_rewrite_tac [th]) >>
     irule append_storage_store_frame >> metis_tac[]) >>
  `state_frame s9 = state_frame
     (if tr then tstore slot (len+1w) (tstore (slot+1w+len) w s3)
      else sstore slot (len+1w) (sstore (slot+1w+len) w s3))` by
    (`state_frame s9 = state_frame
       (if tr then tstore slot (len+1w)
          (if tr then tstore (slot+1w+len) w s3 else sstore (slot+1w+len) w s3)
        else sstore slot (len+1w)
          (if tr then tstore (slot+1w+len) w s3 else sstore (slot+1w+len) w s3))` by
       (qpat_assum `s9 = _` (fn th => once_rewrite_tac [th]) >>
        irule append_storage_store_frame >> metis_tac[]) >>
     Cases_on `tr` >> gvs[]) >>
  `s7.vs_allocas = s6.vs_allocas /\ s7.vs_fmp = s6.vs_fmp /\
   s7.vs_requests = s6.vs_requests /\
   s9.vs_allocas = s8.vs_allocas /\ s9.vs_fmp = s8.vs_fmp /\
   s9.vs_requests = s8.vs_requests` by
    (qpat_x_assum `s7 = _` SUBST1_TAC >>
     qpat_x_assum `s9 = _` SUBST1_TAC >>
     Cases_on `tr` >> simp[sstore_def, tstore_def, LET_THM]) >>
  qpat_x_assum `s7 = _` kall_tac >>
  qpat_x_assum `s9 = _` kall_tac >>
  qexistsl_tac [`s4`, `s5`, `s6`, `s7`, `s8`, `s9`] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  ntac 6 (first_x_assum irule) >> first_assum ACCEPT_TAC
QED
