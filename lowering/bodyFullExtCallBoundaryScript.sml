(* Source and compilation boundaries for the joint external-call stage. *)
Theory bodyFullExtCallBoundary
Ancestors
  exprSimExtCallCase loweringStateRelDefs vyperInterpreter vyperState
  fragExec exprLoweringProps compileEnv emitHelperProps pair

(* A valid input horizon rules out static-frame errors and the non-oracle
   source branch; neither fact may be assumed without the horizon guard. *)
Theorem extcall_call_source_boundary:
  !st0 ctx func cenv cx ret_type es sa s0 sp is_static
   addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
   calldata has_default default_op default_ty default_opt ee t H.
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp is_static
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  valid_horizon cx st0 H ee.storage_trace ==>
  frame_call_value cx value_opt = return value_opt /\
  ee.outcomes = SOME t.vs_outcomes /\
  ~cx.txn.is_static /\ ~t.vs_call_ctx.cc_static /\
  (is_static <=> IS_NONE value_opt)
Proof
  rpt gen_tac >> strip_tac >>
  fs[extcall_request_ready_def] >>
  first_x_assum drule >> strip_tac >>
  fs[stmt_state_rel_def, state_rel_def] >>
  simp[frame_call_value_def] >>
  Cases_on `value_opt` >> gvs[]
QED

(* Expose each compiler action without unfolding instruction emission. *)
Theorem extcall_call_layout:
  !ret_type skip addr_op is_static gas_op call_offset call_len buf_op cap
   value_op sp u sr.
  comp_ignore_bind
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
     else comp_return ())
    (comp_bind
      (if is_static then emit_op STATICCALL
         [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
       else emit_op CALL
         [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind
         (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
         (new_block cont_lbl)))))))))) sp = (u,sr) ==>
  ?s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 success fail_lbl cont_lbl rds fail_buf old_lbl.
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
     else comp_return ()) sp = ((),s1) /\
    emit_op (if is_static then STATICCALL else CALL)
      (if is_static then
         [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
       else
         [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)])
      s1 = (success,s2) /\
    fresh_label "extcall_fail" s2 = (fail_lbl,s3) /\
    fresh_label "extcall_cont" s3 = (cont_lbl,s4) /\
    emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [] s4 = ((),s5) /\
    new_block fail_lbl s5 = (old_lbl,s6) /\
    emit_op RETURNDATASIZE [] s6 = (rds,s7) /\
    compile_alloc_buffer 0 s7 = (fail_buf,s8) /\
    emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds] s8 = ((),s9) /\
    emit_inst REVERT [fail_buf.buf_operand; rds] [] s9 = ((),s10) /\
    new_block cont_lbl s10 = (u,sr)
Proof
  rpt gen_tac >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  rpt (pure_once_rewrite_tac[comp_bind_def] >>
       pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[]) >>
  strip_tac >> gvs[new_block_def] >>
  rename1 `if stat then STATICCALL else CALL` >>
  Cases_on `stat` >> gvs[] >> metis_tac[]
QED

(* Split the optional prefix even when the code-size check is present. *)
Theorem extcall_check_code_split:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
   else comp_return ()) sp = ((),s1) /\
  cs_extends s1 sr /\ fn_has_code sp sr func ==>
  ci_mono sp s1 /\ fn_has_code sp s1 func /\ fn_has_code s1 sr func
Proof
  strip_tac >>
  `ci_mono sp s1` by
    (Cases_on `ret_type = NoneT /\ ~skip` >> gvs[]
     >- (qsuff_tac `ci_mono sp (SND (compile_extcodesize_check addr_op sp))`
         >- simp[] >>
         simp[NoAsms, exprLoweringTheory.compile_extcodesize_check_def] >>
         irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
     gvs[comp_return_def, ci_mono_refl]) >>
  metis_tac[fn_has_code_split, ci_mono_def]
QED

(* The suffix equations from extcall_call_layout supply every local code
   interval, including intervals crossing the failure and continuation blocks. *)
Theorem extcall_suffix_code:
  emit_op opc args s1 = (success,s2) /\
  fresh_label "extcall_fail" s2 = (fail_lbl,s3) /\
  fresh_label "extcall_cont" s3 = (cont_lbl,s4) /\
  emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [] s4 = ((),s5) /\
  new_block fail_lbl s5 = (old_lbl,s6) /\
  emit_op RETURNDATASIZE [] s6 = (rds,s7) /\
  compile_alloc_buffer 0 s7 = (fail_buf,s8) /\
  emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds] s8 = ((),s9) /\
  emit_inst REVERT [fail_buf.buf_operand; rds] [] s9 = ((),s10) /\
  new_block cont_lbl s10 = (u,sr) ==>
  cs_extends s1 sr /\
  (fn_has_code s1 sr func ==>
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  fn_has_code s3 s4 func /\ fn_has_code s4 s5 func /\
  fn_has_code s5 s6 func /\ fn_has_code s6 s7 func /\
  fn_has_code s7 s8 func /\ fn_has_code s8 s9 func /\
  fn_has_code s9 s10 func /\ fn_has_code s10 sr func)
Proof
  strip_tac >>
  `ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
   ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10 /\ ci_mono s10 sr` by
    (rpt conj_tac >>
     metis_tac[ci_mono_emit_op, ci_mono_fresh_label, ci_mono_emit_inst,
       ci_mono_new_block, ci_mono_compile_alloc_buffer, ci_mono_emit_void, SND]) >>
  fs[ci_mono_def] >>
  `cs_extends s9 sr` by metis_tac[cs_extends_trans] >>
  `cs_extends s8 sr` by metis_tac[cs_extends_trans] >>
  `cs_extends s7 sr` by metis_tac[cs_extends_trans] >>
  `cs_extends s6 sr` by metis_tac[cs_extends_trans] >>
  `cs_extends s5 sr` by metis_tac[cs_extends_trans] >>
  `cs_extends s4 sr` by metis_tac[cs_extends_trans] >>
  `cs_extends s3 sr` by metis_tac[cs_extends_trans] >>
  `cs_extends s2 sr` by metis_tac[cs_extends_trans] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  strip_tac >> rpt conj_tac >> metis_tac[cs_extends_trans, fn_has_code_split]
QED

Theorem extcall_call_fresh_outputs:
  emit_op opc args s1 = (success,s2) /\
  fresh_label "extcall_fail" s2 = (fail_lbl,s3) /\
  fresh_label "extcall_cont" s3 = (cont_lbl,s4) /\
  emit_op RETURNDATASIZE [] s6 = (rds,s7) ==>
  (?x. success = Var x /\ ~not_fresh_at s1 x) /\
  (?x. rds = Var x /\ ~not_fresh_at s6 x) /\
  fail_lbl <> cont_lbl /\
  fail_lbl = fresh_label_output "extcall_fail" s2.cs_next_label /\
  cont_lbl = fresh_label_output "extcall_cont" (s2.cs_next_label + 1) /\
  s4.cs_next_label = s2.cs_next_label + 2
Proof
  strip_tac >>
  qpat_x_assum `emit_op opc args s1 = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_x_assum `emit_op RETURNDATASIZE _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  gvs[compileEnvTheory.fresh_label_def] >>
  simp[not_fresh_at_def] >>
  strip_tac >> drule fresh_label_output_inj >> simp[]
QED
