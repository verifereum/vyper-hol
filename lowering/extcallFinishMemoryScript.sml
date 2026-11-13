(* The actual success jump and failure copy after the oracle call. *)
Theory extcallFinishMemory
Ancestors
  extcallCallMemory rawCallFinishPathMemory
  exprSimExtCallCase exprLoweringProps emitHelperProps fragGasPathMem fragExec
  allocaHistory compileEnv venomState venomExecSemantics words list

Theorem extcall_returned_branch_mem:
  fresh_label "extcall_fail" sc = (fail_lbl,s1) /\
  fresh_label "extcall_cont" s1 = (cont,s2) /\
  emit_inst JNZ [ok;Label cont;Label fail_lbl] [] s2 = ((),sj) /\
  new_block fail_lbl sj = (old,sf) /\
  emit_op RETURNDATASIZE [] sf = (rds,s3) /\
  compile_alloc_buffer 0 s3 = (fb,s4) /\
  emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds] s4 = ((),s5) /\
  emit_inst REVERT [fb.buf_operand;rds] [] s5 = ((),se) /\
  new_block cont se = (u,sr) /\ fn_has_code sc sr func /\
  extcall_returned ctx func ce cx rt es sa s0 sc addr buf cap target
    has def dt opt data ee s /\ alloca_history func s /\
  eval_operand ok s = SOME (bool_to_word success) ==>
  ?r. gas_path_mem ctx func s 0 r /\
    ((?t. r = OK t /\ success /\ alloca_history func t /\
       extcall_returned ctx func ce cx rt es sa s0 sr addr buf cap target
         has def dt opt data ee t) \/
     (?t. r = Abort Revert_abort t /\ ~success /\ t.vs_returndata = data))
Proof
  strip_tac >>
  `ci_mono sc s1 /\ ci_mono s1 s2 /\ ci_mono s2 sj /\
   ci_mono sj sf /\ ci_mono sf s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 se /\ ci_mono se sr` by
    (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
      ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
      ci_mono_emit_void, pairTheory.SND]) >>
  `ci_mono sc sr /\ cs_extends sf se /\ cs_extends sc s2 /\ cs_extends s2 sr` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s2 sr func` by metis_tac[fn_has_code_split] >>
  `s2.cs_current_bb = sc.cs_current_bb /\
   s2.cs_current_insts = sc.cs_current_insts` by
    metis_tac[fresh_label_props] >>
  `sr.cs_current_bb = cont /\ sr.cs_current_insts = []` by
    (qpat_x_assum `new_block cont _ = _` mp_tac >> simp[new_block_def] >>
     strip_tac >> gvs[]) >>
  suspend "branch"
QED

Resume extcall_returned_branch_mem[branch]:
  `bool_to_word success = if success then 1w else 0w` by
    (Cases_on `success` >> simp[bool_to_word_def]) >>
  `extcall_returned ctx func ce cx rt es sa s0 sr addr buf cap target
    has def dt opt data ee (jump_to cont s)` by
    (irule extcall_returned_jump >> simp[] >> qexists_tac `sc` >>
     fs[ci_mono_def]) >>
  `alloca_history func (jump_to cont s)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `s` >> simp[]) >>
  `~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
   s.vs_inst_idx = LENGTH sc.cs_current_insts /\ s.vs_returndata = data /\
   LENGTH s.vs_returndata < dimword (:256)` by fs[extcall_returned_def] >>
  ho_match_mp_tac raw_call_finish_branch_guarded_mem >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst REVERT _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void RETURNDATACOPY _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  simp[cs_extends_refl] >> qexistsl_tac [`sr`,`success`] >>
  simp[cs_extends_refl] >> strip_tac >>
  qexists_tac `OK (jump_to cont s)` >> fs[gas_path_mem_rules, jump_to_def]
QED

Finalise extcall_returned_branch_mem

Theorem extcall_oracle_branch_mem:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;offset;len;buf;Lit (n2w cap)]
     else [gas;addr;value;offset;len;buf;Lit (n2w cap)]) sg = (ok,sc) /\
  fresh_label "extcall_fail" sc = (fail_lbl,s1) /\
  fresh_label "extcall_cont" s1 = (cont,s2) /\
  emit_inst JNZ [ok;Label cont;Label fail_lbl] [] s2 = ((),sj) /\
  new_block fail_lbl sj = (old,sf) /\
  emit_op RETURNDATASIZE [] sf = (rds,s3) /\
  compile_alloc_buffer 0 s3 = (fb,s4) /\
  emit_void RETURNDATACOPY [fb.buf_operand;Lit 0w;rds] s4 = ((),s5) /\
  emit_inst REVERT [fb.buf_operand;rds] [] s5 = ((),se) /\
  new_block cont se = (u,sr) /\ cs_extends sc sr /\
  fn_has_code sg sr func /\ fn_inst_ids_distinct func /\
  extcall_request_ready ctx func ce cx rt es sa s0 sg stat
    addr value gas buf offset len cap target vo data has def dt opt ee s /\
  alloca_history func s /\
  (!ao az. eval_operand offset s = SOME ao /\ eval_operand len s = SOME az ==>
    w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  take_call_outcome target data vo ee = (INL (rq,oc),ee1) ==>
  ?r. gas_path_mem ctx func s 0 r /\
    ((?t. r = OK t /\ oc.co_success /\ alloca_history func t /\
       extcall_returned ctx func ce cx rt es sa s0 sr addr buf cap target
         has def dt opt oc.co_returnData (SND (adopt_call_outcome rq oc ee1)) t) \/
     (?t. r = Abort Revert_abort t /\ ~oc.co_success /\
       t.vs_returndata = oc.co_returnData))
Proof
  strip_tac >>
  `ci_mono sg sc` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sg sc func /\ fn_has_code sc sr func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  drule_all extcall_oracle_returned_mem >>
  disch_then (qx_choose_then `z` strip_assume_tac) >>
  drule_all extcall_returned_branch_mem >>
  disch_then (qx_choose_then `r` strip_assume_tac) >>
  qexists_tac `r` >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD]
QED
