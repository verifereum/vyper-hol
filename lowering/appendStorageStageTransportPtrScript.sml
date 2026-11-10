(* Actual-state transport of ordinary runs; pointer certificates are applied
   only after transport, never transported by vars_ext. *)
Theory appendStorageStageTransportPtr
Ancestors appendStorageStageRuns stmtAppendStorageSuffixPtr stmtAppendStorageGuardPtr
  varsExt freshWrites
  stateFrame venomState venomInst finite_map exprLoweringProps emitHelperProps
  venomExecSemantics compileEnv loweringStateRelDefs venomInstProps

Theorem run_inst_seq_vars_ext_ok:
  vars_ext s s' /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             ~is_ext_call_op i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  ?t'. run_inst_seq code s' = OK t' /\ vars_ext t t'
Proof
  strip_tac >> drule_all run_inst_seq_vars_ext >>
  simp[vars_ext_result_def]
QED

Theorem run_inst_seq_vars_ext_abort:
  vars_ext s s' /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             ~is_ext_call_op i.inst_opcode) code /\
  run_inst_seq code s = Abort a t ==>
  ?t'. run_inst_seq code s' = Abort a t' /\ vars_ext t t'
Proof
  strip_tac >> drule_all run_inst_seq_vars_ext >>
  simp[vars_ext_result_def]
QED

Theorem vars_ext_state_frame:
  vars_ext s t ==> state_frame t = state_frame s
Proof
  simp[vars_ext_def] >> strip_tac >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac [th]) >>
  simp[state_frame_vars]
QED

Theorem vars_ext_eval_operand:
  vars_ext s t /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp[vars_ext_def] >> strip_tac >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac [th]) >>
  metis_tac[eval_operand_vars_ext, optionTheory.NOT_NONE_SOME]
QED

Theorem append_storage_check_stages_actual:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  eval_operand bop s = SOME slot /\
  (!x. bop = Var x ==> not_fresh_at st0 x) /\ cap < dimword (:256) ==>
  ?s1 s2.
    run_inst_seq (emitted_insts st0 st1) s = OK s1 /\
    run_inst_seq (emitted_insts st1 st2) s1 = OK s2 /\
    state_frame s1 = state_frame s /\ state_frame s2 = state_frame s1 /\
    eval_operand lop s2 = SOME (if tr then tload slot s else sload slot s) /\
    eval_operand valid s2 =
      SOME (bool_to_word (w2n (if tr then tload slot s else sload slot s) < cap))
Proof
  strip_tac >>
  `eval_operand bop (drop_fresh st0 s) = SOME slot` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt st0 (drop_fresh st0 s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all append_storage_check_stages >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) (drop_fresh st0 s) = OK u1` >>
  rename1 `run_inst_seq (emitted_insts st1 st2) u1 = OK u2` >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st0 st1) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st1 st2)` by
    (imp_res_tac emitted_insts_emit_op >> Cases_on `tr` >>
     gvs[mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  `vars_ext (drop_fresh st0 s) s` by simp[vars_ext_drop_fresh] >>
  `?s1. run_inst_seq (emitted_insts st0 st1) s = OK s1 /\ vars_ext u1 s1` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  `?s2. run_inst_seq (emitted_insts st1 st2) s1 = OK s2 /\ vars_ext u2 s2` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  `tload slot (drop_fresh st0 s) = tload slot s /\
   sload slot (drop_fresh st0 s) = sload slot s` by
    simp[drop_fresh_def, tload_def, sload_def, contract_transient_def,
         contract_storage_def] >>
  `state_frame (drop_fresh st0 s) = state_frame s` by
    metis_tac[vars_ext_drop_fresh, vars_ext_state_frame] >>
  imp_res_tac vars_ext_state_frame >>
  qexistsl_tac [`s1`, `s2`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (irule vars_ext_eval_operand >> qexists_tac `u2` >> simp[]) >>
  irule vars_ext_eval_operand >> qexists_tac `u2` >> simp[]
QED

Theorem run_inst_seq_non_output_vars:
  !code s t x.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~MEM x i.inst_outputs) code /\
    run_inst_seq code s = OK t ==>
    lookup_var x t = lookup_var x s
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `lookup_var x u = lookup_var x s` by
    metis_tac[step_preserves_non_output_vars] >>
  first_x_assum drule_all >> simp[]
QED

Theorem emit_op_old_lookup:
  emit_op opc ops st = (rop,st') /\
  ~is_terminator opc /\ opc <> INVOKE /\
  run_inst_seq (emitted_insts st st') s = OK t /\ not_fresh_at st x ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> irule run_inst_seq_non_output_vars >>
  qexists_tac `emitted_insts st st'` >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[mk_inst_def] >> gvs[not_fresh_at_def]
QED

Theorem emit_void_old_lookup:
  emit_void opc ops st = ((),st') /\
  ~is_terminator opc /\ opc <> INVOKE /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> irule run_inst_seq_non_output_vars >>
  qexists_tac `emitted_insts st st'` >> simp[] >>
  drule emitted_insts_emit_void >> simp[mk_inst_def]
QED

Theorem emit_append_assert_actual:
  emit_void ASSERT [valid] st = ((),st') /\
  eval_operand valid s = SOME (bool_to_word T) ==>
  run_inst_seq (emitted_insts st st') s = OK s
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, assert_ok, bool_to_word_def]
QED

Theorem append_storage_guard_actual:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand bop s = SOME slot /\
  (!x. bop = Var x ==> not_fresh_at st0 x) /\ cap < dimword (:256) /\
  w2n (if tr then tload slot s else sload slot s) < cap /\
  op_taint tn bop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts st0 st3) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st0 st3)
           (s with vs_inst_idx := k) G' tn') /\
    state_frame t = state_frame s /\
    eval_operand lop t = SOME (if tr then tload slot s else sload slot s) /\
    op_taint tn' lop = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st0 x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!x. not_fresh_at st0 x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all append_storage_check_stages_actual >> strip_tac >>
  `run_inst_seq (emitted_insts st2 st3) s2 = OK s2` by
    (irule emit_append_assert_actual >> qexists_tac `valid` >> simp[]) >>
  `state_frame s2 = state_frame s2` by simp[] >>
  drule_all append_storage_guard_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st0 st2) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `st1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st0 st3) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s2`, `st2`] >>
     simp[] >> metis_tac[inst_extends_trans]) >>
  qexistsl_tac [`s2`, `G2`, `tn2`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  simp[] >> rpt strip_tac >>
  `st0.cs_next_var <= st1.cs_next_var` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[]) >>
  `not_fresh_at st1 x` by metis_tac[not_fresh_at_mono] >>
  `~is_terminator (if tr then TLOAD else SLOAD) /\
   (if tr then TLOAD else SLOAD) <> INVOKE /\
   ~is_terminator LT /\ LT <> INVOKE` by
    (Cases_on `tr` >> simp[is_terminator_def]) >>
  `lookup_var x s1 = lookup_var x s` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _`
       (mp_then Any mp_tac emit_op_old_lookup) >>
     disch_then drule_all >> simp[]) >>
  `lookup_var x s2 = lookup_var x s1` by
    (qpat_assum `emit_op LT _ _ = _`
       (mp_then Any mp_tac emit_op_old_lookup) >>
     disch_then drule_all >> simp[]) >> simp[]
QED

Theorem append_storage_guard_abort_actual:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand bop s = SOME slot /\
  (!x. bop = Var x ==> not_fresh_at st0 x) /\ cap < dimword (:256) /\
  ~(w2n (if tr then tload slot s else sload slot s) < cap) /\
  op_taint tn bop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts st0 st3) s = Abort Revert_abort t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st0 st3)
           (s with vs_inst_idx := k) G' tn') /\
    op_taint tn' lop = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st0 x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all append_storage_check_stages_actual >> strip_tac >>
  `run_inst_seq (emitted_insts st2 st3) s2 =
     Abort Revert_abort (revert_state (set_returndata [] s2))` by
    (irule append_storage_assert_abort_stage >>
     qexistsl_tac [`F`, `valid`] >> simp[]) >>
  drule_all append_storage_guard_abort_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st0 st2) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `st1`] >> simp[]) >>
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st0 st3) s =
     Abort Revert_abort (revert_state (set_returndata [] s2))` by
    metis_tac[run_inst_seq_emit_extend] >>
  qexistsl_tac [`revert_state (set_returndata [] s2)`, `G2`, `tn2`] >> simp[]
QED

Theorem append_storage_address_stages_actual:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop s3 = SOME slot /\ eval_operand lop s3 = SOME len /\
  (!x. bop = Var x ==> not_fresh_at st3 x) /\
  (!x. lop = Var x ==> not_fresh_at st3 x) ==>
  ?s4 s5 s6.
    run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\
    run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\
    run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\
    state_frame s4 = state_frame s3 /\ state_frame s5 = state_frame s4 /\
    state_frame s6 = state_frame s5 /\
    eval_operand pop s6 = SOME (slot+1w+len)
Proof
  strip_tac >>
  `eval_operand bop (drop_fresh st3 s3) = SOME slot /\
   eval_operand lop (drop_fresh st3 s3) = SOME len` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt st3 (drop_fresh st3 s3)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all append_storage_address_stages >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st4) (drop_fresh st3 s3) = OK u4` >>
  rename1 `run_inst_seq (emitted_insts st4 st5) u4 = OK u5` >>
  rename1 `run_inst_seq (emitted_insts st5 st6) u5 = OK u6` >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st3 st4) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st4 st5) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st5 st6)` by
    (imp_res_tac emitted_insts_emit_op >>
     gvs[mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  `vars_ext (drop_fresh st3 s3) s3` by simp[vars_ext_drop_fresh] >>
  `?s4. run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\ vars_ext u4 s4` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  `?s5. run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\ vars_ext u5 s5` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  `?s6. run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\ vars_ext u6 s6` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  imp_res_tac vars_ext_state_frame >>
  qexistsl_tac [`s4`, `s5`, `s6`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  irule vars_ext_eval_operand >> qexists_tac `u6` >> simp[]
QED

Theorem writes_fresh_old_operand:
  writes_fresh st code /\ run_inst_seq code s = OK t /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >> drule_all run_inst_seq_writes_fresh >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >>
  gvs[venom_state_component_equality]
QED

Theorem append_storage_store_tail_stages_actual:
  emit_void (if tr then TSTORE else SSTORE) [pop; vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop; nop] st8 = ((),st9) /\
  eval_operand pop s6 = SOME addr /\ eval_operand vop s6 = SOME w /\
  eval_operand lop s6 = SOME len /\ eval_operand bop s6 = SOME slot /\
  (!x. pop = Var x \/ vop = Var x \/ lop = Var x \/ bop = Var x ==>
       not_fresh_at st6 x) /\ ~s6.vs_call_ctx.cc_static ==>
  ?s7 s8 s9.
    run_inst_seq (emitted_insts st6 st7) s6 = OK s7 /\
    run_inst_seq (emitted_insts st7 st8) s7 = OK s8 /\
    run_inst_seq (emitted_insts st8 st9) s8 = OK s9 /\
    state_frame s8 = state_frame s7 /\
    s7.vs_allocas = s6.vs_allocas /\ s7.vs_fmp = s6.vs_fmp /\
    s7.vs_requests = s6.vs_requests /\
    s9.vs_allocas = s8.vs_allocas /\ s9.vs_fmp = s8.vs_fmp /\
    s9.vs_requests = s8.vs_requests /\ eval_operand bop s8 = SOME slot /\
    state_frame s9 = state_frame
      (if tr then tstore slot (len+1w) (tstore addr w s6)
       else sstore slot (len+1w) (sstore addr w s6))
Proof
  strip_tac >>
  `eval_operand pop (drop_fresh st6 s6) = SOME addr /\
   eval_operand vop (drop_fresh st6 s6) = SOME w /\
   eval_operand lop (drop_fresh st6 s6) = SOME len /\
   eval_operand bop (drop_fresh st6 s6) = SOME slot` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt st6 (drop_fresh st6 s6) /\
   ~(drop_fresh st6 s6).vs_call_ctx.cc_static` by
    simp[fresh_vars_wrt_drop_fresh, drop_fresh_def] >>
  drule_all append_storage_store_tail_stages >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st6 st7) (drop_fresh st6 s6) = OK u7` >>
  rename1 `run_inst_seq (emitted_insts st7 st8) u7 = OK u8` >>
  rename1 `run_inst_seq (emitted_insts st8 st9) u8 = OK u9` >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st6 st7) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st7 st8) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts st8 st9)` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     Cases_on `tr` >> gvs[mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  `vars_ext (drop_fresh st6 s6) s6` by simp[vars_ext_drop_fresh] >>
  `?s7. run_inst_seq (emitted_insts st6 st7) s6 = OK s7 /\ vars_ext u7 s7` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  `?s8. run_inst_seq (emitted_insts st7 st8) s7 = OK s8 /\ vars_ext u8 s8` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  `?s9. run_inst_seq (emitted_insts st8 st9) s8 = OK s9 /\ vars_ext u9 s9` by
    (irule run_inst_seq_vars_ext_ok >> metis_tac[]) >>
  suspend "post"
QED

Resume append_storage_store_tail_stages_actual[post]:
  imp_res_tac vars_ext_state_frame >>
  `state_frame s8 = state_frame s7` by metis_tac[] >>
  `eval_operand bop s8 = SOME slot` by
    (irule vars_ext_eval_operand >> qexists_tac `u8` >> simp[]) >>
  qexistsl_tac [`s7`, `s8`, `s9`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `tr` >>
  gvs[state_frame_def, venom_state_component_equality, drop_fresh_def,
      tstore_def, sstore_def, LET_THM]
QED

Finalise append_storage_store_tail_stages_actual

Theorem append_storage_address_writes_fresh:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) ==>
  writes_fresh st3 (emitted_insts st3 st6)
Proof
  strip_tac >> imp_res_tac inst_extends_emit_op >>
  `inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `emitted_insts st3 st6 = emitted_insts st3 st5 ++ emitted_insts st5 st6 /\
   emitted_insts st3 st5 = emitted_insts st3 st4 ++ emitted_insts st4 st5` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  asm_rewrite_tac[writes_fresh_append] >>
  imp_res_tac emitted_insts_emit_op >>
  simp[writes_fresh_def, fresh_write_op_def, mk_inst_def, not_fresh_at_def] >>
  decide_tac
QED

Theorem append_storage_address_run_actual:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop s3 = SOME slot /\ eval_operand lop s3 = SOME len /\
  (!x. bop = Var x ==> not_fresh_at st3 x) /\
  (!x. lop = Var x ==> not_fresh_at st3 x) ==>
  ?s4 s5 s6.
    run_inst_seq (emitted_insts st3 st4) s3 = OK s4 /\
    run_inst_seq (emitted_insts st4 st5) s4 = OK s5 /\
    run_inst_seq (emitted_insts st5 st6) s5 = OK s6 /\
    state_frame s4 = state_frame s3 /\ state_frame s5 = state_frame s4 /\
    state_frame s6 = state_frame s5 /\
    eval_operand pop s6 = SOME (slot+1w+len) /\
    run_inst_seq (emitted_insts st3 st6) s3 = OK s6 /\
    (!x. not_fresh_at st3 x ==> FLOOKUP s6.vs_vars x = FLOOKUP s3.vs_vars x) /\
    (!op. (!x. op = Var x ==> not_fresh_at st3 x) ==>
          eval_operand op s6 = eval_operand op s3)
Proof
  strip_tac >> drule_all append_storage_address_stages_actual >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st3 st5) s3 = OK s5` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s4`, `st4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st6) s3 = OK s6` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s5`, `st5`] >> simp[]) >>
  drule_all append_storage_address_writes_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  qexistsl_tac [`s4`, `s5`, `s6`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> rpt strip_tac >> irule writes_fresh_old_operand >> metis_tac[]
QED


Theorem append_storage_suffix_actual:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  emit_void (if tr then TSTORE else SSTORE) [pop;vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] st8 = ((),st9) /\
  eval_operand bop s3 = SOME slot /\ eval_operand lop s3 = SOME len /\
  eval_operand vop s3 = SOME w /\ ~s3.vs_call_ctx.cc_static /\
  op_taint tn bop = {} /\ op_taint tn lop = {} /\ op_taint tn vop = {} /\
  (!x. bop = Var x \/ lop = Var x \/ vop = Var x ==> not_fresh_at st3 x) /\
  ~ctx_has_dalloca ctx ==>
  ?t G9 tn9.
    run_inst_seq (emitted_insts st3 st9) s3 = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st3 st9)
           (s3 with vs_inst_idx := k) G9 tn9) /\
    state_frame t = state_frame
      (if tr then tstore slot (len+1w) (tstore (slot+1w+len) w s3)
       else sstore slot (len+1w) (sstore (slot+1w+len) w s3)) /\
    tn9.t_mem = tn.t_mem /\ tn9.t_imm = tn.t_imm /\
    (if tr then
       tn9.t_trans = key_update (key_update tn.t_trans (slot+1w+len) {}) slot {} /\
       tn9.t_stor = tn.t_stor
     else
       tn9.t_stor = key_update (key_update tn.t_stor (slot+1w+len) {}) slot {} /\
       tn9.t_trans = tn.t_trans) /\
    (!x. not_fresh_at st3 x ==>
         FLOOKUP G9 x = FLOOKUP G x /\
         op_taint tn9 (Var x) = op_taint tn (Var x)) /\
    (!x. not_fresh_at st3 x ==> lookup_var x t = lookup_var x s3)
Proof
  strip_tac >>
  `(!x. bop = Var x ==> not_fresh_at st3 x) /\
   (!x. lop = Var x ==> not_fresh_at st3 x)` by metis_tac[] >>
  drule_all append_storage_address_run_actual >> strip_tac >>
  `eval_operand bop s6 = SOME slot /\ eval_operand lop s6 = SOME len /\
   eval_operand vop s6 = SOME w` by metis_tac[] >>
  `state_frame s6 = state_frame s3` by metis_tac[] >>
  `~s6.vs_call_ctx.cc_static` by
    (qpat_assum `state_frame s6 = state_frame s3` mp_tac >>
     qpat_assum `~s3.vs_call_ctx.cc_static` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `st3.cs_next_var <= st6.cs_next_var` by
    (qpat_assum `emit_op ADD [bop; _] _ = _` mp_tac >>
     qpat_assum `emit_op MUL _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD [dop; off] _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emitted_insts_emit_op >> gvs[]) >>
  `!x. pop = Var x ==> not_fresh_at st6 x` by
    (qpat_assum `emit_op ADD [dop; off] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_op) >> simp[not_fresh_at_def]) >>
  `!x. pop = Var x \/ vop = Var x \/ lop = Var x \/ bop = Var x ==>
       not_fresh_at st6 x` by metis_tac[not_fresh_at_mono] >>
  drule_all append_storage_store_tail_stages_actual >> strip_tac >>
  drule_all append_storage_suffix_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume append_storage_suffix_actual[compose]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st3 st7 /\ inst_extends st3 st8 /\ inst_extends st3 st6` by
    metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st3 st7) s3 = OK s7` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s6`, `st6`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st8) s3 = OK s8` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s7`, `st7`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st9) s3 = OK s9` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s8`, `st8`] >> simp[]) >>
  qexistsl_tac [`s9`, `G9`, `tn9`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `state_frame s6 = state_frame s3` mp_tac >>
      qpat_assum `state_frame s9 = _` mp_tac >>
      rpt (pop_assum kall_tac) >> Cases_on `tr` >>
      simp[state_frame_def, venom_state_component_equality,
           tstore_def, sstore_def, LET_THM] >> metis_tac[]) >>
  simp[] >> suspend "old_vars"
QED

Resume append_storage_suffix_actual[old_vars]:
  rpt strip_tac >>
  `st3.cs_next_var <= st7.cs_next_var` by
    (qpat_assum `emit_op ADD [bop; _] _ = _` mp_tac >>
     qpat_assum `emit_op MUL _ _ = _` mp_tac >>
     qpat_assum `emit_op ADD [dop; off] _ = _` mp_tac >>
     qpat_assum `emit_void _ [pop; vop] _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >> gvs[]) >>
  `not_fresh_at st7 x` by metis_tac[not_fresh_at_mono] >>
  `~is_terminator (if tr then TSTORE else SSTORE) /\
   (if tr then TSTORE else SSTORE) <> INVOKE /\
   ~is_terminator ADD /\ ADD <> INVOKE` by
    (Cases_on `tr` >> simp[is_terminator_def]) >>
  `lookup_var x s7 = lookup_var x s6` by
    (qpat_assum `emit_void _ [pop; vop] _ = _`
       (mp_then Any mp_tac emit_void_old_lookup) >>
     disch_then drule_all >> simp[]) >>
  `lookup_var x s8 = lookup_var x s7` by
    (qpat_assum `emit_op ADD [lop; _] st7 = _`
       (mp_then Any mp_tac emit_op_old_lookup) >>
     disch_then drule_all >> simp[]) >>
  `lookup_var x s9 = lookup_var x s8` by
    (qpat_assum `emit_void _ [bop; nop] _ = _`
       (mp_then Any mp_tac emit_void_old_lookup) >>
     disch_then drule_all >> simp[]) >>
  simp[lookup_var_def]
QED

Finalise append_storage_suffix_actual

