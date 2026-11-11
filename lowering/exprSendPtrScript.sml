Theory exprSendPtr
Ancestors
  callStepPtr wordArgsPtr exprSimSend fragGasSeqPtr fragGasPathPtr stmtAssertPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomExecProofs
  venomInst venomInstProofs venomState opcodeClass memLocDefs codegenRel contextCodegenRel list
  venomCallOracleDefs venomMemProps ghostPcTransportPtr
  exprLoweringProps exprSimOperands exprSimWordArgs compileEnv loweringStateRelDefs localPtrsProps
  sendSourceFrame typedWordArgsSimPtr exprSimHypsDefs exprSimPrecompiles bodyPtrDefs fragExec
  gasSummaryComposePtr gasExemptCert gasSummaryCompose vyperState typedWordArgsFactsPtr
  typedWordArgsPostPtr exprStackPtr

Theorem ptr_inst_ok_assert:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME w ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSERT [op] []) s
Proof
  strip_tac >> drule step_assert_behavior >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mk_inst_def] >>
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  first_x_assum (qspec_then `id` mp_tac) >>
  Cases_on `w = 0w` >> gvs[]
QED

Theorem assert_ghost_unchanged:
  step_prov PG G (mk_inst id ASSERT [op] []) s = G /\
  step_taint (mk_inst id ASSERT [op] []) s s tn = tn
Proof
  simp[step_prov_def, step_taint_def, mk_inst_def, set_prov_def,
       set_var_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def] >>
  Cases_on `tn` >>
  simp[finite_mapTheory.DRESTRICT_UNIV, range_bytes_def,
       finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION,
       SF CONJ_ss] >>
  simp[taint_component_equality]
QED

Theorem assert_ok_path_ptr:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME w /\ w <> 0w /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSERT [op] []) s = OK s` by
    (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [op] []) s` by
    (irule ptr_inst_ok_assert >> metis_tac[]) >>
  `(mk_inst id ASSERT [op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id ASSERT [op] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, assert_ghost_unchanged] >>
  strip_tac >>
  `~(s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem assert_fail_path_ptr:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME 0w /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (Abort Revert_abort (revert_state (set_returndata [] s)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSERT [op] []) s =
     Abort Revert_abort (revert_state (set_returndata [] s))` by
    (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [op] []) s` by
    (irule ptr_inst_ok_assert >> metis_tac[]) >>
  `(mk_inst id ASSERT [op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id ASSERT [op] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all gas_path_ptr_abort >> simp[mk_inst_def, is_terminator_def]
QED

Theorem ptr_inst_ok_send_call:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\
  op_taint tn value = {} /\ ~ctx_has_dalloca ctx /\
  stor_taint_ok cx tn s ==>
  ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn inst s
Proof
  strip_tac >> irule ptr_inst_ok_call >> simp[allocas_from_def] >>
  gvs[bodyPtrDefsTheory.stor_taint_ok_def, bodyPtrDefsTheory.cx_dead_def] >>
  conj_tac
  >- (irule taint_ok_call >>
      gvs[op_taint_def, source_memory_read_ranges_def,
          mem_read_ops_def, memory_range_of_operands_def, eval_operand_def]) >>
  irule access_ok_call >> simp[eval_operand_def]
QED

Theorem send_call_step:
  ~s.vs_call_ctx.cc_static /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw ==>
  step_inst_base inst s =
    OK (update_var out
      (FST (consume_call_outcome (venom_call_request s aw vw 0w 0w F) 0 0 s))
      (SND (consume_call_outcome (venom_call_request s aw vw 0w 0w F) 0 0 s)))
Proof
  strip_tac >>
  simp[Once step_inst_base_def, eval_operand_def, Excl "consume_call_outcome_eq"] >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> simp[Excl "consume_call_outcome_eq"]
QED

Theorem send_call_runtime_frame:
  ~s.vs_call_ctx.cc_static /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u ==>
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_fmp = s.vs_fmp /\ u.vs_call_ctx = s.vs_call_ctx /\
  (!p. p <> out ==> lookup_var p u = lookup_var p s)
Proof
  strip_tac >> drule_all send_call_step >>
  gvs[Excl "consume_call_outcome_eq"] >>
  simp[consume_call_outcome_eq, write_memory_with_expansion_empty_0,
       update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem send_call_stor_taint:
  ~s.vs_call_ctx.cc_static /\ stor_taint_ok cx tn s /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u ==>
  stor_taint_ok cx (step_taint inst s u tn) u
Proof
  strip_tac >> drule_all send_call_runtime_frame >> strip_tac >>
  irule call_stor_taint_ok >> simp[] >> strip_tac >>
  drule_all send_call_step >> strip_tac >>
  gvs[update_var_def, Excl "consume_call_outcome_eq"] >>
  irule consume_call_no_reset_accounts >>
  simp[Excl "consume_call_outcome_eq"] >>
  qexistsl_tac [`0w`, `aw`, `0w`, `0`, `0`, `vw`] >> simp[]
QED

Theorem send_call_ghost_inv:
  ~s.vs_call_ctx.cc_static /\ ghost_inv d cenv cx es G tn s /\
  es'.scopes = es.scopes /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
  ghost_inv d cenv cx es' (step_prov PG G inst u) (step_taint inst s u tn) u
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by gvs[bodyPtrDefsTheory.ghost_inv_def] >>
  drule_all send_call_runtime_frame >> strip_tac >>
  `stor_taint_ok cx (step_taint inst s u tn) u` by
    (irule send_call_stor_taint >> metis_tac[]) >>
  `(step_taint inst s u tn).t_mem = tn.t_mem` by
    (irule call_zero_region_memory_taint >> metis_tac[]) >>
  irule call_ghost_inv >> metis_tac[]
QED

Theorem send_call_ghost_kept:
  ~s.vs_call_ctx.cc_static /\ ~not_fresh_at sa out /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u ==>
  ghost_kept cenv es sa G tn s (step_prov PG G inst u) (step_taint inst s u tn)
Proof
  strip_tac >> drule_all send_call_runtime_frame >> strip_tac >>
  irule call_ghost_kept >> metis_tac[]
QED

Theorem call_assert_ok_path_ptr:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; rz] /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst aid ASSERT [Var out] []) /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK u /\
  eval_operand (Var out) u = SOME w /\ w <> 0w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `op_taint (step_taint inst s u tn) (Var out) = {}` by
    metis_tac[call_output_untainted] >>
  `gas_path_ptr D 0 ctx fn PG (step_prov PG G inst u)
    (step_taint inst s u tn) (u with vs_inst_idx := SUC s.vs_inst_idx) 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (OK ((u with vs_inst_idx := SUC s.vs_inst_idx) with vs_inst_idx :=
      SUC (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx))` by
    (irule assert_ok_path_ptr >> simp[] >> metis_tac[]) >>
  fs[] >>
  `(inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)` by
    simp[is_terminator_def] >>
  drule_all gas_path_ptr_step >> simp[]
QED

Theorem call_assert_fail_path_ptr:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; rz] /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst aid ASSERT [Var out] []) /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK u /\ eval_operand (Var out) u = SOME 0w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (Abort Revert_abort (revert_state
      (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx))))
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `op_taint (step_taint inst s u tn) (Var out) = {}` by
    metis_tac[call_output_untainted] >>
  `gas_path_ptr D 0 ctx fn PG (step_prov PG G inst u)
    (step_taint inst s u tn) (u with vs_inst_idx := SUC s.vs_inst_idx) 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (Abort Revert_abort (revert_state
      (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx))))` by
    (irule assert_fail_path_ptr >> simp[] >> metis_tac[]) >>
  `(inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)` by
    simp[is_terminator_def] >>
  drule_all gas_path_ptr_step >> simp[]
QED

Theorem call_assert_code_lookup:
  emit_op CALL ops sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\ fn_has_code sm sb fn ==>
  ?out bb. success = Var out /\
    lookup_block sm.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sm.cs_current_insts) =
      SOME (mk_inst sm.cs_next_id CALL ops [out]) /\
    get_instruction bb (SUC (LENGTH sm.cs_current_insts)) =
      SOME (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] [])
Proof
  strip_tac >> drule_all send_tail_shape >> strip_tac >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  qexistsl_tac [`out`, `bb`] >> simp[] >>
  first_assum (qspec_then `0` mp_tac) >>
  first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]
QED

(* Read-result correspondence for any zero-region CALL, not just an emitted id. *)
Theorem send_read_call_step:
  stmt_state_rel ctx fn cenv cx es s /\
  outcomes_accounts_typed es.outcomes /\ accounts_runtime_well_typed es.accounts /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  IS_SOME (eval_operand gas s) /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es = (res, es') ==>
  ?s'. s' = s with <| vs_outcomes := s'.vs_outcomes;
                      vs_requests := s'.vs_requests;
                      vs_accounts := s'.vs_accounts;
                      vs_transient := s'.vs_transient;
                      vs_logs := s'.vs_logs;
                      vs_pending_deletions := s'.vs_pending_deletions;
                      vs_returndata := s'.vs_returndata |> /\
    ((res = INL NoneV /\ step_inst_base inst s = OK (update_var out 1w s') /\
      state_rel fn cenv cx es' s') \/
     (res = INR (Error (RuntimeError "send failed")) /\
      step_inst_base inst s = OK (update_var out 0w s')))
Proof
  strip_tac >> drule eval_send_read >> strip_tac >>
  `state_rel fn cenv cx es s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `?os. es.outcomes = SOME os` by fs[loweringStateRelDefsTheory.state_rel_def] >>
  drule_all eval_send_outcome_typed >> strip_tac >>
  drule_all extCallOracleStepTheory.send_call_oracle_step >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem send_read_checked_tail:
  stmt_state_rel ctx fn cenv cx es s /\ stor_taint_ok cx tn s /\
  outcomes_accounts_typed es.outcomes /\ accounts_runtime_well_typed es.accounts /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst aid ASSERT [Var out] []) /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es = (res, es') ==>
  ?t u w.
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
                  vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
                  vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
                  vs_returndata := t.vs_returndata |> /\
    u = update_var out w t /\ step_inst_base inst s = OK u /\
    eval_operand (Var out) u = SOME w /\
    ((res = INL NoneV /\ w = 1w /\ state_rel fn cenv cx es' t /\
      gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0
        (step_prov PG G inst u) (step_taint inst s u tn)
        (OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)))) \/
     (res = INR (Error (RuntimeError "send failed")) /\ w = 0w /\
      gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0
        (step_prov PG G inst u) (step_taint inst s u tn)
        (Abort Revert_abort (revert_state
          (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx))))))
Proof
  strip_tac >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn inst s` by
    (irule ptr_inst_ok_send_call >> metis_tac[]) >>
  `IS_SOME (eval_operand gas s)` by simp[] >>
  `!w st. eval_operand (Var out) (update_var out w st) = SOME w` by
    simp[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  drule_all send_read_call_step >> strip_tac
  >- (qexistsl_tac [`s'`, `update_var out 1w s'`, `1w`] >> simp[] >>
      irule call_assert_ok_path_ptr >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`s'`, `update_var out 0w s'`, `0w`] >> simp[] >>
  irule call_assert_fail_path_ptr >> simp[] >> metis_tac[]
QED

Theorem send_tail_none_post:
  stmt_state_rel ctx fn cenv cx es1 s /\ wb_frame cenv es es1 sa s0 s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  ~not_fresh_at sm out /\ post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\
  es'.scopes = es1.scopes /\ es'.immutables = es1.immutables /\
  state_rel fn cenv cx es' t /\
  t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
                vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
                vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
                vs_returndata := t.vs_returndata |> ==>
  expr_post ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w)
    ((update_var out w t) with vs_inst_idx := k)
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp /\ t.vs_memory = s.vs_memory /\
   t.vs_vars = s.vs_vars /\ t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> conj_tac
      >- (irule fresh_not_local_ptr >> qexists_tac `sm` >> fs[]) >>
      `immutable_alloca_sep fn cenv cx es' t` by
        (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es1`] >>
         gvs[stmt_state_rel_def] >> rpt strip_tac >> qexists_tac `id` >>
         gvs[local_region_def, lookup_var_def]) >>
      `immutable_base_zero cenv t` by
        (irule immutable_base_zero_frame >> qexists_tac `s` >>
         fs[stmt_state_rel_def, lookup_var_def]) >>
      irule stmt_state_rel_allocas_frame >> simp[] >>
      qexistsl_tac [`es1`, `s`] >> simp[]) >>
  `wb_frame cenv es es' sa s0 s` by
    (qpat_x_assum `wb_frame cenv es es1 sa s0 s` mp_tac >>
     pure_rewrite_tac[loweringPostsTheory.wb_frame_def,
       loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
     qpat_x_assum `es'.scopes = es1.scopes` (fn th => pure_rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  irule wb_frame_readonly_tail >> qexists_tac `sm` >>
  qpat_assum `wb_frame cenv es es' sa s0 s` (irule_at Any) >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem send_tail_path_ptr:
  emit_op CALL [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (void, sb) /\ fn_has_code sm sb fn /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx fn cenv cx es1 s /\ wb_frame cenv es es1 sa s0 s /\
  ghost_inv d cenv cx es1 G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') /\ post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?G' tn' r. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' r /\
    ((?z. r = OK z /\ res = INL NoneV /\
          expr_post ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w) z /\
          ghost_inv d cenv cx es' G' tn' z /\
          ghost_kept cenv es sa G tn s G' tn' /\
          z.vs_current_bb = sb.cs_current_bb /\
          z.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r /\ expr_exit res r))
Proof
  strip_tac >> drule_all call_assert_code_lookup >> strip_tac >>
  drule_all send_tail_shape >> strip_tac >>
  `~not_fresh_at sm out /\ ~not_fresh_at sa out` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id CALL
    [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out]` >>
  `inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
   inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
   get_instruction bb s.vs_inst_idx = SOME inst /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[Abbr `inst`, mk_inst_def] >>
  `stor_taint_ok cx tn s` by fs[bodyPtrDefsTheory.ghost_inv_def] >>
  `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
    (drule eval_send_read >> strip_tac >>
     drule vyperCallOutcomeFrameTheory.eval_send_preserves_non_accounts >> simp[]) >>
  drule_all send_read_checked_tail >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_void _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `outcomes_accounts_typed _` kall_tac >>
  qpat_x_assum `accounts_runtime_well_typed _` kall_tac >>
  qpat_x_assum `LENGTH gas_vs = _` kall_tac >>
  qpat_x_assum `(do tv <- _; _ od) _ = _` kall_tac >>
  qpat_x_assum `_ = STRING _ _` kall_tac >>
  rpt (qpat_x_assum `get_instruction _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `lookup_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `op_taint _ _ = _` kall_tac) >>
  qpat_x_assum `dest_AddressV _ = _` kall_tac >>
  qpat_x_assum `dest_NumV _ = _` kall_tac >>
  qpat_x_assum `cs_extends _ _` kall_tac >>
  gvs[]
  >- suspend "normal"
  >> suspend "failed"
QED

Resume send_tail_path_ptr[normal]:
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `ghost_inv d cenv cx es' (step_prov PG G inst u)
     (step_taint inst s u tn) u` by
    (irule send_call_ghost_inv >> simp[] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `ghost_kept cenv es sa G tn s (step_prov PG G inst u)
     (step_taint inst s u tn)` by
    (irule send_call_ghost_kept >> metis_tac[]) >>
  `ghost_inv d cenv cx es' (step_prov PG G inst u)
     (step_taint inst s u tn)
     (u with <| vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
                vs_inst_idx := SUC (SUC s.vs_inst_idx) |>)` by
    simp[stmtFragPtrTheory.ghost_inv_jump_to] >>
  `(u with <| vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb;
               vs_inst_idx := SUC (SUC s.vs_inst_idx) |>) =
   (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    simp[venom_state_component_equality] >>
  fs[] >>
  qexistsl_tac [`step_prov PG G inst u`, `step_taint inst s u tn`,
                `OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))`] >>
  simp[] >> conj_tac
  >- (simp[Abbr `u`] >> irule send_tail_none_post >> simp[] >>
      conj_tac >- (qexists_tac `sm` >> simp[]) >>
      qexistsl_tac [`es1`, `s`] >> simp[]) >>
  `t.vs_current_bb = sm.cs_current_bb` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[Abbr `u`, update_var_def, arithmeticTheory.ADD1]
QED

Resume send_tail_path_ptr[failed]:
  goal_assum (drule_at Any) >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Finalise send_tail_path_ptr

Theorem send_tail_summary_ptr:
  emit_op CALL [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (void, sb) /\ fn_has_code sm sb fn /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx fn cenv cx es1 s /\ wb_frame cenv es es1 sa s0 s /\
  ghost_inv d cenv cx es1 G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\ es1.gas_obs = [] ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs); read_result cx tv od)
    (es1,s,G,tn)
    (\res ee G' tn' z. res = INL NoneV /\
      expr_post ctx fn cenv cx e es sa sb s0 ee NoneV (Lit 0w) z /\
      ghost_inv d cenv cx ee G' tn' z /\
      ghost_kept cenv es sa G tn s G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee ghosts r. expr_exit res r)
Proof
  strip_tac >>
  qabbrev_tac `src = do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
                       read_result cx tv od` >>
  Cases_on `src es1` >> rename1 `src es1 = (res,ee)` >>
  `ee.gas_obs = es1.gas_obs /\
   !gs. src (es1 with gas_obs := gs) = (res,ee with gas_obs := gs)` by
    (fs[Abbr `src`, SF ETA_ss] >>
     qspec_then `read_result cx` mp_tac (GEN_ALL send_bind_gas_frame) >>
     simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def, SF ETA_ss] >>
     disch_then drule >> simp[]) >>
  ` (do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
        read_result cx tv od) es1 = (res,ee)` by fs[Abbr `src`] >>
  `ee with gas_obs := [] = ee` by
    (simp[vyperStateTheory.evaluation_state_component_equality]) >>
  drule_all send_tail_path_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`res`,`ee`,`G'`,`tn'`,`r`] >>
  simp[gasSummaryTheory.gas_explicit_def]
QED

Theorem send_read_action_ptr:
  LENGTH args = (if has_gas then 3 else 2) ==>
  (do r <- eval_expr cx (Call ann (Send has_gas) args dflt); read_result cx r od) =
  (do vs <- eval_exprs cx args;
      tv <- eval_send cx has_gas vs; read_result cx tv od)
Proof
  strip_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def,
       vyperStateTheory.type_check_def, vyperStateTheory.check_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_return,
       vyperStateTheory.assert_def, vyperStateTheory.bind_assoc] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def, vyperStateTheory.assert_def]
QED


Theorem send_expr_sim_ptr:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) args /\
  ptr_args_ready d ctx PG func cenv cx expr_type (expr_sim_inv cenv cx env) args ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  strip_tac >> drule send_pre_types >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
      expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac >- metis_tac[expr_body_pre_send_arg] >> fs[EVERY_MEM]) >>
  `wb_args_shape cenv expr_type args` by metis_tac[typed_stack_args_shape] >>
  rewrite_tac[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_send >> strip_tac >> gvs[] >>
  drule_all compile_expr_send >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  drule_all send_tail_shape >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `!ee gs. expr_sim_inv cenv cx env ee ==>
      expr_sim_inv cenv cx env (ee with gas_obs := gs)` by simp[] >>
  drule_all lower_typed_args_sim_ptr >> disch_tac >>
  drule_all typed_args_outcome_ptr_facts >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >> disch_tac >>
  drule send_read_action_ptr >> simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- suspend "certificate_head"
  >- suspend "certificate_tail" >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> conj_tac
  >- suspend "normal" >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[wb_args_exit_def, exprSimDefsTheory.expr_exit_def]
QED

Resume send_expr_sim_ptr[certificate_head]:
  rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >> simp[]
QED

Resume send_expr_sim_ptr[certificate_tail]:
  rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_values >> simp[ignore_bind_def]
QED

Resume send_expr_sim_ptr[normal]:
  rpt strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  gvs[] >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` kall_tac >>
  qpat_x_assum `typed_args_ready _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ptr_args_ready _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!e s. MEM e args /\ _ ==> _` kall_tac >>
  qpat_x_assum `wb_args_shape _ _ _` kall_tac >>
  qpat_x_assum `lower_word_args _ _ _ _ = _` kall_tac >>
  `LENGTH vs = LENGTH args` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  `?a v gs. args = a::v::gs` by
    (Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]) >>
  `?to_v amount_v gas_vs. vs = to_v::amount_v::gas_vs /\
      LENGTH gas_vs = (if has_gas then 1 else 0)` by
    (Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]) >>
  gvs[typed_args_post_ptr_def, typed_args_post_def,
      vyperValueTheory.evaluate_type_def] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts` by
    fs[expr_sim_inv_def,
      vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  `op_taint tn gas_op = {} /\ ?gw. eval_operand gas_op t = SOME gw` by
    (Cases_on `has_gas` >> gvs[eval_operand_def, op_taint_def] >>
     gvs[LENGTH_EQ_NUM_compute]) >>
  `dest_AddressV to_v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) to_v))` by
    metis_tac[address_typed_dest] >>
  `dest_NumV amount_v = SOME (w2n (typed_val_to_w256 (BaseTV (UintT 256)) amount_v))` by
    metis_tac[uint256_typed_dest] >>
  suspend "tail_summary"
QED

Resume send_expr_sim_ptr[tail_summary]:
  `!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `expr_type (Call NoneT (Send has_gas) (a::v::gs) dflt) = NoneT` by simp[vyperASTTheory.expr_type_def] >>
  `post_value_type cenv (Call NoneT (Send has_gas) (a::v::gs) dflt) =
   expr_type (Call NoneT (Send has_gas) (a::v::gs) dflt)` by simp[] >>
  drule_all (Q.INST [`e` |-> `Call NoneT (Send has_gas) (a::v::gs) dflt`]
    send_tail_summary_ptr) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_tac >> fs[SF ETA_ss] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  irule gas_summary_ptr_at_conseq >> goal_assum (drule_at Any) >>
  conj_tac >- suspend "tail_post" >> simp[]
QED

Resume send_expr_sim_ptr[tail_post]:
  rpt strip_tac >> gvs[] >>
  conj_tac >- simp[callStepPtrTheory.ptr_val_ok_none] >>
  conj_tac
  >- (strip_tac >> irule callStepPtrTheory.ptr_buf_ok_zero_type >>
      simp[callStepPtrTheory.send_none_buffer_size]) >>
  irule wordArgsPtrTheory.ghost_kept_wb_trans >>
  goal_assum (drule_at Any) >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `ee` >> first_assum ACCEPT_TAC
QED

Finalise send_expr_sim_ptr

Theorem send_expr_vv_sim_ptr:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) args /\
  ptr_args_ready d ctx PG func cenv cx expr_type (expr_sim_inv cenv cx env) args ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  strip_tac >> irule expr_vv_sim_stack_ptr >> rpt conj_tac
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa` >>
      drule compile_expr_send_stack >> simp[])
  >- metis_tac[eval_expr_send_value] >>
  irule send_expr_sim_ptr >> qexists_tac `env` >> simp[]
QED
