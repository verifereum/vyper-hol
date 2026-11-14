(* The CALL and ASSERT use one concrete execution and ghost update. *)
Theory bodyFullSendTail
Ancestors
  exprSendPtr bodyPtrPrecompileBuiltinsSuffix fragGasSeqPtr fragGasEmitCtrl
  fragGasOriginPtr fragGasOrigin gasEvents memSafeRun instMemFrontier
  gasCount ptrSafeRun ptrDiscipline bodyPtrDefs callStepPtr
  venomExecSemantics venomExecProofs venomInst venomInstProofs venomState list
  unitTransformDefs memLocDefs fragExec contextCodegenRel codegenRel

Theorem send_call_assert_path_full[local]:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst aid ASSERT [Var out] []) /\
  ptr_inst_ok D lo 0 ctx fn G tn inst s /\ allocas_from lo s /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\
  step_inst_base inst s = OK u /\ eval_operand (Var out) u = SOME w ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    ((if w = 0w then Abort Revert_abort (revert_state
        (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx)))
      else OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))),
     step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (drule_all step_preserves_control_flow >>
     drule step_preserves_halted >> simp[]) >>
  drule_all send_call_runtime_frame >> strip_tac >>
  `op_taint (step_taint inst s u tn) (Var out) = {}` by
    metis_tac[call_output_untainted] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G inst u, step_taint inst s u tn)` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
     simp[is_terminator_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       eval_operand_def]) >>
  qmatch_goalsub_abbrev_tac `gas_origin_ptr_path _ _ _ (r, G1, tn1)` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (u with vs_inst_idx := SUC s.vs_inst_idx,G1,tn1) [] (r,G1,tn1)` by
    (qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
     `eval_operand (Var out) v = SOME w` by
       gvs[Abbr `v`, eval_operand_def, lookup_var_def] >>
     `step_inst_base (mk_inst aid ASSERT [Var out] []) v =
        if w = 0w then Abort Revert_abort (revert_state (set_returndata [] v))
        else OK v` by (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
     `ptr_inst_ok D lo 0 ctx fn G1 tn1 (mk_inst aid ASSERT [Var out] []) v` by
       (irule assert_ptr_inst_ok >>
        gvs[Abbr `v`, Abbr `tn1`, allocas_from_def] >> metis_tac[]) >>
     Cases_on `w = 0w`
     >- (irule exit_inst_origin_ptr >>
         conj_tac >- simp[Abbr `r`, exit_result_def] >>
         conj_tac >- simp[Abbr `v`] >>
         qexistsl_tac [`bb`, `mk_inst aid ASSERT [Var out] []`] >>
         simp[Abbr `v`, Abbr `r`, mk_inst_def, exit_result_def,
           step_inst_non_invoke, step_assert_behavior,
           mem_safe_step_non_invoke, inst_mem_below_frontier_def,
           inst_dload_in_section_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, gas_events_step_def, gas_count_step_def]) >>
     `step_inst_base (mk_inst aid ASSERT [Var out] []) v = OK v` by
       (simp[Abbr `v`, mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
     drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
     simp[Abbr `v`, Abbr `r`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       assert_ghost_unchanged] >>
     strip_tac >> gvs[GSYM mk_inst_def] >> first_x_assum drule_all >> simp[] >>
     strip_tac >>
     qpat_x_assum `!explicit' PG'. _` (qspecl_then [`explicit`, `PG`] mp_tac) >>
     disch_then (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] (cj 2 gas_origin_ptr_path_rules))) >>
     simp[] >> disch_then irule >>
     irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _`
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] (cj 2 gas_origin_ptr_path_rules))) >>
  simp[] >> disch_then irule >> simp[]
QED

Theorem send_read_checked_tail_full[local]:
  stmt_state_rel H ctx fn cenv cx es s /\ stor_taint_ok_at D tn s /\
  allocas_from lo s /\
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
    ((res = INL NoneV /\ w = 1w /\ state_rel H fn cenv cx es' t /\
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)),
         step_prov PG G inst u, step_taint inst s u tn)) \/
     (res = INR (Error (RuntimeError "send failed")) /\ w = 0w /\
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (Abort Revert_abort (revert_state
          (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx))),
         step_prov PG G inst u, step_taint inst s u tn)))
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >>
  `ptr_inst_ok D lo 0 ctx fn G tn inst s` by
    (irule ptr_inst_ok_send_call_at >> metis_tac[]) >>
  `IS_SOME (eval_operand gas s)` by simp[] >>
  `!w st. eval_operand (Var out) (update_var out w st) = SOME w` by
    simp[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  drule_all send_read_call_step >> strip_tac
  >- (qexistsl_tac [`s'`, `update_var out 1w s'`, `1w`] >> simp[] >>
      drule_at (Pat `step_inst_base _ _ = _`) send_call_assert_path_full >> simp[] >>
      strip_tac >> first_x_assum drule_all >> simp[]) >>
  qexistsl_tac [`s'`, `update_var out 0w s'`, `0w`] >> simp[] >>
  drule_at (Pat `step_inst_base _ _ = _`) send_call_assert_path_full >> simp[] >>
      strip_tac >> first_x_assum drule_all >> simp[]
QED

(* The concrete CALL result is selected once, before the horizon. *)
Theorem send_read_checked_tail_full_uniform:
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
       stmt_state_rel H ctx fn cenv cx es s /\
       stor_taint_ok_at (DF H) tn s) /\
  valid_horizon cx st0 H0 es'.storage_trace /\ allocas_from lo s /\
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
    ((res = INL NoneV /\ w = 1w /\
      !H. valid_horizon cx st0 H es'.storage_trace ==>
        state_rel H fn cenv cx es' t /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)),
           step_prov PG G inst u, step_taint inst s u tn)) \/
     (res = INR (Error (RuntimeError "send failed")) /\ w = 0w /\
      !H. valid_horizon cx st0 H es'.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (Abort Revert_abort (revert_state
            (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx))),
           step_prov PG G inst u, step_taint inst s u tn)))
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_all send_read_checked_tail_full >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `stor_taint_ok_at (DF H0) _ _` kall_tac >>
  qexistsl_tac [`t`, `u`, `w`] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC)
  >- (disj1_tac >> ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
      qx_gen_tac `H1` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H1` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      `step_inst_base inst s = OK (update_var out w t)` by metis_tac[] >>
      `t.vs_vars = s.vs_vars` by
        (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      conj_tac >- (drule_all send_read_state_rel_any >> simp[]) >>
      `~s.vs_call_ctx.cc_static` by
        gvs[exprLoweringPropsTheory.stmt_state_rel_def,
            loweringStateRelDefsTheory.state_rel_def] >>
      `ptr_inst_ok (DF H1) lo 0 ctx fn G tn inst s` by
        (irule ptr_inst_ok_send_call_at >> metis_tac[]) >>
      drule_all send_call_assert_path_full >> simp[]) >>
  disj2_tac >> ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H1` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H1` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `~s.vs_call_ctx.cc_static` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >>
  `ptr_inst_ok (DF H1) lo 0 ctx fn G tn inst s` by
    (irule ptr_inst_ok_send_call_at >> metis_tac[]) >>
  drule_all send_call_assert_path_full >> simp[]
QED
