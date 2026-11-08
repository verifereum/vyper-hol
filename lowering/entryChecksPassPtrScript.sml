(* Exact pointer-safe endpoints of passing entry checks. *)
Theory entryChecksPassPtr
Ancestors entryPrefixPtr entryChecksPtr entryChecksProps moduleLowering
  ptrSafeRun ptrDiscipline fragExec venomExecSemantics venomInst venomState
  compileEnv emitHelperProps exprLoweringProps codegenRel list finite_map words
  moduleLoweringProps typedCopyArrayPtr entryDispatchPtr contextCodegenRel

Theorem callvalue_ptr_endpoint:
  !fn bb.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id CALLVALUE [] [out]) ==>
  !st st_next lo PG G tn.
  out = STRING #"%" (toString st.cs_next_var) /\
  st_next.cs_next_var = SUC st.cs_next_var /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    u = (update_var out s.vs_call_ctx.cc_callvalue s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst id CALLVALUE [] [out])
      (update_var out s.vs_call_ctx.cc_callvalue s) /\
    tn' = step_taint (mk_inst id CALLVALUE [] [out]) s
      (update_var out s.vs_call_ctx.cc_callvalue s) tn /\
    vars_pc_only s u /\ fresh_vars_wrt st_next u /\ ~u.vs_halted /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
    eval_operand (Var out) u = SOME s.vs_call_ctx.cc_callvalue /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' u ==>
              ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `t = update_var out s.vs_call_ctx.cc_callvalue s` >>
  qexistsl_tac [`t with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst id CALLVALUE [] [out]) t`,
    `step_taint (mk_inst id CALLVALUE [] [out]) s t tn`] >>
  `fresh_vars_wrt st_next t` by
    (simp[Abbr `t`] >> irule fresh_vars_wrt_advance >>
     qexistsl_tac [`st.cs_next_var`, `st`] >> simp[]) >>
  `op_taint (step_taint (mk_inst id CALLVALUE [] [out]) s t tn) (Var out) = {} /\
   (step_taint (mk_inst id CALLVALUE [] [out]) s t tn).t_mem = tn.t_mem /\
   (step_taint (mk_inst id CALLVALUE [] [out]) s t tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst id CALLVALUE [] [out]) s t tn).t_trans = tn.t_trans /\
   (step_taint (mk_inst id CALLVALUE [] [out]) s t tn).t_imm = tn.t_imm` by
    simp[Abbr `t`, step_taint_def, mk_inst_def, set_var_taint_def,
         FLOOKUP_UPDATE, op_taint_def, out_taint_def, update_var_def,
         mem_taint_def, new_site_bytes_def, step_writes_def,
         written_taint_def, source_memory_write_ranges_def, adopt_reset_def,
         store_taint_def, imm_taint_def, range_bytes_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `t`, vars_pc_only_inst_idx, vars_pc_only_update_var,
       vars_pc_only_refl, control_moves_keep_vars, update_var_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- (fs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> fs[allocas_below_fmp_def] >> metis_tac[]) >>
  rpt strip_tac >>
  irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `mk_inst id CALLVALUE [] [out]`,
    `update_var out s.vs_call_ctx.cc_callvalue s`] >>
  simp[update_var_def, mk_inst_def, is_terminator_def, step_inst_non_invoke,
       step_inst_base_def, exec_read0_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_def, exec_read0_def,
       mk_inst_def, update_var_def] >>
  fs[mk_inst_def]
QED

Theorem assert_pass_ptr_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) /\
  eval_operand op s = SOME v /\ v <> 0w /\ op_taint tn op = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  !D fuel. ptr_safe_run D lo fuel ctx fn PG G tn
    (s with vs_inst_idx := SUC s.vs_inst_idx) ==>
    ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id ASSERT [op] []) s = G /\
   step_taint (mk_inst id ASSERT [op] []) s s tn = tn` by
    (simp[step_prov_def, step_taint_def, mk_inst_def, set_var_taint_def,
          mem_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
          source_memory_write_ranges_def, adopt_reset_def, store_taint_def,
          imm_taint_def, range_bytes_def, FLOOKUP_DEF,
          pred_setTheory.EXTENSION, SF CONJ_ss] >>
     simp[set_prov_def, DRESTRICT_UNIV, taint_component_equality]) >>
  rpt strip_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `mk_inst id ASSERT [op] []`, `s`] >>
  simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def, is_terminator_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_def, mk_inst_def]
QED
