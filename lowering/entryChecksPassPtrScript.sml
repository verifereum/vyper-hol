(* Exact pointer-safe endpoints of passing entry checks. *)
Theory entryChecksPassPtr
Ancestors entryChecksLayout entryPrefixPtr entryChecksPtr entryChecksProps moduleLowering
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

Theorem compile_entry_value_check_ptr_endpoint[local]:
  compile_entry_checks 4 pay st = ((),st') /\
  (~pay ==> fn_has_code st st' fn) /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) ==>
  ?u G' tn'.
    vars_pc_only s u /\ fresh_vars_wrt st' u /\ ~u.vs_halted /\
    u.vs_current_bb = st'.cs_current_bb /\
    u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' u) ==>
         !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  Cases_on `pay`
  >- (simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexistsl_tac [`s`, `G`, `tn`] >> simp[vars_pc_only_refl]) >>
  strip_tac >> fs[] >> drule_all compile_entry_checks_value_layout >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)])` by simp[] >>
  drule callvalue_ptr_endpoint >> disch_then drule >>
  disch_then (qspecl_then [`ctx`, `st`, `st with cs_next_var := st.cs_next_var + 1`,
    `lo`, `PG`, `G`, `tn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only s s1` >> rename1 `G1 = step_prov PG G _ _` >>
  rename1 `op_taint tn1 (Var _) = {}` >>
  qpat_x_assum `s1 = _` kall_tac >> qpat_x_assum `G1 = _` kall_tac >>
  qpat_x_assum `tn1 = _` kall_tac >>
  suspend "iszero"
QED

Resume compile_entry_value_check_ptr_endpoint[iszero]:
  `!fuel. step_inst fuel ctx
    (mk_inst (st.cs_next_id + 1) ISZERO
      [Var (STRING #"%" (toString st.cs_next_var))]
      [STRING #"%" (toString (st.cs_next_var + 1))]) s1 =
    OK (update_var (STRING #"%" (toString (st.cs_next_var + 1))) 1w s1)` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def, exec_pure1_def,
         bool_to_word_def] >>
  drule dispatch_scalar_update_ptr_endpoint >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  disch_then (qspecl_then [`st with cs_next_var := st.cs_next_var + 1`,
    `st'`, `lo`, `PG`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- fs[arithmeticTheory.ADD1]) >> strip_tac >>
  rename1 `vars_pc_only s1 s2` >> rename1 `G2 = step_prov PG G1 _ _` >>
  rename1 `op_taint tn2 (Var (STRING #"%" (toString (st.cs_next_var + 1)))) = {}` >>
  qpat_x_assum `s2 = _` kall_tac >> qpat_x_assum `G2 = _` kall_tac >>
  qpat_x_assum `tn2 = _` kall_tac >>
  qexistsl_tac [`s2 with vs_inst_idx := SUC s2.vs_inst_idx`, `G2`, `tn2`] >>
  `vars_pc_only s s2` by metis_tac[vars_pc_only_trans] >>
  `allocas_from lo (s2 with vs_inst_idx := SUC s2.vs_inst_idx) /\
   (ctx_has_dalloca ctx ==>
    allocas_below_fmp (s2 with vs_inst_idx := SUC s2.vs_inst_idx))` by
    (fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[vars_pc_only_inst_idx, control_moves_keep_vars] >>
  rpt strip_tac >>
  `ptr_safe_run D lo fuel ctx fn PG G2 tn2 s2` suffices_by metis_tac[] >>
  irule assert_pass_ptr_continuation >> simp[] >>
  qexistsl_tac [`st.cs_next_id + 2`,
    `Var (STRING #"%" (toString (st.cs_next_var + 1)))`, `1w`] >>
  fs[arithmeticTheory.ADD1]
QED

Finalise compile_entry_value_check_ptr_endpoint

Theorem compile_entry_size_check_ptr_endpoint[local]:
  compile_entry_checks m T st = ((),st') /\
  (4 < m ==> fn_has_code st st' fn) /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  m <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?u G' tn'.
    vars_pc_only s u /\ fresh_vars_wrt st' u /\ ~u.vs_halted /\
    u.vs_current_bb = st'.cs_current_bb /\
    u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' u) ==>
         !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  Cases_on `4 < m`
  >- (strip_tac >> `fn_has_code st st' fn` by metis_tac[] >> drule_all compile_entry_checks_size_layout >> strip_tac >>
      suspend "size") >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> qexistsl_tac [`s`, `G`, `tn`] >> simp[vars_pc_only_refl]
QED

Resume compile_entry_size_check_ptr_endpoint[size]:
  `!fuel. step_inst fuel ctx
    (mk_inst st.cs_next_id CALLDATASIZE [] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def, exec_read0_def] >>
  drule dispatch_scalar_update_ptr_endpoint >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  disch_then (qspecl_then [`st`, `st with cs_next_var := st.cs_next_var + 1`,
    `lo`, `PG`, `G`, `tn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only s s1` >> rename1 `G1 = step_prov PG G _ _` >>
  rename1 `op_taint tn1 (Var _) = {}` >>
  qpat_x_assum `s1 = _` kall_tac >> qpat_x_assum `G1 = _` kall_tac >>
  qpat_x_assum `tn1 = _` kall_tac >>
  suspend "lt"
QED

Resume compile_entry_size_check_ptr_endpoint[lt]:
  `m < dimword (:256)` by decide_tac >>
  `!fuel. step_inst fuel ctx
    (mk_inst (st.cs_next_id + 1) LT
      [Var (STRING #"%" (toString st.cs_next_var)); Lit (n2w m)]
      [STRING #"%" (toString (st.cs_next_var + 1))]) s1 =
    OK (update_var (STRING #"%" (toString (st.cs_next_var + 1))) 0w s1)` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, word_lo_n2w, bool_to_word_def] >>
  drule dispatch_scalar_update_ptr_endpoint >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  disch_then (qspecl_then [`st with cs_next_var := st.cs_next_var + 1`,
    `st with cs_next_var := st.cs_next_var + 2`, `lo`, `PG`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- fs[arithmeticTheory.ADD1, op_taint_def]) >> strip_tac >>
  rename1 `vars_pc_only s1 s2` >> rename1 `G2 = step_prov PG G1 _ _` >>
  rename1 `op_taint tn2 (Var (STRING #"%" (toString (st.cs_next_var + 1)))) = {}` >>
  qpat_x_assum `s2 = _` kall_tac >> qpat_x_assum `G2 = _` kall_tac >>
  qpat_x_assum `tn2 = _` kall_tac >>
  suspend "iszero"
QED

Resume compile_entry_size_check_ptr_endpoint[iszero]:
  `!fuel. step_inst fuel ctx
    (mk_inst (st.cs_next_id + 2) ISZERO
      [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
      [STRING #"%" (toString (st.cs_next_var + 2))]) s2 =
    OK (update_var (STRING #"%" (toString (st.cs_next_var + 2))) 1w s2)` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def, exec_pure1_def,
         bool_to_word_def] >>
  drule dispatch_scalar_update_ptr_endpoint >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  disch_then (qspecl_then [`st with cs_next_var := st.cs_next_var + 2`,
    `st'`, `lo`, `PG`, `G2`, `tn2`] mp_tac) >>
  (impl_tac >- fs[arithmeticTheory.ADD1]) >> strip_tac >>
  rename1 `vars_pc_only s2 s3` >> rename1 `G3 = step_prov PG G2 _ _` >>
  rename1 `op_taint tn3 (Var (STRING #"%" (toString (st.cs_next_var + 2)))) = {}` >>
  qpat_x_assum `s3 = _` kall_tac >> qpat_x_assum `G3 = _` kall_tac >>
  qpat_x_assum `tn3 = _` kall_tac >>
  qexistsl_tac [`s3 with vs_inst_idx := SUC s3.vs_inst_idx`, `G3`, `tn3`] >>
  `vars_pc_only s s3` by metis_tac[vars_pc_only_trans] >>
  `allocas_from lo (s3 with vs_inst_idx := SUC s3.vs_inst_idx) /\
   (ctx_has_dalloca ctx ==>
    allocas_below_fmp (s3 with vs_inst_idx := SUC s3.vs_inst_idx))` by
    (fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[vars_pc_only_inst_idx, control_moves_keep_vars] >>
  rpt strip_tac >>
  `ptr_safe_run D lo fuel ctx fn PG G3 tn3 s3` suffices_by metis_tac[] >>
  irule assert_pass_ptr_continuation >> simp[] >>
  qexistsl_tac [`st.cs_next_id + 3`,
    `Var (STRING #"%" (toString (st.cs_next_var + 2)))`, `1w`] >>
  fs[arithmeticTheory.ADD1]
QED

Finalise compile_entry_size_check_ptr_endpoint

Theorem compile_entry_checks_ptr_endpoint:
  compile_entry_checks m pay st = ((),st') /\ fn_has_code st st' fn /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  m <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?u G' tn'.
    vars_pc_only s u /\ fresh_vars_wrt st' u /\ ~u.vs_halted /\
    u.vs_current_bb = st'.cs_current_bb /\
    u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' u) ==>
         !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all compile_entry_checks_split >> strip_tac >>
  drule compile_entry_value_check_ptr_endpoint >>
  disch_then (qspecl_then [`tn`, `s`, `lo`, `fn`, `ctx`, `PG`, `G`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only s s1` >>
  rename1 `tn1.t_mem = tn.t_mem` >>
  rename1 `ptr_safe_run _ _ _ _ _ _ G1 tn1 s1` >>
  `s1.vs_call_ctx = s.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  drule compile_entry_size_check_ptr_endpoint >>
  disch_then (qspecl_then [`tn1`, `s1`, `lo`, `fn`, `ctx`, `PG`, `G1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only s1 s2` >>
  qexistsl_tac [`s2`, `G'`, `tn'`] >>
  simp[] >> metis_tac[vars_pc_only_trans]
QED
