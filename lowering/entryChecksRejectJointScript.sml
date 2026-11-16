(* Joint abort endpoint for installed entry checks. *)
Theory entryChecksRejectJoint
Ancestors entryChecksLayout entryChecksPassPtr entryPrefixPtr entryDispatchPtr fragGasOriginPtr
  arithmetic moduleLoweringProps exprLoweringProps
  fragGasOrigin fragGasPathPtr fragGasPathMem fragExec ptrSafeRun ptrDiscipline
  unitTransformDefs instMemFrontier contextCodegenRel memSafeRun gasCount gasEvents venomExecSemantics venomInst venomState
  emitHelperProps compileEnv codegenRel moduleLowering list words finite_map

Theorem assert_revert_origin_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) /\
  ~s.vs_halted /\ eval_operand op s = SOME 0w /\
  op_taint tn op = {} /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (Abort Revert_abort (revert_state (set_returndata [] s)),G,tn)
Proof
  strip_tac >> rpt gen_tac >> irule (cj 3 gas_origin_ptr_path_rules) >>
  simp[exit_result_def, gas_origin_ptr_edge_def] >> conj_tac
  >- (simp[gas_origin_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, step_ASSERT_revert, mk_inst_def,
           gas_events_step_def, mem_safe_step_non_invoke,
           inst_mem_below_frontier_def, inst_dload_in_section_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def,
           exit_result_def] >> metis_tac[]) >>
  simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, step_ASSERT_revert, mk_inst_def,
       gas_count_step_def, ptr_safe_step_def, ptr_inst_ok_def,
       access_ok_def, taint_ok_def, exit_result_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  metis_tac[]
QED

Theorem checks_origin_then[local]:
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u)) /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,H,u) [] (r,J,v)) ==>
  !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,J,v)
Proof
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED

Theorem compile_entry_value_reject_joint[local]:
  compile_entry_checks 4 F st = ((),last) /\ fn_has_code st last fn /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_call_ctx.cc_callvalue <> 0w ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort z,H,u)
Proof
  strip_tac >> drule_all compile_entry_checks_value_layout >> strip_tac >>
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
  `!fuel. step_inst fuel ctx
    (mk_inst (st.cs_next_id + 1) ISZERO
      [Var (STRING #"%" (toString st.cs_next_var))]
      [STRING #"%" (toString (st.cs_next_var + 1))]) s1 =
    OK (update_var (STRING #"%" (toString (st.cs_next_var + 1))) 0w s1)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
         bool_to_word_def] >>
  drule dispatch_scalar_update_ptr_endpoint >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  disch_then (qspecl_then [`st with cs_next_var := st.cs_next_var + 1`,
    `last`, `lo`, `PG`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- fs[arithmeticTheory.ADD1]) >> strip_tac >>
  rename1 `vars_pc_only s1 s2` >> rename1 `G2 = step_prov PG G1 _ _` >>
  rename1 `op_taint tn2 (Var (STRING #"%" (toString (st.cs_next_var + 1)))) = {}` >>
  qpat_x_assum `s2 = _` kall_tac >> qpat_x_assum `G2 = _` kall_tac >>
  qpat_x_assum `tn2 = _` kall_tac >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s2,G2,tn2) []
    (Abort Revert_abort (revert_state (set_returndata [] s2)),G2,tn2)` by
    (irule assert_revert_origin_ptr >> simp[] >>
     qexistsl_tac [`st.cs_next_id + 2`,
       `Var (STRING #"%" (toString (st.cs_next_var + 1)))`] >> fs[ADD1]) >>
  qexistsl_tac [`revert_state (set_returndata [] s2)`, `G2`, `tn2`] >>
  conj_tac >- simp[revert_state_def, set_returndata_def] >>
  irule checks_origin_then >> qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[] >>
  irule checks_origin_then >> qexistsl_tac [`G2`, `s2`, `tn2`] >> simp[]
QED

Theorem compile_entry_size_reject_joint[local]:
  compile_entry_checks m T st = ((),last) /\ fn_has_code st last fn /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  4 < m /\ m < dimword (:256) /\
  LENGTH s.vs_call_ctx.cc_calldata < m /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort z,H,u)
Proof
  strip_tac >> drule_all compile_entry_checks_size_layout >> strip_tac >>
  `!fuel. step_inst fuel ctx
    (mk_inst st.cs_next_id CALLDATASIZE [] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
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

Resume compile_entry_size_reject_joint[lt]:
  `!fuel. step_inst fuel ctx
    (mk_inst (st.cs_next_id + 1) LT
      [Var (STRING #"%" (toString st.cs_next_var)); Lit (n2w m)]
      [STRING #"%" (toString (st.cs_next_var + 1))]) s1 =
    OK (update_var (STRING #"%" (toString (st.cs_next_var + 1))) 1w s1)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
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

Resume compile_entry_size_reject_joint[iszero]:
  `!fuel. step_inst fuel ctx
    (mk_inst (st.cs_next_id + 2) ISZERO
      [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
      [STRING #"%" (toString (st.cs_next_var + 2))]) s2 =
    OK (update_var (STRING #"%" (toString (st.cs_next_var + 2))) 0w s2)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
         bool_to_word_def] >>
  drule dispatch_scalar_update_ptr_endpoint >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  disch_then (qspecl_then [`st with cs_next_var := st.cs_next_var + 2`,
    `last`, `lo`, `PG`, `G2`, `tn2`] mp_tac) >>
  (impl_tac >- fs[arithmeticTheory.ADD1]) >> strip_tac >>
  rename1 `vars_pc_only s2 s3` >> rename1 `G3 = step_prov PG G2 _ _` >>
  rename1 `op_taint tn3 (Var (STRING #"%" (toString (st.cs_next_var + 2)))) = {}` >>
  qpat_x_assum `s3 = _` kall_tac >> qpat_x_assum `G3 = _` kall_tac >>
  qpat_x_assum `tn3 = _` kall_tac >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s3,G3,tn3) []
    (Abort Revert_abort (revert_state (set_returndata [] s3)),G3,tn3)` by
    (irule assert_revert_origin_ptr >> simp[] >>
     qexistsl_tac [`st.cs_next_id + 3`,
       `Var (STRING #"%" (toString (st.cs_next_var + 2)))`] >> fs[ADD1]) >>
  qexistsl_tac [`revert_state (set_returndata [] s3)`, `G3`, `tn3`] >>
  conj_tac >- simp[revert_state_def, set_returndata_def] >>
  irule checks_origin_then >> qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[] >>
  irule checks_origin_then >> qexistsl_tac [`G2`, `s2`, `tn2`] >> simp[] >>
  irule checks_origin_then >> qexistsl_tac [`G3`, `s3`, `tn3`] >> simp[]
QED

Finalise compile_entry_size_reject_joint

Theorem compile_entry_checks_reject_joint:
  compile_entry_checks m pay st = ((),last) /\ fn_has_code st last fn /\
  ~block_is_terminated st /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ s.vs_returndata = [] /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  m < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  ((~pay /\ s.vs_call_ctx.cc_callvalue <> 0w) \/
   (4 < m /\ LENGTH s.vs_call_ctx.cc_calldata < m)) ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort z,H,u)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_entry_checks_split >> strip_tac >>
  Cases_on `pay`
  >- (gvs[] >> irule compile_entry_size_reject_joint >>
      simp[] >> qexistsl_tac [`last`, `m`, `mid`] >> simp[]) >>
  Cases_on `s.vs_call_ctx.cc_callvalue = 0w`
  >- (gvs[] >>
      `compile_entry_checks 0 F st = ((),mid)` by
        (qpat_x_assum `compile_entry_checks 4 _ _ = _` mp_tac >>
         simp[compile_entry_checks_def]) >>
      drule compile_entry_checks_ptr_endpoint >>
      disch_then (qspecl_then [`tn`, `s`, `lo`, `fn`, `ctx`, `PG`, `G`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      rename1 `vars_pc_only s s1` >>
      rename1 `tn1.t_mem = tn.t_mem` >>
      rename1 `ptr_safe_run _ _ _ _ _ _ G1 tn1 s1` >>
      `s1.vs_call_ctx = s.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
      `?z H u. z.vs_returndata = [] /\
        !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s1,G1,tn1) []
          (Abort Revert_abort z,H,u)` by
        (irule compile_entry_size_reject_joint >>
         simp[] >> qexistsl_tac [`last`, `m`, `mid`] >> simp[]) >>
      qexistsl_tac [`z`, `H`, `u`] >> simp[] >>
      irule checks_origin_then >> qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[]) >>
  gvs[] >> irule compile_entry_value_reject_joint >>
  simp[] >> qexistsl_tac [`mid`, `st`] >> simp[]
QED
