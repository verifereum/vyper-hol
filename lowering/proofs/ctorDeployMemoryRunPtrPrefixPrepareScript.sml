(* Successful finite deployment prefix before argument registration. *)
Theory ctorDeployMemoryRunPtrPrefixPrepare
Ancestors
  ctorDeployMemoryRunPtrPrefixRegisterAddress ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixSequence context compileEnv emitHelper emitHelperProps exprLoweringProps
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  finite_map words arithmetic pred_set list rich_list codegenRel contextCodegenRel memLocDefs
  fragExec abiDecoderContract abiDecoderLoop

Theorem prefix_prepare_callvalue_step:
  step_inst_base (mk_inst iid CALLVALUE [] [x]) s =
    OK (update_var x s.vs_call_ctx.cc_callvalue s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_read0_def]
QED

Theorem prefix_prepare_zero_step:
  step_inst_base (mk_inst iid ASSIGN [Lit 0w] [x]) s = OK (update_var x 0w s)
Proof
  simp[step_inst_base_def, mk_inst_def, eval_operand_def]
QED

Theorem prefix_prepare_callvalue_ptr:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid CALLVALUE [] [x]) s
Proof
  strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
    step_inst_non_invoke, prefix_prepare_callvalue_step, mk_inst_def,
    taint_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    update_var_def]
QED

Theorem prefix_prepare_zero_ptr:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid ASSIGN [Lit 0w] [x]) s
Proof
  strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
    step_inst_non_invoke, prefix_prepare_zero_step, mk_inst_def,
    taint_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
    op_taint_def, update_var_def]
QED

Theorem prefix_prepare_callvalue_ghost:
  ghost_step fuel ctx PG G tn (mk_inst iid CALLVALUE [] [x]) s =
    (DRESTRICT G (COMPL {x}), tn with t_var := tn.t_var |+ (x,{}))
Proof
  simp[ghost_step_def, step_inst_non_invoke, prefix_prepare_callvalue_step,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def, out_taint_def,
    set_var_taint_def, mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def, update_var_def,
    source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality,
    mk_inst_def]
QED

Theorem prefix_prepare_zero_ghost:
  ghost_step fuel ctx PG G tn (mk_inst iid ASSIGN [Lit 0w] [x]) s =
    (DRESTRICT G (COMPL {x}), tn with t_var := tn.t_var |+ (x,{}))
Proof
  simp[ghost_step_def, step_inst_non_invoke, prefix_prepare_zero_step,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def, out_taint_def,
    set_var_taint_def, mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def, update_var_def,
    source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality,
    op_prov_def, first_prov_def, op_taint_def, eval_operand_def, mk_inst_def]
QED

Theorem prefix_prepare_callvalue_run:
  emit_op CALLVALUE [] st = (out,middle) /\ fn_has_code st middle fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let x = STRING #"%" (toString st.cs_next_var);
      t = (update_var x s.vs_call_ctx.cc_callvalue s)
            with vs_inst_idx := LENGTH middle.cs_current_insts
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
        (tn with t_var := tn.t_var |+ (x,{})) t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  match_mp_tac (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`]
    prefix_register_address_emit_run) >>
  simp[update_var_def] >> rpt strip_tac >>
  `step_inst fuel ctx (mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) s.vs_call_ctx.cc_callvalue s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def, exec_read0_def] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)])` by simp[] >>
  `~is_terminator (mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  simp[prefix_prepare_callvalue_ptr, prefix_prepare_callvalue_ghost, update_var_def]
QED

Theorem prefix_prepare_zero_run:
  emit_op ASSIGN [Lit 0w] st = (out,middle) /\ fn_has_code st middle fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let x = STRING #"%" (toString st.cs_next_var);
      t = (update_var x 0w s) with vs_inst_idx := LENGTH middle.cs_current_insts
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
        (tn with t_var := tn.t_var |+ (x,{})) t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  match_mp_tac (Q.INST [`opc` |-> `ASSIGN`, `ops` |-> `[Lit 0w]`]
    prefix_register_address_emit_run) >>
  simp[update_var_def] >> rpt strip_tac >>
  `step_inst fuel ctx (mk_inst st.cs_next_id ASSIGN [Lit 0w] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) 0w s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def, eval_operand_def] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id ASSIGN [Lit 0w] [STRING #"%" (toString st.cs_next_var)])` by simp[] >>
  `~is_terminator (mk_inst st.cs_next_id ASSIGN [Lit 0w] [STRING #"%" (toString st.cs_next_var)]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  simp[prefix_prepare_zero_ptr, prefix_prepare_zero_ghost, update_var_def]
QED

Theorem prefix_prepare_fixed_region_emit:
  compile_fixed_region_with_id cap st = ((iid,buf),last) ==>
  iid = st.cs_next_id /\ buf.buf_size = cap /\
  emit_op ASSIGN [Lit 0w] st = (buf.buf_operand,last)
Proof
  simp[compile_fixed_region_with_id_def, emit_op_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem prefix_prepare_iszero_step:
  eval_operand a s = SOME 0w ==>
  step_inst_base (mk_inst iid ISZERO [a] [x]) s = OK (update_var x 1w s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure1_def, bool_to_word_def]
QED

Theorem prefix_prepare_iszero_ghost:
  eval_operand a s = SOME 0w ==>
  ghost_step fuel ctx PG G tn (mk_inst iid ISZERO [a] [x]) s =
    (DRESTRICT G (COMPL {x}), tn with t_var := tn.t_var |+ (x,{}))
Proof
  strip_tac >>
  simp[ghost_step_def, step_inst_non_invoke, prefix_prepare_iszero_step,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def, out_taint_def,
    set_var_taint_def, mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def, update_var_def,
    source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality,
    mk_inst_def]
QED

Theorem prefix_prepare_iszero_run:
  emit_op ISZERO [a] st = (out,middle) /\ fn_has_code st middle fn /\
  eval_operand a s = SOME 0w /\ op_taint tn a = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let x = STRING #"%" (toString st.cs_next_var);
      t = (update_var x 1w s) with vs_inst_idx := LENGTH middle.cs_current_insts
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG (DRESTRICT G (COMPL {x}))
        (tn with t_var := tn.t_var |+ (x,{})) t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  match_mp_tac (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[a]`]
    prefix_register_address_emit_run) >>
  simp[update_var_def] >> rpt strip_tac >>
  `step_inst fuel ctx (mk_inst st.cs_next_id ISZERO [a] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) 1w s)` by
    simp[step_inst_non_invoke, mk_inst_def, prefix_prepare_iszero_step] >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id ISZERO [a] [STRING #"%" (toString st.cs_next_var)])` by simp[] >>
  `~is_terminator (mk_inst st.cs_next_id ISZERO [a] [STRING #"%" (toString st.cs_next_var)]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  simp[prefix_iszero_ptr_step, prefix_prepare_iszero_ghost, update_var_def]
QED

Theorem prefix_prepare_emit_actual:
  emit_op opc ops st = (out,last) /\
  ((opc = CALLVALUE /\ ops = [] /\ w = initial.vs_call_ctx.cc_callvalue) \/
   (opc = ASSIGN /\ ops = [Lit 0w] /\ w = 0w) \/
   (opc = ISZERO /\ ops = [a] /\ eval_operand a initial = SOME 0w /\
    op_taint tn a = {} /\ w = 1w)) /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt. eval_operand out t = SOME w /\ op_taint qt out = {} /\
    op_prov H out = NONE /\ fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `opc <> INVOKE /\ ~is_terminator opc /\
   run_inst_seq (emitted_insts st last) initial = OK
      (update_var (STRING #"%" (toString st.cs_next_var)) w initial)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[is_terminator_def, run_inst_seq_def, prefix_prepare_callvalue_step,
       prefix_prepare_zero_step, prefix_prepare_iszero_step]) >>
  drule_all prefix_register_address_emit_finish >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule prefix_register_address_emit_shape >> strip_tac >>
  qexistsl [`(update_var (STRING #"%" (toString st.cs_next_var)) w initial)
               with vs_inst_idx := LENGTH last.cs_current_insts`,
            `DRESTRICT G (COMPL {STRING #"%" (toString st.cs_next_var)})`,
            `tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})`] >>
  `!y. not_fresh_at st y ==> y <> STRING #"%" (toString st.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  asm_rewrite_tac[] >>
  simp[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    update_var_def] >>
  gvs[] >>
  FIRST [drule_all prefix_prepare_callvalue_run, drule_all prefix_prepare_zero_run,
         drule_all prefix_prepare_iszero_run] >>
  simp[update_var_def]
QED

Theorem prefix_prepare_assert_actual:
  emit_void ASSERT [a] st = ((),last) /\
  eval_operand a initial = SOME w /\ w <> 0w /\ op_taint tn a = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let t = initial with vs_inst_idx := LENGTH last.cs_current_insts
  in fresh_vars_wrt last t /\ ~t.vs_halted /\
    t.vs_current_bb = last.cs_current_bb /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG G tn t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `last.cs_current_bb = st.cs_current_bb /\
   last.cs_current_insts = st.cs_current_insts ++ [mk_inst st.cs_next_id ASSERT [a] []] /\
   last.cs_next_var = st.cs_next_var /\ last.cs_blocks = st.cs_blocks` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  `emitted_insts st last = [mk_inst st.cs_next_id ASSERT [a] []]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `frag_exec ctx st last (\s. s = initial)
     (\t. t = initial with vs_inst_idx := LENGTH last.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[run_inst_seq_def, step_inst_base_def,
       is_terminator_def, mk_inst_def]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  fs[fresh_vars_wrt_def] >>
  `?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX last.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `get_instruction bb initial.vs_inst_idx = SOME (mk_inst st.cs_next_id ASSERT [a] [])` by
    (gvs[IS_PREFIX_APPEND] >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  `lookup_block st.cs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx func PG G tn bb
      (initial with vs_inst_idx := SUC initial.vs_inst_idx)` by
    (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` (qspec_then `fuel` mp_tac) >>
     simp[ptr_safe_run_def, ADD1]) >>
  `step_inst fuel ctx (mk_inst st.cs_next_id ASSERT [a] []) initial = OK initial` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def] >>
  `~is_terminator (mk_inst st.cs_next_id ASSERT [a] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  `ptr_safe_block D lo fuel ctx func PG G tn bb initial` by
    (drule_all ptr_safe_block_step >> strip_tac >>
     fs[prefix_assert_ptr_step, prefix_assert_ghost_step] >> metis_tac[]) >>
  simp[ptr_safe_run_def]
QED

Theorem prefix_prepare_region_actual:
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) st = (imm,last) /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    eval_operand imm t = SOME 0w /\ op_taint qt imm = {} /\ op_prov H imm = NONE /\
    fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> Cases_on `cap > 0`
  >- (gvs[comp_bind_def, comp_return_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> rename1 `compile_fixed_region_with_id cap st = (r,last)` >>
      PairCases_on `r` >>
      drule prefix_prepare_fixed_region_emit >> strip_tac >>
      simp[] >> irule prefix_prepare_emit_actual >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[comp_return_def] >> qexistsl [`initial`,`G`,`tn`] >>
  simp[eval_operand_def, op_taint_def, op_prov_def, abi_decode_sim_refl]
QED

Theorem prefix_prepare_paycheck_actual:
  emit_op CALLVALUE [] st = (cv,sa) /\
  emit_op ISZERO [cv] sa = (nv,sb) /\ emit_void ASSERT [nv] sb = ((),last) /\
  fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb last func /\
  initial.vs_call_ctx.cc_callvalue = 0w /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`, `w` |-> `0w`]
    prefix_prepare_emit_actual)) >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choose_then `s1` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `allocas_from lo s1` by (fs[allocas_from_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[cv]`, `a` |-> `cv`, `w` |-> `1w`]
    prefix_prepare_emit_actual)) >>
  disch_then (qspecl_then [`PG`,`G1`,`D`]
    (qx_choose_then `s2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `allocas_from lo s2` by (fs[allocas_from_def] >> metis_tac[]) >>
  `1w <> (0w:bytes32)` by simp[] >>
  drule_all prefix_prepare_assert_actual >>
  disch_then (qspecl_then [`PG`,`G2`,`D`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `!y. not_fresh_at st y ==> not_fresh_at sa y` by
    (drule (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`] prefix_register_address_emit_shape) >>
     strip_tac >> simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  qexistsl [`s2 with vs_inst_idx := LENGTH last.cs_current_insts`,`G2`,`tn2`] >>
  simp[lookup_var_def] >>
  rpt conj_tac
  >- metis_tac[lookup_var_def]
  >- metis_tac[abi_decode_sim_trans]
  >> metis_tac[]
QED

Theorem prefix_prepare_payable_actual:
  (if payable then comp_return ()
   else comp_bind (emit_op CALLVALUE [])
     (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),last) /\
  (payable \/ initial.vs_call_ctx.cc_callvalue = 0w) /\
  fn_has_code st last func /\ allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `payable`
  >- (gvs[comp_return_def] >> qexistsl [`initial`,`G`,`tn`] >> simp[abi_decode_sim_refl]) >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLVALUE [] st = (cv,sa)` >>
  rename1 `emit_op ISZERO [cv] sa = (nv,sb)` >>
  `cs_extends st sa` by (drule (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`]
      prefix_register_address_emit_shape) >> simp[]) >>
  `cs_extends sa sb` by (drule (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[cv]`]
      prefix_register_address_emit_shape) >> simp[]) >>
  `cs_extends sb last` by
    (irule cs_extends_same_block >>
     gvs[emit_void_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,fresh_id_def,emit_def]) >>
  `fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb last func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  irule prefix_prepare_paycheck_actual >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem prefix_prepare_payable_layout:
  (if payable then comp_return ()
   else comp_bind (emit_op CALLVALUE [])
     (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),last) ==>
  cs_extends st last /\ st.cs_next_var <= last.cs_next_var
Proof
  Cases_on `payable` >>
  simp[comp_return_def,comp_bind_def,comp_ignore_bind_def,emit_op_def,emit_void_def,
       fresh_var_def,fresh_id_def,emit_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

Theorem prefix_prepare_region_layout:
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) st = (imm,last) ==>
  cs_extends st last /\ st.cs_next_var <= last.cs_next_var
Proof
  Cases_on `cap > 0` >>
  simp[comp_return_def,comp_bind_def,comp_ignore_bind_def,compile_fixed_region_with_id_def,
       emit_op_def,fresh_var_def,fresh_id_def,emit_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

(* Same-witness semantic execution and ghost continuation through both optional stages. *)
Theorem prefix_prepare_actual:
  (if payable then comp_return ()
   else comp_bind (emit_op CALLVALUE [])
     (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),pay) /\
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) pay = (imm,last) /\
  (payable \/ initial.vs_call_ctx.cc_callvalue = 0w) /\
  fn_has_code st last func /\ allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    eval_operand imm t = SOME 0w /\ op_taint qt imm = {} /\ op_prov H imm = NONE /\
    fresh_vars_wrt last t /\
    (!x. imm = Var x ==> FLOOKUP H x = NONE) /\
    (tn = entry_taint ==> qt.t_mem = {} /\ qt.t_stor = {} /\ qt.t_trans = {} /\ qt.t_imm = {}) /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule prefix_prepare_payable_layout >> strip_tac >>
  drule prefix_prepare_region_layout >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all prefix_prepare_payable_actual >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choose_then `s1` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `allocas_from lo s1` by (fs[allocas_from_def] >> metis_tac[]) >>
  drule_all prefix_prepare_region_actual >>
  disch_then (qspecl_then [`tn1`,`PG`,`G1`,`D`]
    (qx_choose_then `s2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `!y. not_fresh_at st y ==> not_fresh_at pay y` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexistsl [`s2`,`G2`,`tn2`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[op_prov_def]) >>
  conj_tac >- (strip_tac >> gvs[entry_taint_def]) >>
  metis_tac[abi_decode_sim_trans]
QED
