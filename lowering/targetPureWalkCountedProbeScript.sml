(* Counted execution interfaces for the zero-index candidate. *)
Theory targetPureWalkCountedProbe
Ancestors
  targetPureWalkSimulationProbe fragGasMode fragGasPath gasCount
  venomExecSemantics venomInst venomState compileEnv list
  exprSimArrayIndex fragGasFresh freshWrites varsExt sourceValueFrames
  emitHelper fragExec loweringStateRelDefs finite_map

Theorem simulation_probe_invoke_count:
  !s id. gas_count_step 1 simulation_probe_context
    (mk_inst id INVOKE [Label simulation_probe_label] []) s = 0
Proof
  rpt gen_tac >>
  simp[Once gas_count_step_def, mk_inst_def, decode_invoke_def,
       simulation_probe_context_def, simulation_probe_callee_def,
       mk_venom_context_def, mk_raw_function_def, lookup_function_def,
       FIND_thm, eval_operands_def, setup_callee_def] >>
  simp[Once gas_count_blocks_def, lookup_block_def, FIND_thm,
       eval_phis_def, phi_prefix_length_def] >>
  simp[Once gas_count_block_def, get_instruction_def] >>
  simp[Once gas_count_step_def, is_terminator_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs,
       eval_operands_def, eval_operand_def] >>
  qmatch_goalsub_abbrev_tac `run_block_non_phis 0 cc bb st` >>
  qabbrev_tac `rr = run_block_non_phis 0 cc bb st` >>
  qpat_x_assum `Abbrev (rr = _)` (K all_tac) >>
  Cases_on `rr` >> simp[Once gas_count_blocks_def]
QED

Theorem simulation_probe_invoke_edge:
  !fn s bb id.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id INVOKE [Label simulation_probe_label] []) ==>
    gas_path_edge simulation_probe_context fn s 0
      (OK (s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >> simp[gas_path_edge_def] >>
  qexists_tac `1` >>
  simp[simulation_probe_invoke_restores, simulation_probe_invoke_count,
       mk_inst_def, is_terminator_def]
QED

Theorem simulation_probe_array_path:
  !sa sb p loader ctx fn cenv cx es s w.
    compile_array_subscript (Var "a_ptr") (Lit 0w) F 1 32 32 F loader sa =
      (p,sb) /\ fn_has_code sa sb fn /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
    not_fresh_at sa "a_ptr" /\ eval_operand (Var "a_ptr") s = SOME w /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      eval_operand p t = SOME w /\ stmt_state_rel ctx fn cenv cx es t /\
      (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
        lookup_var z t = SOME v) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  `straight_fresh (compile_array_subscript (Var "a_ptr") (Lit 0w)
      F 1 32 32 F loader)` by
    (rewrite_tac[compile_array_subscript_split] >> simp[] >>
     irule straight_fresh_bind >> simp[straight_fresh_return] >>
     gen_tac >> irule straight_fresh_array_check_ptr) >>
  `eval_operand (Var "a_ptr") (drop_fresh sa s) = SOME w` by
    simp[eval_operand_drop_fresh] >>
  drule compile_array_subscript_ok >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh, eval_operand_def, array_len_ok_def,
       idx_in_range_def] >>
  strip_tac >>
  gvs[] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[wordsTheory.WORD_MULT_CLAUSES]
QED

Theorem simulation_probe_emit_path:
  !sa sm fn s.
    emit_void INVOKE [Label simulation_probe_label] sa = ((),sm) /\
    fn_has_code sa sm fn /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_marked_path F simulation_probe_context fn s 0
      (OK (s with vs_inst_idx := LENGTH sm.cs_current_insts))
Proof
  rpt strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   sm.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id INVOKE [Label simulation_probe_label] []]` by
    (gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `gas_path_edge simulation_probe_context fn s 0
      (OK (s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule simulation_probe_invoke_edge >> simp[] >> metis_tac[]) >>
  simp[gas_marked_path_def] >>
  `gas_path simulation_probe_context fn
      (s with vs_inst_idx := SUC s.vs_inst_idx) 0
      (OK (s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_rules) >> simp[]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[arithmeticTheory.ADD1]
QED

Theorem simulation_probe_counted_split:
  !sa sm sb p loader fn cx es s w.
    emit_void INVOKE [Label simulation_probe_label] sa = ((),sm) /\
    compile_array_subscript (Var "a_ptr") (Lit 0w) F 1 32 32 F loader sm = (p,sb) /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    local_ptrs_reserved simulation_probe_cenv sm /\
    stmt_state_rel simulation_probe_context fn simulation_probe_cenv cx es s /\
    not_fresh_at sm "a_ptr" /\ eval_operand (Var "a_ptr") s = SOME w /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F simulation_probe_context fn s 0 (OK t) /\
      eval_operand p t = SOME w /\
      stmt_state_rel simulation_probe_context fn simulation_probe_cenv cx es t /\
      (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
        lookup_var z t = SOME v) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  drule_all simulation_probe_emit_path >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
  `stmt_state_rel simulation_probe_context fn simulation_probe_cenv cx es
    (s with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  `eval_operand (Var "a_ptr")
     (s with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME w` by
    fs[eval_operand_def, lookup_var_def] >>
  `~(s with vs_inst_idx := LENGTH sm.cs_current_insts).vs_halted /\
   (s with vs_inst_idx := LENGTH sm.cs_current_insts).vs_current_bb = sm.cs_current_bb /\
   (s with vs_inst_idx := LENGTH sm.cs_current_insts).vs_inst_idx = LENGTH sm.cs_current_insts` by simp[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ s` kall_tac >>
  qpat_x_assum `eval_operand _ s = _` kall_tac >>
  drule_all simulation_probe_array_path >>
  strip_tac >> qexists_tac `t` >> simp[lookup_var_def] >>
  drule_all gas_marked_path_then >> simp[]
QED

Theorem simulation_probe_counted_target:
  !sa sb op fn cx env es s entry.
    compile_get_target_ptr compile_expr simulation_probe_cenv
      module_probe_target sa = (op,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved simulation_probe_cenv sa /\
    stmt_state_rel simulation_probe_context fn simulation_probe_cenv cx es s /\
    lookup_scopes "a" es.scopes = SOME entry /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t p w. op = (p,SOME LocMemory,SOME (ValPT (BaseT (UintT 256)))) /\
      eval_operand (Var "a_ptr") s = SOME w /\ eval_operand p t = SOME w /\
      gas_marked_path F simulation_probe_context fn s 0 (OK t) /\
      stmt_state_rel simulation_probe_context fn simulation_probe_cenv cx es t /\
      (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
        lookup_var z t = SOME v) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  rewrite_tac[simulation_probe_compile_target, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `emit_void INVOKE [Label simulation_probe_label] sa` >>
  rename1 `emit_void INVOKE _ sa = (u,sm)` >>
  Cases_on `compile_array_subscript (Var "a_ptr") (Lit 0w) F 1 32 32 F
    (compile_ptr_load F simulation_probe_cenv.ce_imm_alloca LocMemory) sm` >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `compile_array_subscript _ _ _ _ _ _ _ _ sm = (p,sb)` >>
  `sm.cs_next_var = sa.cs_next_var /\ sm.cs_current_bb = sa.cs_current_bb /\
   cs_extends sa sm` by
    gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def,
        cs_extends_def, emitted_blocks_def] >>
  `straight_fresh (compile_array_subscript (Var "a_ptr") (Lit 0w) F 1 32 32 F
      (compile_ptr_load F simulation_probe_cenv.ce_imm_alloca LocMemory))` by
    (rewrite_tac[compile_array_subscript_split] >> simp[] >>
     irule straight_fresh_bind >> simp[straight_fresh_return] >>
     gen_tac >> irule straight_fresh_array_check_ptr) >>
  `cs_extends sm sb` by
    (qpat_assum `straight_fresh _` mp_tac >>
     rewrite_tac[straight_fresh_def] >>
     disch_then drule >> strip_tac >>
     simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved simulation_probe_cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sm "a_ptr"` by
    (fs[local_ptrs_reserved_def, simulation_probe_cenv_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `?w. eval_operand (Var "a_ptr") s = SOME w` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
        local_ptrs_rel_def, simulation_probe_cenv_def, FLOOKUP_UPDATE] >>
     res_tac >> fs[eval_operand_def]) >>
  drule_all simulation_probe_counted_split >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  fs[not_fresh_at_def]
QED
