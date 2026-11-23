Theory groupedEntryResources
Ancestors
  selectedAcceptedFold moduleLoweringProps allocaFrontierBound
  allocaBudgetProps venomMemDefs ptrDiscipline venomState finite_map arithmetic
  entryValueRevertPtr entryPtrSeamRegister e2eDefs vyperCompiler
  allocaFrontierRoom loweringStateRelDefs venomInst venomWf venomInstIdsProps words
  vyperLoweringCorrect decoderOriginAllocationFrame
  fragGasOriginPtr fragGasPathPtr fragGasPath exprLoweringProps
  fragGasMode fragGasPathMem fragGasPathFrameMem bodyFullPathHistory allocaHistory
  gasPathPtrExec entryDispatchPtr externalEntryChecks fragGasOrigin fragExec venomMemProofs gasCount

Theorem grouped_entry_resources_vars_pc:
  selected_registration_resources ctx fn site lo sa s /\
  vars_pc_only s t /\ (s.vs_allocas = FEMPTY \/ sa.cs_next_id <= sb.cs_next_id) /\
  fresh_vars_wrt sb t /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  selected_registration_resources ctx fn site lo sb t
Proof
  strip_tac >>
  fs[vars_pc_only_def, venom_state_component_equality, selected_registration_resources_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def, allocas_from_def,
     alloca_frontier_inv_def, remaining_alloca_budget_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem grouped_dispatch_initial_resources:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  st.cs_current_bb = "__entry" /\ st.cs_current_insts = [] /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp) ==>
  selected_registration_resources unit.cu_context fn site 0 st s /\
  s.vs_allocas = FEMPTY /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget unit.cu_context < dimword (:256) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp)
Proof
  strip_tac >>
  `vars_pc_only
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) s` by
    simp[vars_pc_only_def, venom_state_component_equality] >>
  drule_all registration_initial_ptr_resources >>
  disch_then (qspec_then `site` strip_assume_tac) >>
  drule_all initial_entry_dispatch_scalars >>
  disch_then (qspecl_then [`0`,`"__entry"`,`st`] strip_assume_tac) >>
  `fn_inst_ids_distinct fn` by
    (drule registration_runtime_acceptance >> strip_tac >>
     drule lowering_context_ok_static_integrity >> strip_tac >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
       metis_tac[lookup_function_MEM, ctx_inst_ids_distinct_fn] >>
     fs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `selected_registration_resources unit.cu_context fn site 0 st s` by
    simp[selected_registration_resources_def] >>
  `allocas_below_fmp s` by
    (qpat_x_assum `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` SUBST1_TAC >>
     fs[allocas_below_fmp_def, initial_venom_state_rel_def]) >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by simp[] >>
  `ctx_has_dalloca unit.cu_context ==>
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp` by
    (strip_tac >>
     qpat_assum `alloca_frontier_inv _ _ _ _` (mp_tac o REWRITE_RULE [alloca_frontier_inv_def]) >>
     simp[deploy_ctor_pending_alloca_eq] >>
     strip_tac >> res_tac >> decide_tac) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem grouped_entry_frame_vars_pc:
  vars_pc_only s t /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
  u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm ==>
  selected_registration_frame s tn t u /\ t.vs_memory = s.vs_memory
Proof
  simp[vars_pc_only_def, venom_state_component_equality, selected_registration_frame_def]
QED

Theorem grouped_entry_resources_path:
  gas_origin_ptr_path (D,0,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,H,u) /\
  selected_registration_resources ctx fn site 0 sa s /\
  stmt_state_rel horizon ctx fn ce cx ee t /\
  fn_inst_ids_distinct fn /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb t /\
  (!id pair. FLOOKUP t.vs_allocas id = SOME pair ==> id < sb.cs_next_id) ==>
  selected_registration_resources ctx fn site 0 sb t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all decoder_origin_path_allocation_frame >> strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_path_ptr_erase >> disch_tac >>
  drule gas_path_normal >> strip_tac >>
  qpat_x_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
  simp[selected_registration_resources_def, allocas_from_def] >>
  qpat_x_assum `alloca_frontier_inv _ _ _ _` mp_tac >>
  simp[alloca_frontier_inv_def, GSYM deploy_ctor_pending_alloca_eq] >>
  rpt strip_tac >> res_tac
QED

Theorem grouped_entry_origin_continuation:
  gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,FEMPTY,entry_taint)
    marks (OK t,G,tn) /\
  fn_inst_ids_distinct fn /\ s.vs_allocas = FEMPTY /\
  ctx.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\ lookup_block "__entry" fn.fn_blocks = SOME bb /\
  (!l b. lookup_block l fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0) /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> ==>
  gas_path ctx fn s (LENGTH marks) (OK t) /\
  gas_path_mem ctx fn s (LENGTH marks) (OK t) /\
  alloca_history fn t /\ ~t.vs_halted /\
  t.vs_gas_readings = DROP (LENGTH marks) vs.vs_gas_readings /\
  t.vs_code = vs.vs_code /\ t.vs_labels = vs.vs_labels /\
  ((!fuel. ptr_safe_run D 0 fuel ctx fn [] G tn t) ==>
   !fuel. ptr_safe_blocks D 0 fuel ctx fn [] FEMPTY entry_taint s) /\
  !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_context fuel' ctx vs = r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_current_bb = "__entry" /\ s.vs_inst_idx = 0 /\
    s.vs_gas_readings = vs.vs_gas_readings /\ s.vs_code = vs.vs_code /\
    s.vs_labels = vs.vs_labels` by simp[] >>
  qpat_x_assum `s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` (assume_tac o SYM) >>
  `alloca_history fn s /\ alloca_inv s` by
    metis_tac[alloca_history_empty, alloca_inv_empty_proof] >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >> disch_tac >>
  drule gas_path_mem_exec >> simp[exit_result_def] >> strip_tac >>
  `runs_through ctx fn s t` by (simp[runs_through_def] >> metis_tac[]) >>
  `alloca_history fn t` by
    (mp_tac (Q.INST [`G` |-> `FEMPTY`, `G'` |-> `G`, `PG` |-> `[]`,
       `lo` |-> `0`, `tn` |-> `entry_taint`, `tn'` |-> `tn`, `func` |-> `fn`,
       `u` |-> `t`] body_full_path_alloca_history) >>
     asm_rewrite_tac[]) >>
  drule gas_path_code_labels >> simp[] >> strip_tac >>
  drule gas_path_suffix >> simp[gas_count_suffix_def] >> disch_tac >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (strip_tac >>
      `!fuel. ptr_safe_run D 0 fuel ctx fn [] FEMPTY entry_taint s` by
        (mp_tac (Q.SPECL [`D`,`0`,`ctx`,`fn`,`[]`,`FEMPTY`,`entry_taint`,
           `s`,`LENGTH (marks:bool list)`,`G`,`tn`,`t`] gas_path_ptr_safe_run) >>
         asm_rewrite_tac[] >> metis_tac[]) >>
      irule ptr_safe_blocks_from_phi_free_run >> asm_rewrite_tac[] >>
      qexists_tac `bb` >> metis_tac[]) >>
  mp_tac (Q.SPECL [`ctx`,`fn`,`vs`,`t`,`bb`] entry_context_continuation) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
