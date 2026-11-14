(* Resource initialization at the common post-check endpoint. *)
Theory defaultEntryResourceInit
Ancestors
  defaultConcreteRegistrationDefs defaultEntryPrefix defaultDispatchFacts
  entryValidatedResources entryReachBodyInitialResources entryReachBodyFmp
  entryRegistrationCursorHistory entryValueRevertPtr acceptedContextPhi
  ctorDeployMemoryFrontier allocaFrontierBound vyperLoweringCorrect
  vyperCompiler venomWf fcgDefs moduleLoweringProps compileEnv finite_map
  venomMemProps abiAllocationHistory exprLoweringProps
  venomInstProofs1 contextCodegenRel list ptrDiscipline venomInst arithmetic
  externalEntryChecks moduleLowering emitHelperProps entryDispatchProps
  sourceValueRejection vyperContext vyperInterpreter loweringStateRelDefs
  rich_list fragExec venomInstIdsProps

Theorem default_prefix_entry_frame:
  vars_pc_only initial s ==> default_registration_entry_frame initial s
Proof
  rw[vars_pc_only_def, default_registration_entry_frame_def] >>
  pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

Theorem default_post_checks_resources:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ initial_venom_state_rel tops am tx initial /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  vars_pc_only initial s /\
  compile_entry_checks mc pay sc = ((),st) /\ sc.cs_current_insts = [] /\
  fn_has_code sc st fn /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} ==>
  default_registration_resources unit.cu_context fn site 0 st s tn /\
  default_registration_entry_frame initial s
Proof
  strip_tac >>
  drule_all entry_checks_start_allocation_resources >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >> gvs[] >>
  `alloca_room unit.cu_context fn s` by
    (irule validated_entry_alloca_room >> simp[] >> metis_tac[]) >>
  `alloca_history fn s` by
    (irule entry_checks_cursor_alloca_history >> simp[] >>
     qexistsl [`mc`, `pay`, `sc`, `st`] >> simp[]) >>
  `fmp_room unit.cu_context fn s` by
    (irule entry_runtime_fmp_room >> metis_tac[lookup_function_MEM]) >>
  `ctx_wf unit.cu_context` by
    (drule lowering_context_ok_integrity >> strip_tac >>
     drule lowering_context_ok_bridge >> strip_tac >>
     simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, MEM_MAP] >>
     metis_tac[lookup_function_MEM, lookup_function_result_name]) >>
  `alloca_frontier_inv unit.cu_context fn site s` by
    (irule entry_root_zero_frontier >> goal_assum $ drule_at Any >> simp[] >>
     metis_tac[lowering_context_ok_integrity, lowering_context_ok_bridge,
       reachable_call_graph_acyclic_def]) >>
  simp[default_registration_resources_def, default_prefix_entry_frame,
       allocas_from_def, alloca_frontier_inv_from_def, GSYM alloca_frontier_inv_def] >>
  drule lowering_context_ok_alloca_budget >>
  gvs[alloca_frontier_inv_def] >> decide_tac
QED

Theorem default_external_bodies_next_var:
  !packages sa sb. compile_external_fn_bodies packages sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  Induct >- simp[compile_external_fn_bodies_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac std_ss [compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `new_block h0 sa` >>
  rename1 `new_block h0 sa = (old,s1)` >> simp[] >>
  Cases_on `compile_entry_checks h3 h4 s1` >>
  rename1 `compile_entry_checks h3 h4 s1 = (u,s2)` >>
  Cases_on `u` >> simp[] >>
  Cases_on `compile_external_function_body h1 h2 h5 h6 h7 h8 h9 h10 s2` >>
  rename1 `compile_external_function_body _ _ _ _ _ _ _ _ _ = (u,s3)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule new_block_props >> strip_tac >>
  drule compile_entry_checks_next_var >> strip_tac >>
  drule compile_external_function_body_next_var >> strip_tac >> decide_tac
QED

(* Compiler placement is an explicit interface input. Both selected and fallback
   placements exported by default_dispatch_cases have this form; packages is
   respectively the selected prefix or all external packages. *)
Theorem default_entry_prefix_resources:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) /\
  sels = MAP (\(sel,lbl,z). (sel,lbl))
    (build_selectors (type_env tops) (FST (classify_functions tops))) /\
  compile_selector_dispatch_linear sels fallback ds = ((),de) /\
  fn_has_code ds de fn /\ ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\
  cs_extends de opened /\
  compile_external_fn_bodies packages de = ((),before) /\
  new_block (linear_dispatch_target vs.vs_call_ctx.cc_calldata sels fallback)
    before = (before.cs_current_bb,opened) /\
  compile_entry_checks mc pay opened = ((),st) /\ fn_has_code opened st fn /\
  cs_extends opened st /\ pay = (mut = Payable) /\
  (mc <= 4 \/ mc <= LENGTH vs.vs_call_ctx.cc_calldata) ==>
  ?s G tn.
    gas_path_mem unit.cu_context fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>)
      0 (OK s) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>,
       FEMPTY,entry_taint) [] (OK s,G,tn)) /\
    vars_pc_only
      (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) s /\
    default_registration_resources unit.cu_context fn site 0 st s tn /\
    default_registration_entry_frame vs s /\
    (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] G tn s) ==>
      !fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>))
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >> gvs[] >>
  `~ctx_has_dalloca unit.cu_context` by metis_tac[entry_runtime_no_dalloca] >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn_inst_ids_distinct fn` by
    (`ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
       metis_tac[ctx_inst_ids_distinct_fn, lowering_context_ok_static_integrity] >>
     gvs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  drule new_block_props >> strip_tac >>
  `de.cs_next_var <= opened.cs_next_var` by
    (drule default_external_bodies_next_var >> simp[]) >>
  `?bb. lookup_block opened.cs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[fn_has_code_start] >>
  `!bb. lookup_block opened.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lowering_context_ok_block_phi] >>
  qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
    assume_tac linear_selectors_lt >>
  drule_all initial_entry_dispatch_scalars >>
  disch_then (qspecl_then [`0`, `ds.cs_current_bb`, `ds`] strip_assume_tac) >>
  `mut = Payable \/ vs.vs_call_ctx.cc_callvalue = 0w` by
    (drule send_call_value_success_condition >>
     simp[initial_evaluation_context_def] >> strip_tac >>
     fs[initial_venom_state_rel_def, venom_env_rel_def, call_ctx_rel_def]) >>
  drule default_entry_prefix_joint >>
  disch_then (qspecl_then [`st`,
    `vs with <|vs_prev_bb := NONE; vs_current_bb := ds.cs_current_bb; vs_inst_idx := 0|>`,
    `mut = Payable`, `opened`, `mc`, `fn`, `unit.cu_context`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only _ s` >>
  `vars_pc_only vs s` by
    (irule vars_pc_only_trans >>
     qexists_tac `vs with <|vs_prev_bb := NONE; vs_current_bb := ds.cs_current_bb; vs_inst_idx := 0|>` >>
     simp[] >> simp[vars_pc_only_def]) >>
  drule_all default_post_checks_resources >> strip_tac >>
  qexistsl [`s`, `G2`, `tn2`] >> simp[]
QED
