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
