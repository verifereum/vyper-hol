(* Initialize ABI registration from the linked entry's scalar prefix. *)
Theory linkedEntryCheckResources
Ancestors
  defaultEntryResourceInit defaultConcreteRegistrationDefs entryValidatedResources
  entryReachBodyInitialResources entryRegistrationCursorHistory entryReachBodyFmp
  sourceUnitExecutionMods vyperLoweringCorrect loweringStateRelDefs
  allocaFrontierBound allocaFrontierRoom venomWf venomInst venomMemProps
  venomState exprLoweringProps ptrDiscipline fragExec compileEnv finite_map
  contextCodegenRel vyperCompiler moduleLoweringProps
  actualEntryAllocationFrame abiAllocationHistory list arithmetic

Theorem linked_post_checks_resources:
  lowering_context_ok ctx /\ ctx.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" ctx.ctx_functions = SOME fn /\
  initial_venom_state_rel_mods mods am tx initial /\ vars_pc_only initial s /\
  (ctx_has_dalloca ctx ==>
    unit_alloca_budget ctx <= w2n initial.vs_initial_fmp /\
    w2n initial.vs_initial_fmp < 2 ** 254) /\
  compile_entry_checks mc pay opened = ((),checked) /\
  opened.cs_current_insts = [] /\ fn_has_code opened checked fn /\
  fresh_vars_wrt checked s /\ ~s.vs_halted /\
  s.vs_current_bb = checked.cs_current_bb /\
  s.vs_inst_idx = LENGTH checked.cs_current_insts /\
  tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} ==>
  default_registration_resources ctx fn site 0 checked s tn /\
  default_registration_entry_frame initial s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0` by
    (drule vars_pc_only_allocas >>
     drule entry_vars_pc_only_frontier >>
     fs[initial_venom_state_rel_mods_def]) >>
  `alloca_inv s` by (irule alloca_inv_empty >> simp[]) >>
  `alloca_room ctx fn s` by
    (irule validated_entry_alloca_room >> simp[] >>
     qexists_tac `"__entry"` >> simp[]) >>
  `alloca_history fn s` by
    (irule entry_checks_cursor_alloca_history >> simp[] >>
     qexistsl_tac [`mc`,`pay`,`opened`,`checked`] >> simp[]) >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `ctx_wf ctx` by
    (simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, MEM_MAP] >>
     metis_tac[lookup_function_MEM, lookup_function_result_name]) >>
  `alloca_frontier_inv ctx fn site s` by
    (irule entry_root_zero_frontier >> fs[reachable_call_graph_acyclic_def] >>
     qexists_tac `"__entry"` >> simp[]) >>
  `s.vs_fmp = s.vs_initial_fmp /\ s.vs_initial_fmp = initial.vs_initial_fmp` by
    fs[vars_pc_only_def, venom_state_component_equality, initial_venom_state_rel_mods_def] >>
  `fmp_room ctx fn s` by
    (irule entry_frontier_fmp_room >> fs[] >> qexists_tac `site` >> simp[]) >>
  drule_then assume_tac lowering_context_ok_alloca_budget >>
  drule_then assume_tac abi_alloca_history_empty >>
  simp[default_registration_resources_def, default_prefix_entry_frame,
       allocas_from_def, alloca_frontier_inv_from_def, GSYM alloca_frontier_inv_def] >>
  fs[alloca_frontier_inv_def]
QED
