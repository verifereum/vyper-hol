(* Static and dynamic transports from the selected initializer to its common job. *)
Theory groupedDefaultCutTransport
Ancestors
  groupedEntryCounters entryRejectAllocationIds calldataRegistrationExec groupedInternalLabels
  fragGasPath fragExec venomExecProofs venomState loweringShapeDefs loweringShapeProps loweringShapeRules
  fragFuelCtx fragFuelRuntimeBody fragFuelRuntimePackage exprLoweringProps
  compileEnv emitHelperProps freshLabelStringProps rejectPrefixSourceShape vyperCompiler venomInst arithmetic list pair

Theorem grouped_cut_call_ctx_edge[local]:
  gas_path_edge ctx fn s n (OK t) ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[gas_path_edge_def,exit_result_def] >> rpt strip_tac >> gvs[jump_to_def]
  >- metis_tac[step_inst_ok_preserves_call_ctx]
  >- (drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => once_rewrite_tac[th]) >> simp[] >>
      metis_tac[step_inst_ok_preserves_call_ctx]) >>
  qpat_x_assum `OK t = _` (fn eq => fs[GSYM eq,exit_result_def])
QED

Theorem grouped_cut_call_ctx:
  !ctx fn s n r. gas_path ctx fn s n r ==>
    !t. r = OK t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  ho_match_mp_tac gas_path_ind >> simp[exit_result_def] >>
  metis_tac[grouped_cut_call_ctx_edge]
QED

Theorem grouped_cut_counters:
  compile_entry_checks mincd pay checks = ((),si) /\
  compile_init_kwargs ce vars off k (Lit 0w) si = ((),sb) /\
  emit_inst JMP [Label entry.cs_current_bb] [] sb = ((),term) /\
  ci_mono term dispatch_end /\ ci_mono dispatch_end sd /\
  compile_external_jobs pre sd = ((),js) /\
  new_block entry.cs_current_bb js = (js.cs_current_bb,entry) /\
  compile_register_positional_args (compile_register_kwarg_vars ce vars) args 4 entry = (registered,sa) ==>
  ci_mono checks si /\ ci_mono si sb /\ ci_mono sb sd /\ ci_mono term entry /\
  ci_mono sd entry /\ ci_mono si entry /\ ci_mono sb entry /\ ci_mono checks entry /\ ci_mono entry sa
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono checks si /\ ci_mono si sb /\ ci_mono sb term /\
   ci_mono sd js /\ ci_mono entry sa` by
    metis_tac[compile_entry_checks_ci_mono,compile_init_kwargs_ci_mono,
      ci_mono_emit_inst,compile_external_jobs_ci_mono,registration_compile_ci_mono,SND] >>
  `ci_mono js entry` by
    (drule new_block_props >> strip_tac >> simp[ci_mono_def] >>
     drule_then ACCEPT_TAC cs_extends_new_block) >>
  `ci_mono term sd` by metis_tac[ci_mono_trans] >>
  `ci_mono sb sd` by metis_tac[ci_mono_trans] >>
  `ci_mono sd entry` by metis_tac[ci_mono_trans] >>
  `ci_mono sb entry` by metis_tac[ci_mono_trans] >>
  `ci_mono si entry` by metis_tac[ci_mono_trans] >>
  simp[] >> metis_tac[ci_mono_trans]
QED

Theorem grouped_cut_instruction_bounds:
  fresh_label "fallback" (initial_compile_state "__entry") = (fallback,sf) /\
  groups = MAP (package_external_group tops target trans nkeys) (FST (classify_functions tops)) /\
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
  cs_extends cut sd /\ sd.cs_next_var <= entry.cs_next_var /\ sd.cs_next_id <= entry.cs_next_id ==>
  !i. MEM i (state_insts cut) ==>
    i.inst_opcode <> INVOKE /\ (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
    EVERY (not_fresh_at entry) i.inst_outputs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `state_insts sf = [] /\ shape_state sf` by
    (drule fresh_label_props >> simp[initial_compile_state_def,state_insts_def,all_blocks_def] >>
     strip_tac >> irule shape_state_same_code >> qexists_tac `initial_compile_state "__entry"` >>
     simp[shape_state_initial_compile_state,initial_compile_state_def]) >>
  `jump_label_ok fallback /\ ~label_sfx "dispatch" fallback` by
    (`fresh_label_output "fallback" 0 = fallback` by
       (qpat_assum `fresh_label "fallback" _ = _`
          (mp_tac o AP_TERM ``FST : string # compile_state -> string``) >>
        simp[NoAsms,fresh_label_def,initial_compile_state_def]) >>
     pop_assum (SUBST1_TAC o SYM) >>
     simp[jump_label_ok_def,compiler_label_def,fresh_label_output_in_future,label_sfx_def] >>
     metis_tac[fresh_label_output_inj, EVAL ``"fallback" <> "dispatch"`` |> EQT_ELIM]) >>
  drule_all checked_group_dispatch_shape >> strip_tac >>
  drule_all checked_group_dispatch_safe_opcodes >> strip_tac >>
  drule entry_ids_group_dispatch >> strip_tac >> rpt gen_tac >> disch_tac >>
  `MEM i (state_insts sd)` by metis_tac[state_insts_cs_extends,MEM_APPEND] >>
  qpat_assum `EVERY _ (state_insts sd)` (assume_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
  qpat_assum `entry_alloca_ids sf sd` (strip_assume_tac o REWRITE_RULE [entry_alloca_ids_def]) >>
  qpat_assum `shape_state sd` (strip_assume_tac o REWRITE_RULE [shape_state_def,shape_base_state_def]) >>
  qpat_assum `!i. MEM i (state_insts sd) ==> _ /\ _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac
  >- (strip_tac >>
      qpat_assum `!i. MEM i (state_insts sd) /\ i.inst_opcode = ALLOCA ==> _`
        (qspec_then `i` (drule_all_then strip_assume_tac))
      >- (qpat_assum `MEM i (state_insts sf)` mp_tac >>
          qpat_assum `state_insts sf = []` (fn th => simp_tac bool_ss [th,MEM])) >>
      irule LESS_LESS_EQ_TRANS >> qexists_tac `sd.cs_next_id` >> simp[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
  qexists_tac `sd` >> simp[] >> first_x_assum irule >> qexists_tac `i` >> simp[]
QED
