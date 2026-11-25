(* The runtime certificate supplies the raw entry facts used by replay. *)
Theory linkedRuntimeCertificateFocus
Ancestors
  sourceUnitExecutionMods linkedRawUnitShape linkedUnitMemory
  e2eCorrectness e2eComposition ctorDeployMemoryFrontier
  ptrOkCheck acceptedContextPhi fragGasOriginPtrSafeUpto
  fragGasOriginEvents o1SafeUpto o1PipelineCompose o1PassContract
  unitMemInv unitTransformDefs staticLayoutDefs vyperStorageFootprint
  venomInst venomState list
  vyperCompiler ptrDiscipline sourceUnitExecution vyperInterpreter vyperLoweringCorrect

Theorem linked_runtime_certificate_raw_entry_boundary:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  o1_source_unit_ok unit /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp) /\
  initial_venom_state_rel_mods mods am tx vs /\ code_layout_valid vs /\
  source_unit_execution_correct_with_mods shadow_ctx marks mods exps ret am tx unit vs /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func ==>
  ?D fuel extra.
    dead_wf D /\
    (!fn inst s. raw_reachable vs unit.cu_context fn inst s /\
       gas_cut (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings)) vs s ==>
       inst_dload_in_section inst s) /\
    o1_safe_upto D 0 (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings))
      unit.cu_context vs /\
    MAP (\key. key IN gas_explicit_sites unit.cu_context shadow_ctx)
      (gas_events_blocks fuel unit.cu_context func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0|>)) = marks ++ extra
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_raw_shape_mods >> strip_tac >>
  drule lower_vyper_runtime_unit_global_reserved_mods >> strip_tac >>
  drule vyperCompilerTheory.lowering_context_ok_bridge >> strip_tac >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[EVERY_MEM] >>
  `ptr_ok_check unit.cu_context` by fs[lowering_context_ok_def] >>
  drule_then assume_tac ptr_ok_check_sound >>
  drule_all_then assume_tac source_fmp_free >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved /\
   fixed_region_reserved 0 unit.cu_context` by
    simp[reserved_intervals_wf_def, fixed_region_reserved_def] >>
  `w2n vs.vs_initial_fmp <= w2n vs.vs_fmp` by
    fs[initial_venom_state_rel_mods_def] >>
  drule_all_then assume_tac lower_vyper_runtime_unit_dload_headroom_ok_mods >>
  `!H:(bool # bytes32 # type_value) list # num list.
     dead_wf (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))` by
    (gen_tac >> simp[cx_dead_def, initial_evaluation_context_def] >>
     MATCH_ACCEPT_TAC
       (SIMP_RULE (srw_ss()) [external_call_dead_def]
         (Q.INST [`src` |-> `(INL NoneV, am, [])`] external_call_dead_wf))) >>
  qpat_x_assum `source_unit_execution_correct_with_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[source_unit_execution_correct_with_mods_def] >> strip_tac >> gvs[] >>
  rename1 `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func` >>
  `?bb. lookup_block "__entry" func.fn_blocks = SOME bb` by
    (qpat_x_assum `fn_entry_label func = SOME "__entry"` mp_tac >>
     Cases_on `func.fn_blocks` >>
     simp[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  drule_all_then assume_tac lowering_context_ok_block_phi >>
  all_tac
  >~ [`gas_origin_ptr_focus _ _ _ _`] >- suspend "focus"
  >~ [`gas_origin_ptr_focus _ _ _ _`] >- suspend "focus"
  >> suspend "exit"
QED

Resume linked_runtime_certificate_raw_entry_boundary[focus]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `D = cx_dead H
    (initial_evaluation_context am.sources am.layouts tx NONE)` >>
  `dead_wf D` by
    (simp[Abbr `D`] >>
     first_assum (fn th => ACCEPT_TAC (Q.SPEC `H` th))) >>
  `o1_safe_upto D 0 (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings))
     unit.cu_context vs` by
    (irule gas_origin_ptr_focus_o1_safe_upto >>
     simp[reserved_intervals_wf_def] >> metis_tac[]) >>
  `!fn inst s. raw_reachable vs unit.cu_context fn inst s /\
     gas_cut (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings)) vs s ==>
     inst_dload_in_section inst s` by
    (drule gas_origin_ptr_focus_dload_upto >>
     simp[reserved_intervals_wf_def] >> metis_tac[]) >>
  drule_then assume_tac fragGasOriginPtrTheory.gas_origin_ptr_focus_origin >>
  drule_at (Pat `gas_origin_focus _ _ _ _ _ _`) gas_origin_focus_entry_events_prefix >>
  simp[] >> strip_tac >>
  qexistsl_tac [`D`, `fuel`, `extra`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume linked_runtime_certificate_raw_entry_boundary[exit]:
  drule_all_then strip_assume_tac e2eCorrectnessTheory.selected_run >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) (storage_trace_horizon obs) obs` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon obs` mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_safe_blocks D` >>
  qspecl_then [`mods`, `exps`, `rp`, `unit`, `vs`, `func`, `"__entry"`, `D`]
    mp_tac lower_vyper_runtime_unit_ptr_taint_mods >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then strip_assume_tac >>
  `raw_unit_memory_ok unit.cu_context vs` by
    (Cases_on `ctx_has_dalloca unit.cu_context`
     >- (`!f inst s. raw_reachable vs unit.cu_context f inst s ==>
             dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
           (qspecl_then [`0`, `unit.cu_context`, `"__entry"`, `func`, `"__entry"`, `vs`]
              mp_tac lowered_unit_checked_dalloca_facts >> asm_rewrite_tac[]) >>
         qspecl_then [`mods`, `exps`, `rp`, `unit`, `am`, `tx`,
                      `vs`, `func`, `"__entry"`, `D`]
           mp_tac lower_vyper_runtime_unit_memory_ok_from_no_wrap_mods >>
         impl_tac >- asm_rewrite_tac[] >> simp[]) >>
     qspecl_then [`mods`, `exps`, `rp`, `unit`, `am`, `tx`,
                  `vs`, `func`, `"__entry"`, `D`]
       mp_tac lower_vyper_runtime_unit_memory_ok_mods >> simp[]) >>
  `mem_inv dload_offset_ok unit.cu_context vs` by
    (qspecl_then [`mods`, `exps`, `rp`, `unit`, `vs`, `func`, `"__entry"`]
       mp_tac lower_vyper_runtime_unit_dload_offset_ok_mods >> simp[]) >>
  `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
            s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
     unit.cu_context vs` by
    (qspecl_then [`mods`, `exps`, `rp`, `unit`, `vs`, `func`, `"__entry"`]
       mp_tac lower_vyper_runtime_unit_dload_in_section_mods >> simp[]) >>
  `mem_inv raw_mem_ok unit.cu_context vs` by
    (PURE_REWRITE_TAC [mem_inv_def, raw_mem_ok_def] >>
     qpat_assum `raw_unit_memory_ok _ _`
       (ACCEPT_TAC o PURE_REWRITE_RULE [raw_unit_memory_ok_def])) >>
  `o1_src_inv D unit.cu_context vs` by
    (simp[o1_src_inv_def, reserved_intervals_wf_def] >> qexists_tac `0` >> asm_rewrite_tac[]) >>
  `!n. o1_safe_upto D 0 n unit.cu_context vs` by
    (irule o1_src_inv_ptr_safe_upto >> asm_rewrite_tac[]) >>
  drule_at (Pat `gas_origin_path _ _ _ _ _ _ _`)
    gas_origin_path_entry_events >> simp[] >>
  disch_then (qx_choose_then `event_fuel` assume_tac) >>
  qexistsl_tac [`D`, `event_fuel`, `[]`] >>
  simp[Abbr `D`] >>
  rpt strip_tac >>
  qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ _`
    (drule o CONJUNCT2 o REWRITE_RULE [mem_inv_raw_reachable]) >>
  simp[]
QED

Finalise linked_runtime_certificate_raw_entry_boundary
