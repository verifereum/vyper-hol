(* One deployment certificate supplies its own safety cut and event mask. *)
Theory deployUnitExecutionBoundary
Ancestors
  deployUnitExecution deployUnitExitSafe ctorDeployRawEntryFacts ctorDeployDead
  ctorDeployImmBudget ctorDeployMemoryFrontier fragGasOriginEvents fragGasOriginPtr
  fragGasOriginPtrSafeUpto o1SafeUpto unitMemInv o1PassContract
  ctorDeployDefs e2eDeployDefs e2eEntry venomInstProofs venomInst venomState
  list arithmetic

Theorem deploy_certificate_raw_entry_boundary:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es
   vs_out fmp shadow_ctx func gs marks v.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
    deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    v = vs_out with <|vs_gas_readings := gs; vs_fmp := fmp;
                     vs_initial_fmp := fmp|> /\
    deploy_unit_execution_correct_with shadow_ctx marks tops runtime_bc am
      (tx with code := vs_out.vs_code) dunit v /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func ==>
    ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s. raw_reachable v dunit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH marks) (LENGTH gs)) v s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D (imm_len tops) (MIN (LENGTH marks) (LENGTH gs))
        dunit.cu_context v /\
      MAP (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx)
        (gas_events_blocks f dunit.cu_context func
          (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0|>)) = marks ++ extra
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_raw_entry_context_facts >> strip_tac >>
  `v.vs_alloca_next = imm_len tops /\
   v.vs_gas_readings = gs /\ v.vs_initial_fmp = v.vs_fmp` by
    simp[opt_deploy_entry_state_def, opt_entry_state_def, entry_venom_state_def] >>
  `mem_inv dload_headroom_ok dunit.cu_context v` by
    (irule deploy_raw_entry_mem_inv >> metis_tac[]) >>
  `code_layout_valid v` by
    (gvs[] >> irule deploy_raw_entry_code_layout >> metis_tac[]) >>
  qpat_x_assum `v = _` kall_tac >>
  qpat_x_assum `vs_out = _` kall_tac >>
  qpat_x_assum `deploy_unit_execution_correct_with _ _ _ _ _ _ _ _` mp_tac >>
  simp[deploy_unit_execution_correct_with_def] >> strip_tac >> gvs[] >>
  `?bb. lookup_block "__deploy" func.fn_blocks = SOME bb` by
    (gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
     Cases_on `func.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (irule deploy_raw_entry_no_phi >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  all_tac
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- suspend "focus"
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- suspend "focus"
  >> suspend "exit"
QED

Resume deploy_certificate_raw_entry_boundary[focus]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `dead_wf (deploy_dead H tops runtime_bc am (tx with code := vs_out.vs_code))` by
    metis_tac[deploy_dead_wf] >>
  `o1_safe_upto (deploy_dead H tops runtime_bc am (tx with code := vs_out.vs_code))
     (imm_len tops) (MIN (LENGTH marks) (LENGTH v.vs_gas_readings))
     dunit.cu_context v` by
    (irule gas_origin_ptr_focus_o1_safe_upto >> simp[] >> metis_tac[]) >>
  `!fn inst s. raw_reachable v dunit.cu_context fn inst s /\
     gas_cut (MIN (LENGTH marks) (LENGTH v.vs_gas_readings)) v s ==>
     inst_dload_in_section inst s` by
    (drule gas_origin_ptr_focus_dload_upto >> simp[] >> metis_tac[]) >>
  drule gas_origin_ptr_focus_origin >> strip_tac >>
  drule_at (Pat `gas_origin_focus _ _ _ _ _ _`)
    gas_origin_focus_entry_events_prefix >> simp[] >> strip_tac >>
  qexistsl_tac [`deploy_dead H tops runtime_bc am (tx with code := vs_out.vs_code)`,
                `fuel`, `extra`] >> simp[] >> metis_tac[]
QED

Resume deploy_certificate_raw_entry_boundary[exit]:
  rpt strip_tac >>
  drule_all deploy_unit_exit_arm_runs >> strip_tac >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  `imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)` by
    decide_tac >>
  `EVERY pre_fmp_ops dunit.cu_context.ctx_functions` by
    gvs[fmp_free_ctx_def, EVERY_MEM] >>
  `raw_unit_memory_ok dunit.cu_context v` by
    (irule lowered_unit_raw_memory_ok_from >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `mem_inv raw_mem_ok dunit.cu_context v` by
    (qpat_x_assum `raw_unit_memory_ok _ _` mp_tac >>
     simp[unitTransformDefsTheory.raw_unit_memory_ok_def, mem_inv_def,
          raw_mem_ok_def]) >>
  `mem_inv dload_offset_ok dunit.cu_context v` by
    (irule lowered_unit_dload_offset_ok >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ptr_discipline (imm_len tops) dunit.cu_context v /\
   taint_within
     (deploy_dead (storage_trace_horizon obs) tops runtime_bc am
       (tx with code := vs_out.vs_code)) dunit.cu_context v` by
    (irule lowered_unit_ptr_taint >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `o1_safe_upto
     (deploy_dead (storage_trace_horizon obs) tops runtime_bc am
       (tx with code := vs_out.vs_code))
     (imm_len tops) (MIN (LENGTH marks) (LENGTH v.vs_gas_readings))
     dunit.cu_context v` by
    (simp[o1_safe_upto_def, o1_ptr_safe_upto_def,
          ptr_discipline_upto_whole, taint_within_upto_whole] >>
     fs[mem_inv_raw_reachable] >> metis_tac[]) >>
  `!fn inst s. raw_reachable v dunit.cu_context fn inst s ==>
     inst_dload_in_section inst s` by
    (rpt strip_tac >> irule lowered_unit_dload_in_section >> metis_tac[]) >>
  drule_at (Pat `gas_origin_path _ _ _ _ _ _ _`)
    gas_origin_path_entry_events >> simp[] >> strip_tac >>
  qexistsl_tac [`deploy_dead (storage_trace_horizon obs) tops runtime_bc am
                   (tx with code := vs_out.vs_code)`, `fuel'`, `[]`] >>
  simp[deploy_dead_wf] >> metis_tac[]
QED

Finalise deploy_certificate_raw_entry_boundary
