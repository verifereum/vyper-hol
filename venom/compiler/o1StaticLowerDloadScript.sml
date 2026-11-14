Theory o1StaticLowerDload
Ancestors
  o1ContractLowerDloadStage o1PassContract unitTransformDefs lowerDloadDefs
  venomPassSchedule o1ContractLowerDloadSim o1ContractLowerDloadMem
  o1ContractLowerDloadTaint o1ContractLowerDloadPtr ptrDiscipline

(* LowerDload preserves instruction order. The static guards compare the
   flags of related states; they do not require an initially nonstatic call. *)
Theorem o1_static_stage_lower_dload:
  !C C' vs.
    ctx_pass_stage rpolicy (EL 1 o1_fn_passes) (o1_walk_view rpolicy 1) C C' /\
    o1_pre 1 C C' /\ dead_wf D /\ o1_ctx_shape C /\
    o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
    code_layout_valid vs /\ o1_inv D 1 C vs ==>
    ctx_sim_fuel (pass_fuel (EL 1 o1_fn_passes) C') D C C' vs vs /\
    o1_inv D (SUC 1) C' vs
Proof
  simp[o1_fn_passes_def, o1_inv_def, pass_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  `ctx_sim_fuel I D C C' vs vs` by
    metis_tac[lower_dload_stage_sim_fuel_static] >>
  `mem_inv raw_mem_ok C' vs` by metis_tac[lower_dload_stage_mem_static] >>
  `taint_within D C' vs` by metis_tac[lower_dload_stage_taint_static] >>
  `mem_inv dload_offset_ok C' vs` by
    (irule lower_dload_stage_dload_ok_static >> fs[o1_src_inv_def] >>
     metis_tac[]) >>
  `mem_inv dload_headroom_ok C' vs` by
    metis_tac[lower_dload_stage_headroom] >>
  `EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C'` by
    (irule lower_dload_stage_shape >> fs[o1_src_inv_def] >> metis_tac[]) >>
  `fmp_free_ctx C'` by
    (irule lower_dload_stage_fmp_free >> fs[o1_src_inv_def] >> metis_tac[]) >>
  `callee_first names C'.ctx_functions` by
    metis_tac[lower_dload_stage_callee_first] >>
  `EVERY make_ssa_input_ok C'.ctx_functions` by
    (irule lower_dload_stage_make_ssa_input_ok >> fs[o1_src_inv_def] >>
     metis_tac[]) >>
  `EVERY ssa_form C'.ctx_functions` by
    metis_tac[lower_dload_stage_ssa_form] >>
  fs[o1_src_inv_def] >>
  `ptr_discipline lo C' vs` by
    (irule lower_dload_stage_ptr_static >> simp[o1_src_inv_def] >> metis_tac[]) >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by fs[ctx_pass_stage_def] >>
  fs[fixed_region_reserved_def] >> metis_tac[]
QED
