Theory concretizePtrActivationSupport
Ancestors concretizePtrRootCover concretizePtrFrameOrigins concretizePtrClosure
  concretizePtrRuntimeOrigins pointerClosure pointerConfinedDefs
  ptrDiscipline venomInst finite_map pred_set list
  concretizePtrAllocationOrigins venomMemProps venomExecSemantics
  ptrDisciplineEmptyTaint venomState

Theorem ptr_frame_roots_extend:
  (!aid p. FLOOKUP A aid = SOME p ==> FLOOKUP B aid = SOME p) ==>
  ptr_frame_site_roots fn A PG site SUBSET ptr_frame_site_roots fn B PG site
Proof
  simp[SUBSET_DEF, ptr_frame_site_roots_def] >> metis_tac[]
QED

Theorem ptr_frame_support_extend:
  (!aid p. FLOOKUP A aid = SOME p ==> FLOOKUP B aid = SOME p) /\
  ptr_site_supported (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site ==>
  ptr_site_supported (pointer_derived_vars fn (ptr_frame_site_roots fn B PG site)) G site
Proof
  strip_tac >>
  `pointer_derived_vars fn (ptr_frame_site_roots fn A PG site) SUBSET
   pointer_derived_vars fn (ptr_frame_site_roots fn B PG site)` by
    (irule ptr_derived_mono >> simp[ptr_frame_site_roots_finite] >>
     metis_tac[ptr_frame_roots_extend]) >>
  fs[ptr_site_supported_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_site_support_restrict:
  ptr_site_supported X G site ==> ptr_site_supported X (DRESTRICT G keys) site
Proof
  simp[ptr_site_supported_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ptr_step_allocas_extend:
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' ==>
  !aid p. FLOOKUP s.vs_allocas aid = SOME p ==>
    FLOOKUP s'.vs_allocas aid = SOME p
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
      metis_tac[exec_alloca_lookup_preserved]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  metis_tac[step_inst_non_alloca_preserves_allocas]
QED

Theorem ptr_frame_current_table_step:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s'.vs_allocas PG site))
    (step_prov PG G inst s') site
Proof
  strip_tac >> irule ptr_frame_site_step >> simp[] >>
  irule ptr_frame_support_extend >>
  goal_assum (drule_at Any) >> metis_tac[ptr_step_allocas_extend]
QED

Theorem ptr_frame_current_table_entry:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site /\
  enters_block fn s s1 ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s1.vs_allocas PG site))
    (entry_prov fn s G) site
Proof
  strip_tac >> drule enters_block_allocas >> strip_tac >> simp[] >>
  metis_tac[ptr_frame_site_entry]
QED

Theorem ptr_return_allocas:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state saved ended)) = SOME s' ==>
  s'.vs_allocas = saved.vs_allocas
Proof
  strip_tac >> drule bind_outputs_allocation_frame >>
  simp[merge_callee_state_allocas]
QED

Theorem ptr_frame_table_support_invariant:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions ==>
    MEM fn ctx.ctx_functions /\
    (!site. ptr_site_supported
      (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site) /\
    EVERY (\f. MEM f.cf_fn ctx.ctx_functions /\ !site. ptr_site_supported
      (pointer_derived_vars f.cf_fn
        (ptr_frame_site_roots f.cf_fn f.cf_state.vs_allocas f.cf_params site))
      f.cf_prov site) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> simp[ptr_site_supported_def] >> metis_tac[lookup_function_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `EVERY _ _ ==> _` mp_tac >> simp[] >> strip_tac >>
      `MEM inst (fn_insts fn)` by
        (gvs[contextCodegenRelTheory.active_inst_def, fn_insts_def,
          venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[MEM_EL]) >>
      simp[] >> gen_tac >> irule ptr_frame_current_table_step >>
      fs[EVERY_MEM] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `EVERY _ _ ==> _` mp_tac >> simp[] >> strip_tac >>
      `~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, is_alloca_op_def]) >>
      `s'.vs_allocas = s.vs_allocas` by
        metis_tac[step_inst_non_alloca_preserves_allocas] >>
      simp[] >> gen_tac >> irule ptr_frame_current_table_entry >> simp[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `EVERY _ _ ==> _` mp_tac >> simp[] >> strip_tac >>
      simp[ptr_site_supported_def] >> metis_tac[lookup_function_MEM])
  >> rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `EVERY _ _ ==> _` mp_tac >> simp[] >> strip_tac >>
  `s'.vs_allocas = f.cf_state.vs_allocas` by metis_tac[ptr_return_allocas] >>
  simp[] >> metis_tac[ptr_site_support_restrict]

QED

Theorem ptr_frame_current_table_support:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions ==>
  !site. ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site
Proof metis_tac[ptr_frame_table_support_invariant]
QED

Theorem ptr_frame_saved_table_support:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  n < LENGTH stk ==>
  !site. ptr_site_supported
    (pointer_derived_vars (EL n stk).cf_fn
      (ptr_frame_site_roots (EL n stk).cf_fn (EL n stk).cf_state.vs_allocas
        (EL n stk).cf_params site)) (EL n stk).cf_prov site
Proof
  strip_tac >> drule ptr_frame_table_support_invariant >> simp[EVERY_EL] >>
  metis_tac[]
QED

Theorem ptr_frame_production_singleton_write_site:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v =
    [Ptr (Allocation aid) off] /\ FLOOKUP G v = SOME site ==>
  FLOOKUP s.vs_allocas aid = SOME site
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions /\ ptr_params_ok P fn PG` by
    metis_tac[concretizePtrParamSupportTheory.ptr_frame_current_static] >>
  `ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site` by
    metis_tac[ptr_frame_current_table_support] >>
  irule ptr_param_supported_production_singleton_write_site >>
  fs[EVERY_MEM] >> metis_tac[]
QED
