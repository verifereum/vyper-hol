(*
 * MakeSSA's first O1 run keeps the pointer discipline above the same
 * fixed region.  It renames variables and adds PHIs and ASSIGNs between
 * them, and touches no memory operation.
 *)
Theory o1ContractMakeSsaPtr
Ancestors
  o1PassContract ptrDiscipline unitMemInv venomPassSchedule list makeSsaCurrentOrigin
  makeSsaCurrentLockstep makeSsaCurrentSim makeSsaCurrentProps
  makeSsaCurrentRevertForward o1ContractMakeSsaReplay o1PassLift
  o1FrameLockstep unitTransformDefs contextCodegenRel
  o1ContractMakeSsaPtrOk o1ContractMakeSsaPtrRows o1ContractMakeSsaPtrPos

Theorem make_ssa_stage_ptr:
  !rpolicy D view C C' vs names lo.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ EVERY make_ssa_input_ok C.ctx_functions /\
    callee_first names C.ctx_functions /\
    fixed_region_reserved lo C /\ ptr_discipline lo C vs ==>
    ptr_discipline lo C' vs
Proof
  rpt strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `~ctx_has_dalloca C` by gvs[o1_src_inv_def] >>
  `C'.ctx_entry = C.ctx_entry /\
   LIST_REL (\fn fn'. ?t t'.
     ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
     make_ssa_current_fn t fn = (fn',t'))
     C.ctx_functions C'.ctx_functions` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     simp[ctx_pass_stage_def] >> strip_tac >> simp[] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[] >> drule make_ssa_pass_step_replay >> simp[]) >>
  `LENGTH C'.ctx_functions = LENGTH C.ctx_functions` by
    metis_tac[LIST_REL_LENGTH] >>
  `!n. n < LENGTH C.ctx_functions ==>
     make_ssa_input_ok (EL n C.ctx_functions) /\
     fn_inst_wf (EL n C.ctx_functions) /\
     wf_function (EL n C.ctx_functions) /\
     first_block_no_preds (EL n C.ctx_functions) /\
     first_block_no_phi (EL n C.ctx_functions) /\
     ?t t'. ir_supply_covers_fn t (EL n C.ctx_functions) /\
       ir_supply_inst_ok t /\
       make_ssa_current_fn t (EL n C.ctx_functions) =
         (EL n C'.ctx_functions,t')` by
    (rpt strip_tac >>
     `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
     `o1_fn_shape C (EL n C.ctx_functions) /\
      make_ssa_input_ok (EL n C.ctx_functions)` by
       metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
     gvs[o1_fn_shape_def, LIST_REL_EL_EQN]) >>
  `!n. n < LENGTH C.ctx_functions ==>
     fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions)` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     irule make_ssa_current_fn_fn_bisim >> gvs[make_ssa_input_ok_def] >>
     metis_tac[]) >>
  `ctx_bisim C C'` by
    (irule fn_bisim_ctx_bisim >> simp[LIST_REL_EL_EQN]) >>
  qabbrev_tac `Q = \fn fn' pos.
     pos = make_ssa_pos fn fn' /\
     make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
     first_block_no_preds fn /\ first_block_no_phi fn /\
     ?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
            make_ssa_current_fn t fn = (fn',t')` >>
  `lockstep_ctx Q vs.vs_labels C C'` by
    (simp[lockstep_ctx_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
     `fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions)` by
       metis_tac[] >>
     fs[fn_bisim_def] >>
     first_x_assum drule >> strip_tac >>
     qexists `make_ssa_pos (EL n C.ctx_functions) (EL n C'.ctx_functions)` >>
     simp[Abbr `Q`] >>
     irule make_ssa_current_fn_frame_lockstep >> metis_tac[]) >>
  `~ctx_has_dalloca C'` by
    (rewrite_tac[ctx_has_dalloca_def, EXISTS_MEM, MEM_EL] >> CCONTR_TAC >>
     gvs[] >> rename1 `EL n C'.ctx_functions` >>
     qpat_x_assum `!n. n < LENGTH C.ctx_functions ==> make_ssa_input_ok _ /\ _`
       (qspec_then `n` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
     `EXISTS (\inst. inst.inst_opcode = DALLOCA)
        (fn_insts (EL n C.ctx_functions))` by
       (irule make_ssa_current_fn_dalloca >> simp[EXISTS_MEM, MEM_EL] >>
        metis_tac[]) >>
     qpat_x_assum `~ctx_has_dalloca C` mp_tac >>
     simp[ctx_has_dalloca_def, EXISTS_MEM, MEM_EL] >>
     gvs[EXISTS_MEM, MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `ptr_discipline lo C vs` mp_tac >>
  rewrite_tac[ptr_discipline_def] >> strip_tac >>
  simp[ptr_discipline_def] >> qexists `P` >> conj_tac
  >- (gvs[EVERY_EL] >> rpt gen_tac >> strip_tac >>
      `fn_ptr_ok P (EL n C.ctx_functions)` by metis_tac[] >>
      qpat_x_assum `!n. n < LENGTH C.ctx_functions ==> make_ssa_input_ok _ /\ _`
        (qspec_then `n` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      drule_all make_ssa_current_fn_ptr_ok >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `frame_reachable vs C' stk2 PG G2 tn2 fn2 inst2 s2` >>
  drule frame_reachable_lockstep >>
  disch_then (qspecl_then [`Q`, `C`] mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `Q _ _ _` mp_tac >> simp[Abbr `Q`] >> strip_tac >>
  gvs[] >>
  drule_all lockstep_rel >> strip_tac >>
  `s2.vs_allocas = s.vs_allocas` by
    metis_tac[state_rel_def, execution_frame_fields] >>
  `allocas_from lo s2` by
    (qpat_x_assum `allocas_from lo s` mp_tac >>
     rewrite_tac[allocas_from_def] >>
     qpat_x_assum `s2.vs_allocas = _` SUBST1_TAC >> rewrite_tac[]) >>
  `p /\ in_revert_forward fn s ==> in_revert_forward fn2 s2` by
    (Cases_on `p` >> simp[] >>
     drule_all make_ssa_lockstep_revert >> simp[]) >>
  `p /\ about_to_revert fn inst s ==> about_to_revert fn2 inst2 s2` by
    (Cases_on `p` >> simp[] >>
     drule_all make_ssa_lockstep_revert >> simp[]) >>
  `~p /\ inst2.inst_opcode = NOP ==> inst2.inst_operands = []` by
    (strip_tac >> gvs[]) >>
  drule_all lockstep_ptr_rows >> simp[]
QED
