(* MakeSSA preserves pointer discipline at the same gas cut and filling.
   The frame lockstep identifies the source cut before source safety is used. *)
Theory o1MakeSsaPtrUpto
Ancestors
  o1ContractMakeSsa o1SafeUpto o1ContractMakeSsaPtrOk
  o1ContractMakeSsaPtrRows o1ContractMakeSsaPtrPos o1FrameLockstep
  makeSsaCurrentLockstep makeSsaCurrentRevertForward makeSsaCurrentOrigin
  o1PassContract ptrDiscipline unitMemInv list makeSsaCurrentSim
  makeSsaCurrentProps o1PassLift contextCodegenRel

Theorem make_ssa_stage_ptr_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  ptr_discipline_upto lo n C vs ==>
  ptr_discipline_upto lo n C' vs
Proof
  rpt strip_tac >>
  drule make_ssa_stage_functions >> strip_tac >>
  drule make_ssa_stage_length >> strip_tac >>
  `ctx_bisim C C'` by (irule make_ssa_stage_bisim >> metis_tac[]) >>
  qabbrev_tac `Q = \fn fn' pos.
     pos = make_ssa_pos fn fn' /\
     make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
     first_block_no_preds fn /\ first_block_no_phi fn /\
     ?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
            make_ssa_current_fn t fn = (fn',t')` >>
  `lockstep_ctx Q vs.vs_labels C C'` by
    (simp[lockstep_ctx_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
     drule_all make_ssa_stage_el >> strip_tac >>
     `fn_bisim (EL n' C.ctx_functions) (EL n' C'.ctx_functions)` by
       (irule make_ssa_current_fn_fn_bisim >>
        gvs[make_ssa_input_ok_def] >> metis_tac[]) >>
     fs[fn_bisim_def] >>
     qexists `make_ssa_pos (EL n' C.ctx_functions) (EL n' C'.ctx_functions)` >>
     simp[Abbr `Q`] >> reverse conj_tac >- metis_tac[] >>
     irule make_ssa_current_fn_frame_lockstep >> metis_tac[]) >>
  `~ctx_has_dalloca C ==> ~ctx_has_dalloca C'` by suspend "dalloca" >>
  qpat_x_assum `ptr_discipline_upto lo n C vs` mp_tac >>
  rewrite_tac[ptr_discipline_upto_def] >> strip_tac >>
  simp[ptr_discipline_upto_def] >> conj_tac
  >- (qexists `P` >> simp[EVERY_EL] >> rpt gen_tac >> strip_tac >>
      drule_all make_ssa_stage_el >> strip_tac >>
      `fn_ptr_ok P (EL n' C.ctx_functions)` by
        (qpat_x_assum `EVERY (\fn. fn_ptr_ok P fn /\ _) _` mp_tac >>
         simp[EVERY_EL] >> disch_then (qspec_then `n'` mp_tac) >> simp[]) >>
      drule_all make_ssa_current_fn_ptr_ok >> simp[]) >>
  suspend "reachable"
QED

Resume make_ssa_stage_ptr_upto[dalloca]:
  strip_tac >> rewrite_tac[ctx_has_dalloca_def, EXISTS_MEM, MEM_EL] >>
  CCONTR_TAC >> gvs[] >> rename1 `EL k C'.ctx_functions` >>
  `k < LENGTH C.ctx_functions` by simp[] >>
  drule_all make_ssa_stage_el >> strip_tac >>
  `EXISTS (\inst. inst.inst_opcode = DALLOCA)
     (fn_insts (EL k C.ctx_functions))` by
    (irule make_ssa_current_fn_dalloca >> simp[EXISTS_MEM, MEM_EL] >>
     metis_tac[]) >>
  qpat_x_assum `~ctx_has_dalloca C` mp_tac >>
  simp[ctx_has_dalloca_def, EXISTS_MEM, MEM_EL] >>
  gvs[EXISTS_MEM, MEM_EL] >> metis_tac[]
QED

Resume make_ssa_stage_ptr_upto[reachable]:
  rpt gen_tac >> strip_tac >>
  rename1 `frame_reachable vs C' stk2 PG G2 tn2 fn2 inst2 s2` >>
  drule frame_reachable_lockstep >>
  disch_then (qspecl_then [`Q`, `C`] mp_tac) >> simp[] >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `gas_cut n vs s` by
    (irule gas_cut_execution_frame >> goal_assum (drule_at Any) >>
     gvs[state_rel_def]) >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `Q _ _ _` mp_tac >> simp[Abbr `Q`] >> strip_tac >> gvs[] >>
  `s2.vs_allocas = s.vs_allocas` by
    metis_tac[state_rel_def, execution_frame_fields] >>
  `allocas_from lo s2` by
    (qpat_x_assum `allocas_from lo s` mp_tac >>
     rewrite_tac[allocas_from_def] >>
     qpat_x_assum `s2.vs_allocas = _` SUBST1_TAC >> rewrite_tac[]) >>
  `s2.vs_fmp = s.vs_fmp /\ s2.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[state_rel_def, execution_frame_fields] >>
  `ctx_has_dalloca C' ==> allocas_below_fmp s2` by
    (strip_tac >> `allocas_below_fmp s` by metis_tac[] >>
     fs[allocas_below_fmp_def] >> metis_tac[]) >>
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

Finalise make_ssa_stage_ptr_upto
