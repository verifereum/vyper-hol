(* Fixed-filling static rows for the first MakeSSA stage.  These use no
   whole-run source invariant: headroom is transported as a frame predicate. *)
Theory gasFocusMakeSsaStatic
Ancestors
  o1ContractMakeSsa o1ContractMakeSsaSrc o1PassContract ptrDiscipline
  unitMemInv lowerDloadDefs venomPassSchedule list o1PassLift
  contextRawReachable venomInst venomWf venomFnScheduleRunner
  makeSsaDefs makeSsaCurrentProps makeSsaCurrentSim
  o1ContractMakeSsaReplay o1ContractMakeSsaSrcOpcodes makeSsaCurrentLockstep
  o1FrameLockstep stateFrame venomState option

(* Indexed and output-member forms of the published stage correspondence. *)
Theorem focus_make_ssa_stage_el[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ n < LENGTH C.ctx_functions ==>
  n < LENGTH C'.ctx_functions /\
  MEM (EL n C.ctx_functions) C.ctx_functions /\
  o1_fn_shape C (EL n C.ctx_functions) /\
  ALL_DISTINCT (fn_labels (EL n C.ctx_functions)) /\
  ?t t'. ir_supply_covers_fn t (EL n C.ctx_functions) /\
    ir_supply_inst_ok t /\
    make_ssa_current_fn t (EL n C.ctx_functions) = (EL n C'.ctx_functions,t')
Proof
  strip_tac >> drule make_ssa_stage_functions >> strip_tac >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
  `o1_fn_shape C (EL n C.ctx_functions)` by
    metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels (EL n C.ctx_functions))` by
    fs[o1_fn_shape_def, wf_function_def] >>
  gvs[LIST_REL_EL_EQN]
QED

Theorem focus_make_ssa_stage_fn[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ MEM fn' C'.ctx_functions ==>
  ?fn t t'. MEM fn C.ctx_functions /\ ALL_DISTINCT (fn_labels fn) /\
    make_ssa_current_fn t fn = (fn',t')
Proof
  strip_tac >> drule make_ssa_stage_functions >> strip_tac >>
  `?n. n < LENGTH C'.ctx_functions /\ fn' = EL n C'.ctx_functions` by
    metis_tac[MEM_EL] >>
  `n < LENGTH C.ctx_functions` by metis_tac[LIST_REL_LENGTH] >>
  drule_all focus_make_ssa_stage_el >> strip_tac >> metis_tac[]
QED

Theorem focus_make_ssa_stage_fmp_free[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ fmp_free_ctx C ==> fmp_free_ctx C'
Proof
  rw[fmp_free_ctx_def, EVERY_MEM] >>
  drule_all focus_make_ssa_stage_fn >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (drule make_ssa_current_fn_metadata >> simp[fn_fmp_convention_eq_def]) >>
  drule_all make_ssa_current_fn_kept_opcodes >> strip_tac >>
  fs[pre_fmp_ops_def, EVERY_MEM] >> rpt strip_tac >>
  Cases_on `kept_opcode inst.inst_opcode`
  >- (`MEM inst.inst_opcode
        (FILTER kept_opcode (MAP (\i. i.inst_opcode) (fn_insts fn)))` by
        (simp_tac bool_ss [MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
      `MEM inst.inst_opcode
        (FILTER kept_opcode (MAP (\i. i.inst_opcode) (fn_insts fn')))` by
        metis_tac[] >>
      qpat_x_assum `MEM _ (FILTER _ (MAP _ (fn_insts fn')))` mp_tac >>
      simp_tac bool_ss [MEM_FILTER, MEM_MAP] >> rpt strip_tac >>
      metis_tac[]) >>
  gvs[kept_opcode_def, pre_fmp_opcode_def]
QED

Theorem focus_make_ssa_stage_callee_first[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ callee_first names C.ctx_functions ==>
  callee_first names C'.ctx_functions
Proof
  rw[callee_first_def] >>
  drule_all focus_make_ssa_stage_fn >> strip_tac >>
  `fn_invoke_targets g = fn_invoke_targets fn` by
    (simp[fn_invoke_targets_def] >>
     irule make_ssa_current_fn_invoke_targets >> fs[fn_labels_def] >>
     metis_tac[]) >>
  drule make_ssa_current_fn_metadata >>
  simp[fn_identity_metadata_eq_def] >> metis_tac[]
QED

Theorem focus_make_ssa_stage_dload_count[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C ==> ctx_dload_count C' = ctx_dload_count C
Proof
  strip_tac >> drule make_ssa_stage_functions >> strip_tac >>
  simp[ctx_dload_count_def] >> AP_TERM_TAC >>
  `LENGTH C'.ctx_functions = LENGTH C.ctx_functions` by
    metis_tac[LIST_REL_LENGTH] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rpt strip_tac >>
  drule_all focus_make_ssa_stage_el >> strip_tac >>
  drule_all make_ssa_current_fn_dload_count >> simp[]
QED

Theorem focus_make_ssa_stage_headroom[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv dload_headroom_ok C vs ==>
  mem_inv dload_headroom_ok C' vs
Proof
  strip_tac >>
  qabbrev_tac `k = ctx_dload_count C` >>
  qabbrev_tac `d = ctx_has_dalloca C` >>
  `ctx_dload_count C' = k` by metis_tac[focus_make_ssa_stage_dload_count] >>
  `ctx_has_dalloca C' ==> d` by
    (simp[Abbr `d`, ctx_has_dalloca_def, EXISTS_MEM, MEM_EL, PULL_EXISTS] >>
     rpt strip_tac >>
     `n < LENGTH C.ctx_functions` by
       metis_tac[make_ssa_stage_functions, LIST_REL_LENGTH] >>
     drule_all focus_make_ssa_stage_el >> strip_tac >>
     `MEM (EL n' (fn_insts (EL n C'.ctx_functions)))
          (fn_insts (EL n C'.ctx_functions))` by simp[EL_MEM] >>
     drule_all make_ssa_current_fn_no_dalloca >>
     metis_tac[MEM_EL]) >>
  qabbrev_tac `Q = \ctx:venom_context fn:ir_function inst:instruction s.
     s.vs_alloca_next + 32 * k < dimword (:256) /\
     (d ==> s.vs_alloca_next + 32 * k <= w2n s.vs_initial_fmp)` >>
  `mem_inv Q C vs` by
    (irule mem_inv_mono >> qexists_tac `dload_headroom_ok` >>
     simp[dload_headroom_ok_def, Abbr `Q`, Abbr `k`, Abbr `d`,
          ctx_has_dalloca_def]) >>
  `mem_inv Q C' vs` by
    (irule frame_sim_mem_inv >>
     simp[mem_corr_closed_def, mem_corr_def, Abbr `Q`] >>
     qexists_tac `C` >> simp[] >>
     drule make_ssa_stage_functions >> strip_tac >> simp[] >>
     conj_tac >- (irule make_ssa_src_stage_frame_sim >> metis_tac[]) >>
     fs[]) >>
  irule mem_inv_mono >> goal_assum (drule_at Any) >>
  simp[dload_headroom_ok_def, Abbr `Q`] >>
  fs[ctx_has_dalloca_def]
QED

Theorem make_ssa_focus_static_rows:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv dload_headroom_ok C vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fmp_free_ctx C /\ callee_first names C.ctx_functions ==>
  mem_inv dload_headroom_ok C' vs /\
  EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\
  fmp_free_ctx C' /\ callee_first names C'.ctx_functions
Proof
  strip_tac >>
  `EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions` by
    (rw[EVERY_MEM] >> drule_all focus_make_ssa_stage_fn >> strip_tac >>
     drule make_ssa_current_fn_metadata >>
     fs[EVERY_MEM, fn_static_layout_eq_def]) >>
  metis_tac[focus_make_ssa_stage_headroom, focus_make_ssa_stage_fmp_free,
            focus_make_ssa_stage_callee_first]
QED
