(*
 * MakeSSA's first O1 run keeps the source rows of o1_inv besides the
 * memory, pointer and taint ones: no layout end, no DALLOCA, no FMP
 * convention or operation, the DLOAD offset bound and the alloca headroom
 * LowerDload needs, and the callee-first order.  The pass changes no
 * opcode of an existing instruction but PHIs it cleans up, adds only
 * PHIs and ASSIGNs, and renames variables, so a renamed DLOAD offset
 * holds the original's value.
 *)
Theory o1ContractMakeSsaSrc
Ancestors
  o1PassContract ptrDiscipline unitMemInv lowerDloadDefs venomPassSchedule
  list o1PassLift contextRawReachable venomInst venomWf venomFnScheduleRunner
  makeSsaCurrentDefs makeSsaCurrentProps makeSsaCurrentSim
  o1ContractMakeSsaReplay o1ContractMakeSsaSrcOpcodes makeSsaCurrentLockstep
  o1FrameLockstep stateFrame venomState option


(* ===== The stage's functions ===== *)

Theorem make_ssa_src_stage_fns[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' ==>
  C'.ctx_entry = C.ctx_entry /\
  LIST_REL (\fn fn'. ?t t'.
    ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    make_ssa_current_fn t fn = (fn',t'))
    C.ctx_functions C'.ctx_functions
Proof
  simp[ctx_pass_stage_def] >> strip_tac >> simp[] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[] >> drule make_ssa_pass_step_replay >> simp[]
QED

(* The n-th output function is MakeSSA's run on the n-th input one. *)
Theorem make_ssa_src_stage_el[local]:
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
  strip_tac >> drule make_ssa_src_stage_fns >> strip_tac >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
  `o1_fn_shape C (EL n C.ctx_functions)` by
    metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels (EL n C.ctx_functions))` by
    fs[o1_fn_shape_def, wf_function_def] >>
  gvs[LIST_REL_EL_EQN]
QED

Theorem make_ssa_src_stage_fn[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ MEM fn' C'.ctx_functions ==>
  ?fn t t'. MEM fn C.ctx_functions /\ ALL_DISTINCT (fn_labels fn) /\
    make_ssa_current_fn t fn = (fn',t')
Proof
  strip_tac >> drule make_ssa_src_stage_fns >> strip_tac >>
  `?n. n < LENGTH C'.ctx_functions /\ fn' = EL n C'.ctx_functions` by
    metis_tac[MEM_EL] >>
  `n < LENGTH C.ctx_functions` by metis_tac[LIST_REL_LENGTH] >>
  drule_all make_ssa_src_stage_el >> strip_tac >> metis_tac[]
QED

(* ===== Static rows ===== *)

Theorem make_ssa_src_stage_shape[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ ~ctx_has_dalloca C ==>
  EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C'
Proof
  strip_tac >> conj_tac
  >- (rw[EVERY_MEM] >> drule_all make_ssa_src_stage_fn >> strip_tac >>
      drule make_ssa_current_fn_metadata >>
      fs[EVERY_MEM, fn_static_layout_eq_def]) >>
  fs[ctx_has_dalloca_def, EXISTS_MEM] >> CCONTR_TAC >> gvs[] >>
  drule_all make_ssa_src_stage_fn >> strip_tac >>
  drule_all make_ssa_current_fn_no_dalloca >> metis_tac[]
QED

Theorem make_ssa_src_stage_fmp_free[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ fmp_free_ctx C ==> fmp_free_ctx C'
Proof
  rw[fmp_free_ctx_def, EVERY_MEM] >>
  drule_all make_ssa_src_stage_fn >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (drule make_ssa_current_fn_metadata >> simp[fn_fmp_convention_eq_def]) >>
  drule_then (qspec_then `t` mp_tac) make_ssa_current_fn_no_raw_fmp_ops >>
  simp[]
QED

Theorem make_ssa_src_stage_callee_first[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ callee_first names C.ctx_functions ==>
  callee_first names C'.ctx_functions
Proof
  rw[callee_first_def] >>
  drule_all make_ssa_src_stage_fn >> strip_tac >>
  `fn_invoke_targets g = fn_invoke_targets fn` by
    (simp[fn_invoke_targets_def] >>
     irule make_ssa_current_fn_invoke_targets >> fs[fn_labels_def] >>
     metis_tac[]) >>
  drule make_ssa_current_fn_metadata >>
  simp[fn_identity_metadata_eq_def] >> metis_tac[]
QED

Theorem make_ssa_src_stage_dload_count[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C ==> ctx_dload_count C' = ctx_dload_count C
Proof
  strip_tac >> drule make_ssa_src_stage_fns >> strip_tac >>
  simp[ctx_dload_count_def] >> AP_TERM_TAC >>
  `LENGTH C'.ctx_functions = LENGTH C.ctx_functions` by
    metis_tac[LIST_REL_LENGTH] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rpt strip_tac >>
  drule_all make_ssa_src_stage_el >> strip_tac >>
  drule_all make_ssa_current_fn_dload_count >> simp[]
QED

(* ===== Frame facts ===== *)

Theorem make_ssa_src_stage_frame[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions ==>
  ctx_bisim C C' /\
  LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                     fn_entry_label fn' = fn_entry_label fn /\
                     ?t t'. make_ssa_current_fn t fn = (fn',t') /\
                       ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
                       make_ssa_input_ok fn /\ o1_fn_shape C fn)
    C.ctx_functions C'.ctx_functions
Proof
  strip_tac >> drule make_ssa_src_stage_fns >> strip_tac >>
  `LENGTH C'.ctx_functions = LENGTH C.ctx_functions` by
    metis_tac[LIST_REL_LENGTH] >>
  `!n. n < LENGTH C.ctx_functions ==>
       fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions) /\
       make_ssa_input_ok (EL n C.ctx_functions) /\
       o1_fn_shape C (EL n C.ctx_functions) /\
       ?t t'. make_ssa_current_fn t (EL n C.ctx_functions) =
                (EL n C'.ctx_functions,t') /\
              ir_supply_covers_fn t (EL n C.ctx_functions) /\
              ir_supply_inst_ok t` by
    (rpt gen_tac >> strip_tac >> drule_all make_ssa_src_stage_el >>
     strip_tac >>
     `make_ssa_input_ok (EL n C.ctx_functions)` by fs[EVERY_MEM] >>
     `fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions)` by
       (irule make_ssa_current_fn_fn_bisim >>
        gvs[make_ssa_input_ok_def, o1_fn_shape_def] >> metis_tac[]) >>
     metis_tac[]) >>
  conj_tac
  >- (irule fn_bisim_ctx_bisim >> simp[LIST_REL_EL_EQN]) >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[fn_bisim_def] >> metis_tac[]
QED

Theorem make_ssa_src_stage_frame_sim[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions ==>
  LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                     fn_entry_label fn' = fn_entry_label fn /\
                     frame_sim L C C' fn fn')
    C.ctx_functions C'.ctx_functions
Proof
  strip_tac >> drule_all make_ssa_src_stage_frame >> strip_tac >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >> rpt strip_tac >>
  gvs[] >> irule make_ssa_current_fn_frame_sim >>
  gvs[make_ssa_input_ok_def, o1_fn_shape_def] >> metis_tac[]
QED

(* The headroom bound reads only the frontier and the DLOAD count, which
   the stage keeps. *)
Theorem make_ssa_src_stage_headroom[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv dload_headroom_ok C vs ==>
  mem_inv dload_headroom_ok C' vs
Proof
  strip_tac >>
  qabbrev_tac `k = ctx_dload_count C` >>
  `ctx_dload_count C' = k` by metis_tac[make_ssa_src_stage_dload_count] >>
  `mem_inv (\ctx fn inst s. s.vs_alloca_next + 32 * k < dimword (:256))
     C vs` by
    (irule mem_inv_mono >> qexists_tac `dload_headroom_ok` >>
     simp[dload_headroom_ok_def, Abbr `k`]) >>
  `mem_inv (\ctx fn inst s. s.vs_alloca_next + 32 * k < dimword (:256))
     C' vs` by
    (irule frame_sim_mem_inv >> simp[mem_corr_closed_def, mem_corr_def] >>
     qexists_tac `C` >> simp[] >>
     drule make_ssa_src_stage_fns >> strip_tac >> simp[] >>
     conj_tac >- (irule make_ssa_src_stage_frame_sim >> metis_tac[]) >>
     fs[]) >>
  irule mem_inv_mono >> goal_assum (drule_at Any) >>
  simp[dload_headroom_ok_def]
QED

(* Each function of the output is MakeSSA's run on the input function of
   its name. *)
Theorem make_ssa_src_stage_lookup[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  lookup_function nm C.ctx_functions = SOME fn ==>
  ?fn' t t'. lookup_function nm C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = fn_entry_label fn /\
    make_ssa_current_fn t fn = (fn',t') /\
    ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    make_ssa_input_ok fn /\ o1_fn_shape C fn
Proof
  strip_tac >> drule_all make_ssa_src_stage_frame >> strip_tac >>
  drule list_rel_lookup_function >> impl_tac >- simp[] >>
  disch_then (qspec_then `nm` mp_tac) >> simp[] >>
  Cases_on `lookup_function nm C'.ctx_functions` >>
  simp[optionTheory.OPTREL_def] >> metis_tac[]
QED

(* The DLOAD offset bound: a reachable DLOAD of the output reads the value
   of the one of the input it renames, from the same code. *)
Theorem make_ssa_src_stage_dload_ok[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv dload_offset_ok C vs ==>
  mem_inv dload_offset_ok C' vs
Proof
  strip_tac >>
  `LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                      fn_entry_label fn' = fn_entry_label fn /\
                      frame_sim vs.vs_labels C C' fn fn')
     C.ctx_functions C'.ctx_functions` by
    metis_tac[make_ssa_src_stage_frame_sim] >>
  `ctx_bisim C C'` by metis_tac[make_ssa_src_stage_frame] >>
  `C'.ctx_entry = C.ctx_entry` by metis_tac[make_ssa_src_stage_fns] >>
  fs[mem_inv_raw_reachable] >> conj_tac
  >- (drule_all make_ssa_src_stage_lookup >> strip_tac >> metis_tac[]) >>
  rpt strip_tac >> rename1 `raw_reachable vs C' fn' inst' s'` >>
  reverse (Cases_on
    `inst'.inst_opcode = DLOAD \/ inst'.inst_opcode = DLOADBYTES`)
  >- fs[dload_offset_ok_def] >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  `frame_origin vs C C' fn' inst' s'` by
    (irule frame_sim_raw_origins >> fs[]) >>
  fs[frame_origin_def] >>
  drule_all make_ssa_src_stage_lookup >> strip_tac >> gvs[] >>
  rename1 `make_ssa_current_fn _ g = (fn',_)` >>
  `frame_lockstep vs.vs_labels C C' g fn' (make_ssa_pos g fn')` by
    (irule make_ssa_current_fn_frame_lockstep >> fs[o1_fn_shape_def] >>
     metis_tac[]) >>
  fs[frame_lockstep_def] >>
  `?inst s. frame_reach C g s0 inst s /\
            inst.inst_opcode = inst'.inst_opcode /\
            execution_frame s' = execution_frame s /\
            LIST_REL (\op op'. eval_operand op' s' = eval_operand op s)
              inst.inst_operands inst'.inst_operands` by
    (irule frame_reach_lockstep >> fs[] >> metis_tac[]) >>
  `raw_reachable vs C g inst s` by
    (irule frame_reach_raw_reachable >> metis_tac[]) >>
  `s'.vs_code = s.vs_code /\ s'.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `execution_frame s' = execution_frame s` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  first_x_assum drule >>
  simp[dload_offset_ok_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS2] >> first_x_assum irule >> metis_tac[]
QED

Theorem make_ssa_stage_src_rows:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ EVERY make_ssa_input_ok C.ctx_functions /\
    callee_first names C.ctx_functions ==>
    EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C' /\
    fmp_free_ctx C' /\ mem_inv dload_offset_ok C' vs /\
    mem_inv dload_headroom_ok C' vs /\ callee_first names C'.ctx_functions
Proof
  rpt gen_tac >> strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  fs[o1_src_inv_def] >>
  metis_tac[make_ssa_src_stage_shape, make_ssa_src_stage_fmp_free,
            make_ssa_src_stage_callee_first, make_ssa_src_stage_headroom,
            make_ssa_src_stage_dload_ok]
QED
