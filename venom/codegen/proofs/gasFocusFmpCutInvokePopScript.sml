(* The cut return resumes the saved callers and restricts the current site
   map at the source caller's saved frontier. *)
Theory gasFocusFmpCutInvokePop
Ancestors
  gasFocusFmpCutSites gasFocusChronologicalCut gasFocusFmpStagePin
  gasFocusFmpRetPoint fmpStageFmpStepsLedgerRestrict
  fmpStageFmpStepsRetSource fmpStageFmpStepsRetCaller
  fmpStageFmpStepsRetInvokeCode fmpStageFmpStepsRetInvokeObserved
  fmpStageFmpStepsRetInvokeOrigin fmpStageFmpStepsCallAbi
  fmpStageFmpStepsInvokePosition fmpStageFmpStepsRetBind
  fmpStageFmpStepsRetAnalysis fmpStageFmpStepsRetFresh
  concretizeStageLookup concretizePtrChronologicalHistory fmpStepBridge
  lowerDloadPtrRawReachable concretizeLayoutCutSafe ptrDisciplineCallCtx
  fmpStageOpFrame fmpStageRel o1PassContract o1SafeUpto
  contextCodegenRel venomExecSemantics venomExecProofs unitTransformDefs
  venomWf venomWfProps venomInstIdsProps venomInst venomState
  words list finite_map pred_set arithmetic

Theorem pop_saved_cut_bounds[local]:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C (f::stk) PG G tn fn inst s /\ gas_cut n vs s ==>
  EVERY (\g. w2n g.cf_state.vs_fmp <= w2n f.cf_state.vs_fmp) (f::stk) /\
  !g. MEM g (f::stk) ==>
    (!v b z. FLOOKUP g.cf_prov v = SOME (b,z) /\ 0 < z ==>
             b < w2n g.cf_state.vs_fmp) /\
    (!k b z. k < LENGTH g.cf_params /\ EL k g.cf_params = SOME (b,z) /\ 0 < z ==>
             b < w2n g.cf_state.vs_fmp)
Proof
  strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  `EVERY (\g. gas_cut n vs g.cf_state) (f::stk)` by
    (drule ptr_chrono_saved_callers_cut >> simp[ptr_observe_def]) >>
  drule fmp_stage_saved_source >> strip_tac >>
  conj_tac
  >- (qpat_assum `!pre g rest. _`
        (qspecl_then [`[]`,`f`,`stk`] (strip_assume_tac o SRULE [])) >>
      `gas_cut n vs f.cf_state` by gvs[] >>
      drule_all focus_fmp_frame_sites_upto >> simp[]) >>
  qx_gen_tac `g` >> strip_tac >>
  `?pre rest. f::stk = pre ++ g::rest` by metis_tac[MEM_SPLIT] >>
  qpat_x_assum `!pre g rest. _` (qspecl_then [`pre`,`g`,`rest`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `gas_cut n vs g.cf_state` by gvs[EVERY_MEM] >>
  drule_all focus_fmp_frame_sites_upto >> strip_tac >>
  conj_tac >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!v b z. FLOOKUP _ _ = _ /\ _ ==> _` drule_all >>
      strip_tac >> decide_tac) >>
  fs[EVERY_EL] >>
  qpat_x_assum `!k. k < LENGTH g.cf_params ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem pop_saved_restrict[local]:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C (f::stk) PG G tn fn inst s /\ gas_cut n vs s /\
  fmp_saved_rel C' sm fmp0 raw0 (f::stk) ts ==>
  fmp_saved_rel C' (DRESTRICT sm {key | FST key < w2n f.cf_state.vs_fmp})
    fmp0 raw0 (f::stk) ts
Proof
  strip_tac >> drule_all pop_saved_cut_bounds >> strip_tac >>
  irule fmp_saved_rel_drestrict >> simp[] >>
  fs[EVERY_MEM] >> conj_tac >> rpt strip_tac >>
  `b < w2n f.cf_state.vs_fmp` suffices_by simp[FLOOKUP_DRESTRICT] >>
  metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem pop_observed_nonpublishing[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C C' /\
  fmp_free_ctx C /\ o1_walk_view rp 3 C' fn observed /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name observed.cu_context.ctx_functions = SOME g ==>
  !sig. g.fn_fmp_signature = SOME sig ==> ~sig.fms_publishes
Proof
  strip_tac >>
  `MEM name (ctx_fn_names observed.cu_context)` by
    (drule lookup_function_MEM >> drule fmpAnalysisPropsTheory.lookup_function_name >>
     rpt strip_tac >> pure_rewrite_tac[ctx_fn_names_def, MEM_MAP] >> metis_tac[]) >>
  `?src. lookup_function name C.ctx_functions = SOME src` by
    (Cases_on `lookup_function name C.ctx_functions` >>
     gvs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  drule_all fmp_return_stage_callee_signature >> strip_tac >>
  drule_all fmp_call_walk_signature >> strip_tac >> gvs[]
QED

Theorem pop_invoke_outputs[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C C' /\
  fmp_free_ctx C /\ lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  MEM j (fn_insts fn') /\ j.inst_opcode = INVOKE /\ j.inst_id = inst.inst_id ==>
  j.inst_outputs = inst.inst_outputs
Proof
  strip_tac >> drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `!i name args callee sig.
     MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
     i.inst_operands = Label name::args /\
     lookup_function name observed.cu_context.ctx_functions = SOME callee /\
     callee.fn_fmp_signature = SOME sig ==> ~sig.fms_publishes` by
    (rpt strip_tac >>
     `MEM name (fn_invoke_targets fn)` by
       (simp[concretizeAnalysisMetadataOwnershipTheory.invoke_target_instruction] >> metis_tac[]) >>
     drule_all pop_observed_nonpublishing >> simp[]) >>
  drule fmp_return_function_origin >> disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >> metis_tac[fn_inst_ids_distinct_inj]
QED

Theorem pop_resume_caller[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C C' /\
  o1_ctx_shape C /\ fmp_free_ctx C /\ ssa_form fn /\ pre_fmp_ops fn /\
  frame_reachable vs C stk PG G tn fn inst s /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tn.t_var s t /\
  ret.iret_adopt_fmp = NONE /\ jr.iret_adopt_fmp = NONE /\
  jr.iret_values = ret.iret_values /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s1 /\
  active_inst fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?j t1. active_inst fn' j t /\ j.inst_opcode = INVOKE /\
    j.inst_id = inst.inst_id /\ j.inst_outputs = inst.inst_outputs /\
    bind_outputs j.inst_outputs jr.iret_values
      (adopt_return_fmp jr (merge_callee_state t te)) = SOME t1 /\
    s1 = (merge_callee_state s se with vs_vars := s1.vs_vars) /\
    t1 = (merge_callee_state t te with vs_vars := t1.vs_vars) /\
    fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG
      (DRESTRICT G (COMPL (set inst.inst_outputs)))
      (DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule frame_reachable_raw_certificate >> simp[] >> strip_tac >>
  `o1_fn_shape C fn /\ EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmpLowerPropsTheory.fmp_lookup_function_self >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `fn_inst_ids_distinct fn` by
    (fs[o1_ctx_shape_def] >> drule_all allocaFrontierBoundTheory.ctx_inst_ids_distinct_fn >>
     simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `MEM inst (fn_insts fn)` by metis_tac[allocaFrontierBoundTheory.active_inst_mem_fn_insts] >>
  `wf_function fn /\ ssa_form fn /\ ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[o1_fn_shape_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT inst.inst_outputs` by
    (irule all_distinct_flat_map_member >> qexists_tac `fn_insts fn` >>
     conj_tac >- (qpat_assum `ssa_form fn` (ACCEPT_TAC o
       SIMP_RULE (srw_ss() ++ ETA_ss) [venomWfTheory.ssa_form_def])) >>
     first_assum ACCEPT_TAC) >>
  drule_all frame_reachable_dfs >> strip_tac >>
  drule_all fmp_frame_invoke_position >> strip_tac >>
  `j.inst_outputs = inst.inst_outputs` by (drule_all pop_invoke_outputs >> simp[]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
        s.vs_inst_idx < LENGTH bb.bb_instructions /\
        EL s.vs_inst_idx bb.bb_instructions = inst` by
    (qpat_assum `active_inst fn inst s`
       (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
     metis_tac[venomExecProofsTheory.wf_lookup_block]) >>
  qpat_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
  drule_all fmp_return_bind_caller >>
  disch_then (qspec_then `te` strip_assume_tac) >>
  `fn.fn_fmp_signature = NONE` by fs[fmp_free_ctx_def, EVERY_MEM] >>
  drule_all focus_fmp_selected_root_pin >> strip_tac >>
  rename1 `fmp_stage_lowered infos0 ctx0 runner0 fn actual` >>
  `actual = fn'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `actual = fn'` SUBST_ALL_TAC >>
  `!rl r. fmp_stage_root infos ctx fn = SOME (rl,r) ==>
      (fn_is_context_entry ctx fn <=> C.ctx_entry = SOME fn.fn_name) /\
      ~MEM runner inst.inst_outputs` by
    (qpat_x_assum `!i c v rl r. fmp_stage_lowered i c v fn fn' /\ _ ==> _`
      (qspecl_then [`infos`,`ctx`,`runner`] mp_tac) >> simp[]) >>
  `!rl r. fmp_stage_root infos ctx fn = SOME (rl,r) /\
      s.vs_current_bb = rl ==> r <> SUC s.vs_inst_idx` by
    (rpt strip_tac >>
     `fn_is_context_entry ctx fn ==> entry_fn_no_params fn` by
       (qpat_assum `!rl r. fmp_stage_root infos ctx fn = _ ==> _`
          (qspecl_then [`rl`,`r`] mp_tac) >>
        simp[] >> strip_tac >>
        qpat_assum `o1_fn_shape C fn`
          (strip_assume_tac o REWRITE_RULE [o1_fn_shape_def]) >> simp[]) >>
     `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE` by simp[] >>
     drule_all fmp_return_root_excluded >> simp[]) >>
  qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` (fn th =>
    qpat_x_assum `t.vs_inst_idx = _` (assume_tac o SIMP_RULE (srw_ss()) [th])) >>
  `!rl r. fmp_stage_root infos ctx fn = SOME (rl,r) ==>
      ~fmp_clears_marks infos inst` by
    (rpt gen_tac >> disch_tac >> irule fmp_return_saved_invoke_nonclearing >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`bb`,`ctx`,`fn`,`fn'`,`s.vs_inst_idx`,`j`,
               `s.vs_current_bb`,`rl`,`r`,`runner`,`t`] >> simp[]) >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx) = SUC t.vs_inst_idx` by
    (qpat_assum `t.vs_inst_idx = _` (fn th => CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV th)))) >>
     gvs[fmp_return_tidx_suc]) >>
  qexistsl [`j`,`t1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms, fmp_frame_rel_def, LET_THM] >>
  qexistsl [`infos`,`ctx`,`runner`] >>
  `s1.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb` by
    gvs[merge_callee_state_def, venom_state_component_equality] >>
  gvs[venom_state_component_equality, merge_callee_state_def] >>
  conj_tac >- gvs[fmp_params_rel_def] >>
  conj_tac >- (qpat_assum `!b z c id. _` mp_tac >> metis_tac[]) >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  mp_tac (Q.INST [`k` |-> `s.vs_inst_idx`, `rl` |-> `x0`, `rp` |-> `x1`,
    `outs` |-> `(EL s.vs_inst_idx bb.bb_instructions).inst_outputs`,
    `vals` |-> `ret.iret_values`, `ret` |-> `jr`, `callee` |-> `te`,
    `A` |-> `COMPL (set (EL s.vs_inst_idx bb.bb_instructions).inst_outputs)`,
    `tidx` |-> `SUC t.vs_inst_idx`, `fmp0` |-> `w2n t.vs_initial_fmp`]
    fmp_return_root_analysis) >>
  impl_tac
  >- (simp[merge_callee_state_def] >> rpt conj_tac >> gvs[]
      >~ [`MEM _ (SND _)`]
      >- (mp_tac (Q.INST [`lbl` |-> `t.vs_current_bb`, `idx` |-> `s.vs_inst_idx`,
            `inst` |-> `EL s.vs_inst_idx bb.bb_instructions`,
            `live` |-> `liveness_analyze fn`] fmp_return_popped_outputs_fresh) >> simp[]) >>
      IF_CASES_TAC >> gvs[] >> qexists `regions` >> simp[]) >>
  strip_tac >> qexists `st1` >> gvs[lookup_var_def]
QED

Theorem focus_fmp_cut_invoke_pop:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C C' /\
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ fmp_free_ctx C /\
  raw0 = w2n vs.vs_fmp /\
  (!g i u. raw_reachable vs C g i u /\ gas_cut n vs u ==>
           dalloca_no_wrap i u) /\
  frame_reachable vs C (f::stk) PG G tn fn rinst s /\ gas_cut n vs s /\
  active_inst fn rinst s /\ rinst.inst_opcode = RET /\
  opaque_use_ok fn /\ ptr_use_static_ok P (fn_pv P fn) rinst /\
  FDOM G SUBSET fn_pv P fn /\ taint_ok fn tn rinst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T (f::stk) PG G tn fn s lo t
    ((tc,lc)::ts) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s1 /\
  active_inst f.cf_fn next (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  active_inst fn' rinst t /\ se = s /\ ret.iret_adopt_fmp = NONE /\
  ?jr fc' j t1.
    (!fuel. step_inst fuel C' rinst t = IntRet jr t) /\
    jr.iret_values = ret.iret_values /\ jr.iret_adopt_fmp = NONE /\
    lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fc' /\
    active_inst fc' j tc /\ j.inst_opcode = INVOKE /\
    j.inst_id = f.cf_inst.inst_id /\ j.inst_outputs = f.cf_inst.inst_outputs /\
    bind_outputs j.inst_outputs jr.iret_values
      (adopt_return_fmp jr (merge_callee_state tc t)) = SOME t1 /\
    fmp_stage_rel D C' (DRESTRICT sm {key | FST key < w2n f.cf_state.vs_fmp})
      fmp0 raw0 eom F stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx) lc
      (t1 with vs_inst_idx := SUC tc.vs_inst_idx) ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by (drule frame_reachable_raw_certificate >> simp[]) >>
  `wf_function fn /\ make_ssa_input_ok fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def, o1_fn_row_def, DECIDE ``3 <= 4``]) >>
  drule_all fmp_focus_ret_point >> strip_tac >>
  `s.vs_call_ctx = f.cf_state.vs_call_ctx` by
    (drule ptr_reachable_stack_call_ctx >> simp[]) >>
  drule fmp_stage_saved_source >>
  disch_then (qspecl_then [`[]`,`f`,`stk`] (strip_assume_tac o SRULE [])) >>
  `MEM f.cf_fn C.ctx_functions` by
    (qpat_assum `frame_reachable _ _ stk _ _ _ _ _ _`
       (mp_tac o MATCH_MP frame_reachable_raw_certificate) >> simp[]) >>
  `ssa_form f.cf_fn /\ pre_fmp_ops f.cf_fn` by
    (fs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  drule_all pop_saved_restrict >> strip_tac >>
  qpat_x_assum `fmp_saved_rel _ (DRESTRICT _ _) _ _ (f::stk) _`
    (strip_assume_tac o REWRITE_RULE [fmp_saved_rel_def]) >>
  rename1 `lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fc'` >>
  qpat_assum `tn0.t_var = f.cf_tvar` (fn th =>
    qpat_x_assum `fmp_frame_rel (DRESTRICT _ _) _ _ _ _ _ _ _ _ _ _ _ _ _`
      (assume_tac o REWRITE_RULE [GSYM th])) >>
  drule_all pop_resume_caller >>
  disch_then (qspec_then `t` strip_assume_tac) >>
  simp[] >> qexistsl [`j`,`t1`] >> simp[] >>
  simp[fmp_stage_rel_def] >>
  gvs[venom_state_component_equality, merge_callee_state_def] >>
  conj_tac
  >- (irule fmp_sites_ok_return_restrict >>
      qpat_x_assum `fmp_frame_rel sm _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[fmp_frame_rel_def, fmp_frame_base_def, fmp_frame_lo_def] >>
      metis_tac[]) >>
  conj_tac >- (irule fmp_memory_agree_drestrict >> first_assum ACCEPT_TAC) >>
  fs[o1LowerDloadSharedTheory.ld_shared_agree_def]
QED
