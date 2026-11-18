(* Concrete C3/C4 segments under cut-local safety. *)
Theory gasFocusFmpCutSegments
Ancestors
  gasFocusFmpDallocaRun gasFocusFmpDallocaSaved gasFocusFmpDallocaActive
  fmpStageFmpStepsDallocaShared fmpStageFmpStepsDallocaExec
  fmpStageFmpStepsInvokePosition lowerDloadPtrRawReachable
  fmpLowerSequenceExec fmpStageRel o1PassContract unitShapeDefs
  venomState venomInst venomExecProofs finite_map words list
  fmpStageControl fmpLowerReclaimPlan fmpStepReclaim fmpReclaimDefs
  fmpAnalysisDefs venomWf gasFocusFmpStagePin fmpLedgerProps fmpStepStack
  fmpStepAnalysis venomFnInstsProofs venomInstProofs1

Theorem cut_ordinary_not_reclaim[local]:
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA] ==>
  ~fmp_is_reclaim_point infos inst
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule fmp_reclaim_point_opcodes >>
  gvs[] >> metis_tac[is_terminator_def]
QED

Theorem cut_ordinary_analysis_suc[local]:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; SETFMP] /\
  df_at NONE states lbl idx = SOME st ==>
  ?st'. df_at NONE states lbl (SUC idx) = SOME st' /\
    st'.frs_stack = st.frs_stack
Proof
  strip_tac >>
  `~fmp_is_reclaim_point infos inst` by (irule cut_ordinary_not_reclaim >> gvs[]) >>
  `~fmp_clears_marks infos inst` by
    gvs[fmp_clears_marks_def, fmp_callee_info_def, fmp_invoke_target_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  fs[wf_function_def, fn_labels_def] >>
  drule_all fmp_reclaim_states_df_at_suc >>
  simp[fmp_transfer_def, fmp_reclaim_step_def, fmp_pop_at_def,
       fmp_apply_effect_def] >> gvs[]
QED

Theorem cut_ordinary_control_suc[local]:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM] /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) ==>
  (lbl,idx) NOTIN FDOM (fmp_stage_plan infos ctx fn) /\
  (!rp. fmp_stage_root infos ctx fn = SOME (lbl,rp) ==> rp <> SUC idx) /\
  fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
    lbl bb.bb_instructions (SUC idx) =
  SUC (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
    lbl bb.bb_instructions idx)
Proof
  strip_tac >> conj_asm1_tac
  >- (strip_tac >> drule_all fmp_stage_plan_point >> strip_tac >>
      `~fmp_is_reclaim_point infos inst` by (irule cut_ordinary_not_reclaim >> gvs[]) >>
      gvs[]) >>
  conj_asm1_tac
  >- (rpt strip_tac >> metis_tac[fmp_stage_root_crossing, MEM]) >>
  irule fmp_stage_tidx_suc >> fs[] >> metis_tac[]
QED

(* An ordinary instruction cannot redefine a saved DALLOCA mark in SSA. *)
Theorem cut_ordinary_ledger[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode <> DALLOCA /\
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states lbl idx = SOME st /\
  MAP (\r. r.fr_mark) regions = st.frs_stack /\
  fmp_ledger_ok (fn_insts fn) env t lo regions /\
  (!v. ~MEM v inst.inst_outputs ==> lookup_var v t1 = lookup_var v t) ==>
  fmp_ledger_ok (fn_insts fn) env (t1 with vs_inst_idx := j) lo regions
Proof
  strip_tac >> irule fmp_ledger_frame >> qexists `t` >> simp[] >>
  rpt strip_tac >>
  `EVERY (fmp_dalloca_output fn) st.frs_stack` by
    metis_tac[fmp_reclaim_states_stack] >>
  `MEM r.fr_mark st.frs_stack` by
    (qpat_assum `MAP _ regions = _` (SUBST1_TAC o SYM) >> simp[MEM_MAP] >>
     qexists `r` >> simp[]) >>
  `fmp_dalloca_output fn r.fr_mark` by metis_tac[EVERY_MEM] >>
  `~MEM r.fr_mark inst.inst_outputs` by
    (gvs[fmp_dalloca_output_def, ssa_form_def] >>
     metis_tac[all_distinct_flat_map_unique]) >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

Theorem cut_ordinary_root_suc[local]:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  wf_function fn /\ ssa_form fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; SETFMP] /\
  df_at NONE states lbl idx = SOME st /\
  (lbl = rl ==> rp <> SUC idx) /\ ~MEM runner inst.inst_outputs /\
  s1.vs_params = s.vs_params /\ t1.vs_params = t.vs_params /\
  (!v. ~MEM v inst.inst_outputs ==> lookup_var v t1 = lookup_var v t) /\
  (if lbl = rl /\ idx < rp then
     lo = elo /\ st.frs_stack = [] /\
     (fn_is_context_entry ctx fn ==> fmp0 = elo) /\
     (~fn_is_context_entry ctx fn ==>
       LENGTH s.vs_params = LENGTH (fn_user_param_insts fn) /\
       LENGTH s.vs_params < LENGTH t.vs_params /\
       EL (LENGTH s.vs_params) t.vs_params = n2w elo)
   else lookup_var runner t = SOME (n2w lo) /\
     ?regions. fmp_ledger_ok (fn_insts fn) env t lo regions /\
       MAP (\r. r.fr_mark) regions = st.frs_stack /\
       EVERY (\r. elo <= r.fr_lo) regions /\ fmp_ledger_link sm eb lo regions) ==>
  ?st'. df_at NONE states lbl (SUC idx) = SOME st' /\
    (if lbl = rl /\ SUC idx < rp then
       lo = elo /\ st'.frs_stack = [] /\
       (fn_is_context_entry ctx fn ==> fmp0 = elo) /\
       (~fn_is_context_entry ctx fn ==>
         LENGTH s1.vs_params = LENGTH (fn_user_param_insts fn) /\
         LENGTH s1.vs_params < LENGTH t1.vs_params /\
         EL (LENGTH s1.vs_params) t1.vs_params = n2w elo)
     else lookup_var runner (t1 with vs_inst_idx := j) = SOME (n2w lo) /\
       ?regions. fmp_ledger_ok (fn_insts fn) env (t1 with vs_inst_idx := j) lo regions /\
         MAP (\r. r.fr_mark) regions = st'.frs_stack /\
         EVERY (\r. elo <= r.fr_lo) regions /\ fmp_ledger_link sm eb lo regions)
Proof
  strip_tac >> drule_all cut_ordinary_analysis_suc >>
  disch_then (qx_choose_then `st'` strip_assume_tac) >>
  `lbl = rl /\ SUC idx < rp <=> lbl = rl /\ idx < rp` by
    (Cases_on `lbl = rl` >> fs[] >> decide_tac) >>
  qexists `st'` >> simp[] >>
  IF_CASES_TAC >- fs[] >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  conj_tac
  >- (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `inst.inst_opcode <> DALLOCA` by fs[] >>
  drule_all cut_ordinary_ledger >> disch_then (qspec_then `j` assume_tac) >>
  qexists `regions` >> simp[]
QED

Theorem focus_fmp_cut_dalloca_segment:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  wf_function fn /\ ssa_form fn /\ make_ssa_input_ok fn /\
  fn.fn_fmp_signature = NONE /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1 t1 sm1 sz fn' bb' code tail op out runner plus31 mask aligned ai ni mi bi.
    r = OK s1 /\ inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
    eval_operand op s = SOME sz /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    DROP t.vs_inst_idx bb'.bb_instructions = code ++ tail /\
    code = [mk_inst ai ADD [op;Lit 31w] [plus31];
            mk_inst ni NOT [Lit 31w] [mask];
            mk_inst mi AND [Var plus31;Var mask] [aligned];
            mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] /\
    (!k'. fmp_target_run k' C' fn.fn_name t 4 t1) /\
    let z = venomLayout$ceil32 (w2n sz) in
      sm1 = (if z = 0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) /\
      fmp_stage_rel D C' sm1 fmp0 raw0 eom F stk PG
        (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
        (s1 with vs_inst_idx := SUC s.vs_inst_idx) (lo+z) t1 ts
Proof
  strip_tac >>
  drule_all frame_reachable_raw_certificate >> strip_tac >>
  `dalloca_no_wrap inst s` by metis_tac[] >>
  drule_all fmp_dalloca_source >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        s.vs_inst_idx < LENGTH bb.bb_instructions /\
        EL s.vs_inst_idx bb.bb_instructions = inst` by
    (drule_all o1_ctx_shape_active_lookup >>
     simp[get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >>
     qexists `bb` >> simp[] >> metis_tac[MEM_EL]) >>
  `!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `retpc_use_ok inst v` by metis_tac[opaque_use_ok_def] >>
     gvs[retpc_use_ok_def] >> gvs[opaque_use_ok_def, retpc_use_ok_def]) >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  qpat_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
  drule_all fmp_dalloca_lowered_needs >> strip_tac >>
  drule_all fmp_stage_root_exists >> strip_tac >>
  `~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp)` by
    metis_tac[fmp_dalloca_not_before_root] >>
  qpat_x_assum `s.vs_current_bb = t.vs_current_bb` (assume_tac o SYM) >>
  qpat_x_assum `(case fmp_stage_root infos ctx fn of NONE => _ | SOME _ => _)` mp_tac >>
  simp[] >> strip_tac >>
  `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
     (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
     (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
      then 1 else 0)` by
    (qpat_x_assum `t.vs_inst_idx = _` mp_tac >> simp[] >> decide_tac) >>
  `step_inst k C inst s = OK s1` by simp[] >>
  drule_all focus_fmp_dalloca_restored_run >> rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `op = size_op /\ out' = out /\ sz' = sz` by gvs[] >>
  qpat_x_assum `op = size_op` SUBST_ALL_TAC >>
  qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  qpat_x_assum `sz' = sz` SUBST_ALL_TAC >>
  `raw0 <= w2n s.vs_fmp /\ fmp0 <= lo` by fs[fmp_frontier_rel_def] >>
  qabbrev_tac `sm1 = if venomLayout$ceil32 (w2n sz) = 0 then sm else
      sm |+ ((w2n s.vs_fmp,venomLayout$ceil32 (w2n sz)),(lo,inst.inst_id))` >>
  `sm1 = (if venomLayout$ceil32 (w2n sz) = 0 then sm else
      sm |+ ((w2n s.vs_fmp,venomLayout$ceil32 (w2n sz)),(lo,inst.inst_id)))` by simp[Abbr `sm1`] >>
  `fmp_saved_rel C' sm1 fmp0 raw0 stk ts` by
    (simp[Abbr `sm1`] >> irule focus_fmp_dalloca_saved_upto >> metis_tac[]) >>
  `fmp_sites_ok sm1 fmp0 raw0 (lo+venomLayout$ceil32 (w2n sz)) s1.vs_fmp /\
   ld_memory_agree (fmp_ld_sites sm1) eom
     (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
   ld_shared_agree D s1.vs_call_ctx.cc_address (step_taint inst s s1 tn)
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1 /\
   s1.vs_returndata = t1.vs_returndata /\ s1.vs_halted = t1.vs_halted` by
    (drule fmp_dalloca_shared >> disch_then irule >>
     ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (qexists `size_op` >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`aligned`,`t.vs_inst_idx+4`,`mask`,`out`,`plus31`,`runner`,`sz`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fmp_frame_rel sm1 fmp0 raw0 (fmp_frame_base raw0 stk)
     (fmp_frame_lo fmp0 ts) (lo+venomLayout$ceil32 (w2n sz)) F fn fn' PG
     (step_prov PG G inst s1) (step_taint inst s s1 tn).t_var
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1` by
    (drule_at (Pat `fmp_frame_rel _ _ _ _ _ _ T _ _ _ _ _ _ _`)
       focus_fmp_dalloca_active_upto >>
     disch_then (drule_at (Pat `fmp_stage_lowered _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `fmp_ledger_ok _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
     disch_then (drule_at (Pat `gas_cut _ _ _`)) >>
     disch_then (drule_at (Pat `df_at NONE _ _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `fmp_stage_root _ _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `_ = (update_var _ _ _) with vs_inst_idx := _`)) >>
     disch_then irule >>
     qpat_assum `raw0 = w2n vs.vs_fmp` SUBST1_TAC >>
     rpt conj_tac >>> NTH_GOAL (simp[]) 13 >>> NTH_GOAL (simp[]) 14 >>> NTH_GOAL (gvs[]) 24 >> first_assum ACCEPT_TAC) >>
  `fmp_stage_rel D C' sm1 fmp0 raw0 eom F stk PG
     (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
     (s1 with vs_inst_idx := SUC s.vs_inst_idx)
     (lo+venomLayout$ceil32 (w2n sz)) t1 ts` by
    (rewrite_tac[fmp_stage_rel_def,venom_state_accfupds] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `fn'` >> conj_tac >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`t1`,`bb'`,`tail`,`runner`,`plus31`,`mask`,`aligned`,
    `ai`,`ni`,`mi`,`bi`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `DROP t.vs_inst_idx _ = _` mp_tac >>
     qpat_assum `t.vs_inst_idx = fmp_stage_tidx _ _ _ bb.bb_instructions _ + _`
       SUBST1_TAC >>
     qpat_assum `fmp_stage_root _ _ _ = SOME _` SUBST1_TAC >>
     simp[NoAsms]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `fmp_stage_rel _ _ sm1 _ _ _ F _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `raw0 = _` SUBST1_TAC >>
  qpat_assum `s1 = update_var _ _ _` SUBST1_TAC >>
  simp[NoAsms]
QED
