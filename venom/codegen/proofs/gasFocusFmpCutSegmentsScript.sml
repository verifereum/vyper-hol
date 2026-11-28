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
  gasFocusFmpGasPair fmpStageOpFrame lowerDloadPtrScalar decoderGhostFramePtr
  ptrDiscipline o1LowerDloadRelocationKernel o1LowerDloadShared
  livenessProofs venomExecSemantics rich_list codegenRel pred_set
  analysisSimDefs venomWfProps ctxLookupAgreeHelpers cfgWf gasEvents
  fmpStageReclaimSound ptrStaticDiscipline arithmetic
  gasFocusFmpCutPureEffect gasFocusFmpCutMemoryEffect gasFocusFmpCutSharedEffect
  gasFocusFmpCutExternalEffect fmpStageOpBase frameViewFacts passSimulationDefs

(* Ordinary instructions have no reclaim prefix, so the related target cursor
   points at the kept instruction itself. *)
Theorem cut_ordinary_kept_fetch[local]:
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL s.vs_inst_idx bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM] /\
  pre_fmp_opcode inst.inst_opcode /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts ==>
  ?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
        get_instruction bb' t.vs_inst_idx = SOME inst
Proof
  strip_tac >>
  gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `~fmp_is_reclaim_point infos (EL s.vs_inst_idx bb.bb_instructions)` by
    (irule fmpStageOpFrameTheory.fmp_ordinary_not_reclaim >> simp[]) >>
  `~((t.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn))` by
    metis_tac[fmp_stage_plan_point] >>
  `~MEM (EL s.vs_inst_idx bb.bb_instructions).inst_opcode
    [DALLOCA; INVOKE; RETPC_PARAM]` by simp[] >>
  drule fmp_stage_kept_inst >>
  disch_then (qspecl_then [`t.vs_current_bb`, `EL s.vs_inst_idx bb.bb_instructions`,
                          `s.vs_inst_idx`, `bb`] mp_tac) >>
  simp[get_instruction_def]
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
  `~fmp_is_reclaim_point infos inst` by (irule fmpStageOpFrameTheory.fmp_ordinary_not_reclaim >> gvs[]) >>
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
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
     (fn_is_context_entry ctx fn ==> entry_fn_no_params fn)) ==>
  (lbl,idx) NOTIN FDOM (fmp_stage_plan infos ctx fn) /\
  (!rp. fmp_stage_root infos ctx fn = SOME (lbl,rp) ==> rp <> SUC idx) /\
  fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
    lbl bb.bb_instructions (SUC idx) =
  SUC (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
    lbl bb.bb_instructions idx)
Proof
  strip_tac >> conj_asm1_tac
  >- (strip_tac >> drule_all fmp_stage_plan_point >> strip_tac >>
      `~fmp_is_reclaim_point infos inst` by (irule fmpStageOpFrameTheory.fmp_ordinary_not_reclaim >> gvs[]) >>
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
    sm1 = (if (venomLayout$ceil32 (w2n sz)) = 0 then sm else sm |+ ((w2n s.vs_fmp,(venomLayout$ceil32 (w2n sz))),(lo,inst.inst_id))) /\
    fmp_stage_rel D C' sm1 fmp0 raw0 eom F stk PG
      (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) (lo+(venomLayout$ceil32 (w2n sz))) t1 ts
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
  drule_all (CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) focus_fmp_dalloca_restored_run) >>
  strip_tac >>
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

Theorem cut_gas_ghost_updates[local]:
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  s1 = update_var out x (s with vs_gas_readings := rs) ==>
  step_prov PG G inst s1 = DRESTRICT G (COMPL {out}) /\
  step_taint inst s s1 tn = tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    simp[out_taint_opcode_exclusion, written_taint_opcode_exclusion] >>
  simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       set_var_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
       imm_taint_def, new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, update_var_def, FLOOKUP_DEF,
       taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem cut_gas_env_suc[local]:
  fmp_env_rel sm fn live G tv s t /\
  (!v. MEM v live' /\ v <> out ==> MEM v live) ==>
  fmp_env_rel sm fn live' (DRESTRICT G (COMPL {out})) (tv |+ (out,{}))
    ((update_var out x (s with vs_gas_readings := rs)) with vs_inst_idx := i)
    ((update_var out x (t with vs_gas_readings := rs)) with vs_inst_idx := j)
Proof
  strip_tac >> simp[fmp_env_rel_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> Cases_on `v = out`
  >- simp[FLOOKUP_DRESTRICT, fmp_value_rel_def, ld_value_agree_def,
          op_taint_def, FLOOKUP_UPDATE, word_agree_except_def] >>
  fs[fmp_env_rel_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* The ordinary slice changes the active index by one. The root has
   already been crossed or is still strictly ahead, and the analysis
   stack and ledger are transported on the same lowering witness. *)
Theorem cut_ordinary_frame_suc[local]:
  wf_function fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\ EL s.vs_inst_idx bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; SETFMP] /\
  (!infos ctx runner rl rp.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\
    ~MEM runner inst.inst_outputs) /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG G tv s t /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx))
    G' tv' (s1 with vs_inst_idx := SUC s.vs_inst_idx) (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
  (!env. fmp_base_analyze (fn_insts fn) = SOME env /\
         fmp_frame_covers sm env eb lo G ==> fmp_frame_covers sm env eb lo G') /\
  (!v. ~MEM v inst.inst_outputs ==> lookup_var v t1 = lookup_var v t) /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_params = s.vs_params /\ s1.vs_call_ctx = s.vs_call_ctx /\
  s1.vs_tx_ctx = s.vs_tx_ctx /\ s1.vs_block_ctx = s.vs_block_ctx /\
  s1.vs_data_section = s.vs_data_section /\ s1.vs_labels = s.vs_labels /\
  s1.vs_code = s.vs_code /\ s1.vs_prev_hashes = s.vs_prev_hashes /\
  s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
  t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
  t1.vs_params = t.vs_params /\ t1.vs_call_ctx = t.vs_call_ctx /\
  t1.vs_tx_ctx = t.vs_tx_ctx /\ t1.vs_block_ctx = t.vs_block_ctx /\
  t1.vs_data_section = t.vs_data_section /\ t1.vs_labels = t.vs_labels /\
  t1.vs_code = t.vs_code /\ t1.vs_prev_hashes = t.vs_prev_hashes /\
  t1.vs_initial_fmp = t.vs_initial_fmp ==>
  fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG G' tv'
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) (t1 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> fs[fmp_frame_rel_def] >>
  qexistsl [`infos`, `ctx`, `runner`] >>
  `~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM]` by fs[] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
     (fn_is_context_entry ctx fn ==> entry_fn_no_params fn)` by metis_tac[] >>
  drule_all cut_ordinary_control_suc >> strip_tac >>
  qpat_x_assum `s.vs_current_bb = t.vs_current_bb` (SUBST_ALL_TAC o SYM) >>
  fs[fmp_params_rel_def] >>
  qpat_assum `t.vs_inst_idx = _` SUBST_ALL_TAC >> gs[] >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!b z c id. FLOOKUP sm (b,z) = _ ==> _`
       (qspecl_then [`b`, `z`, `c`, `id`] mp_tac) >> simp[]) >>
  Cases_on `fmp_stage_root infos ctx fn` >- fs[] >>
  PairCases_on `x` >> fs[] >>
  rename1 `fmp_stage_root infos ctx fn = SOME (rl,rp)` >>
  `s.vs_current_bb = rl ==> rp <> SUC s.vs_inst_idx` by metis_tac[] >>
  `~MEM runner inst.inst_outputs` by metis_tac[] >>
  `~MEM inst.inst_opcode [INVOKE; DALLOCA; SETFMP]` by fs[] >>
  drule_all cut_ordinary_root_suc >>
  disch_then (qspec_then `SUC (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (SOME (rl,rp)) s.vs_current_bb bb.bb_instructions s.vs_inst_idx)` strip_assume_tac) >>
  qexists `st'` >> gvs[]
QED

(* Once the concrete executions have supplied their output and memory effects,
   all other fields follow from nonterminator preservation. *)
Theorem cut_ordinary_stage_suc[local]:
  wf_function fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\ EL s.vs_inst_idx bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; SETFMP; PHI] /\
  ~is_alloca_op inst.inst_opcode /\
  (!infos ctx runner rl rp.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\
    ~MEM runner inst.inst_outputs) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  active_inst fn inst s /\ fn_static_ptr_ok P fn /\ fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\ pre_fmp_ops fn /\
  EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==> b + z <= fmp_frame_base raw0 stk) PG /\
  step_inst k C inst s = OK s1 /\ step_inst_base inst t = OK t1 /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
    ?y. FLOOKUP t1.vs_vars v = SOME y /\
      (~retpc_var fn v ==> fmp_value_rel sm
        (FLOOKUP (step_prov PG G inst s1) v)
        (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
    (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
Proof
  strip_tac >>
  `step_inst_base inst s = OK s1` by (fs[step_inst_non_invoke] >> (gvs[step_inst_non_invoke])) >>
  `!env. fmp_base_analyze (fn_insts fn) = SOME env /\
     fmp_frame_covers sm env (fmp_frame_base raw0 stk) lo G ==>
     fmp_frame_covers sm env (fmp_frame_base raw0 stk) lo (step_prov PG G inst s1)` by
    (rpt strip_tac >> irule fmp_stage_covers_step >> simp[] >>
     conj_tac >- metis_tac[fmp_stage_rel_def, fmp_sites_ok_def] >>
     conj_tac >- fs[MEM] >>
     conj_tac >-
       (qpat_x_assum `EVERY _ PG` mp_tac >>
        simp[EVERY_MEM] >> disch_then assume_tac >>
        qx_gen_tac `h` >> disch_tac >>
        map_every qx_gen_tac [`b`, `z`] >> strip_tac >>
        qpat_x_assum `!h. MEM h PG ==> _`
          (qspec_then `h` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (qspecl_then [`b`, `z`] mp_tac) >>
        impl_tac >- simp[] >> decide_tac) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  map_every (fn eq => qpat_assum eq
    (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac step_inst_base_preserves_all) >>
    simp[] >> strip_tac)
    [`step_inst_base inst s = OK s1`, `step_inst_base inst t = OK t1`] >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  `fn'' = fn'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `fn'' = fn'` SUBST_ALL_TAC >>
  `fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tn.t_var s t` by fs[fmp_frame_rel_def] >>
  `fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx))
    (step_prov PG G inst s1) (step_taint inst s s1 tn).t_var
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
    (simp[fmp_env_rel_def] >> rpt strip_tac >> Cases_on `MEM v inst.inst_outputs`
     >- (qpat_assum `!v x. MEM v inst.inst_outputs /\ _ ==> _`
           (drule_all_then strip_assume_tac) >> qexists `y` >> fs[op_taint_def]) >>
     `FLOOKUP s.vs_vars v = SOME x /\ FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v` by
       gvs[GSYM lookup_var_def] >>
     qpat_assum `fmp_env_rel _ _ _ _ _ _ _`
       (qspecl_then [`v`, `x`] mp_tac o REWRITE_RULE [fmp_env_rel_def]) >>
     simp[] >> strip_tac >> qexists `y` >>
     simp[step_prov_other_output] >> strip_tac >>
     `MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)` by
       (drule live_vars_at_propagate >> simp[inst_defs_def] >>
        disch_then irule >> simp[] >> qexists `bb` >> simp[]) >>
     `op_taint (step_taint inst s s1 tn) (Var v) = op_taint tn (Var v)` by
       simp[step_taint_other_output] >>
     fs[op_taint_def]) >>
  rewrite_tac[fmp_stage_rel_def] >>
  conj_tac >- gvs[] >>
  conj_tac >-
    (qexists `fn'` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule cut_ordinary_frame_suc >> gs[] >> metis_tac[]) >>
  qpat_assum `ld_shared_agree D _ _ s1 t1`
    (mp_tac o REWRITE_RULE [ld_shared_agree_def]) >>
  simp[ld_shared_agree_def]
QED

Theorem cut_gas_frame_suc[local]:
  wf_function fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\ EL s.vs_inst_idx bb.bb_instructions = inst /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  (!infos ctx runner rl rp.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\ runner <> out) /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG G tv s t ==>
  fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG
    (DRESTRICT G (COMPL {out})) (tv |+ (out,{}))
    ((update_var out x (s with vs_gas_readings := rs)) with vs_inst_idx := SUC s.vs_inst_idx)
    ((update_var out x (t with vs_gas_readings := rs)) with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx)) /\
       v <> out ==> MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)` by
    (rpt strip_tac >> drule live_vars_at_propagate >> simp[inst_defs_def] >>
     disch_then irule >> qexists `bb` >> simp[]) >>
  `fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx))
    (DRESTRICT G (COMPL {out})) (tv |+ (out,{}))
    ((update_var out x (s with vs_gas_readings := rs)) with vs_inst_idx := SUC s.vs_inst_idx)
    ((update_var out x (t with vs_gas_readings := rs)) with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule cut_gas_env_suc >>
     qexists `live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx` >>
     gvs[fmp_frame_rel_def]) >>
  irule cut_ordinary_frame_suc >>
  simp[update_var_def, is_terminator_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G`,`tv`] >> simp[] >>
  simp[fmp_frame_covers_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

(* Rebuild the stage relation on the two actual scalar updates. The site
   geometry, memory and suspended frames do not change. *)
Theorem cut_gas_stage_suc[local]:
  wf_function fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\ EL s.vs_inst_idx bb.bb_instructions = inst /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  (!infos ctx runner rl rp.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\ runner <> out) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  s1 = update_var out x (s with vs_gas_readings := rs) /\
  u = update_var out x (t with vs_gas_readings := rs) ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
    (u with vs_inst_idx := SUC t.vs_inst_idx) ts
Proof
  strip_tac >>
  qpat_x_assum `u = _` mp_tac >> drule_all cut_gas_ghost_updates >> strip_tac >> strip_tac >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  `fn'' = fn'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `fn'' = fn'` SUBST_ALL_TAC >>
  rewrite_tac[fmp_stage_rel_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >-
    (qexists `fn'` >> conj_tac >- first_assum ACCEPT_TAC >>
     drule_all cut_gas_frame_suc >>
     (simp[])) >>
  simp[update_var_def] >> fs[ld_shared_agree_def]
QED

Theorem focus_fmp_cut_gas_segment:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  ssa_form fn /\ fn.fn_fmp_signature = NONE /\
  active_inst fn inst s /\ inst.inst_opcode = GAS /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = OK s1 ==>
  ?fn' bb bb' tail u.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    DROP t.vs_inst_idx bb'.bb_instructions = inst::tail /\
    (!k'. fmp_target_run k' C' fn.fn_name t 1
      (u with vs_inst_idx := SUC t.vs_inst_idx)) /\
    (!k. gas_events_step k C fn.fn_name inst s = [(fn.fn_name,inst.inst_id)]) /\
    (!k'. gas_events_step k' C' fn'.fn_name inst t = [(fn.fn_name,inst.inst_id)]) /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
      (u with vs_inst_idx := SUC t.vs_inst_idx) ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ (C.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn)` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `pre_fmp_ops fn /\ all_reachable fn` by
    fs[o1_fn_row_def, make_ssa_input_ok_def, EVERY_MEM] >>
  drule_all focus_fmp_selected_root_pin >> strip_tac >>
  drule_all focus_fmp_gas_pair >> disch_then (qspec_then `C` strip_assume_tac) >>
  qpat_x_assum `!k s1. step_inst _ _ _ _ = OK _ ==> _` (drule_then strip_assume_tac) >>
  rename1 `!k'. step_inst k' C' inst t = OK u` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\ EL s.vs_inst_idx bb.bb_instructions = inst /\
   t.vs_inst_idx < LENGTH bb'.bb_instructions /\ EL t.vs_inst_idx bb'.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> qexists `bb` >> simp[] >> metis_tac[MEM_EL]) >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[all_reachable_def, fn_reachable_in_cfg_dfs_pre] >>
  `!infos ctx runner rl rp.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\ runner <> out` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!infos ctx runner rl rp. _ ==> _`
       (drule_all_then strip_assume_tac) >>
     conj_tac >- simp[] >>
     qpat_x_assum `!j. MEM j (fn_insts fn) ==> _` (qspec_then `inst` mp_tac) >> simp[]) >>
  drule_all cut_gas_stage_suc >> strip_tac >>
  `DROP t.vs_inst_idx bb'.bb_instructions = inst::DROP (t.vs_inst_idx+1) bb'.bb_instructions` by
    (drule DROP_EL_CONS >> simp[]) >>
  qexistsl [`fn'`,`bb`,`bb'`,`DROP (t.vs_inst_idx+1) bb'.bb_instructions`,`u`] >>
  simp[] >> gen_tac >>
  simp[fmp_target_run_def] >> qexists `u` >>
  simp[run_insts_def, arithmeticTheory.ADD1]
QED

val ordinary_pure = ``[CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
  COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
  CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE; BLOCKHASH; BLOBHASH;
  BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD] ++
  [Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT; ISZERO; AND; OR; XOR;
   NOT; SIGNEXTEND; BYTE; OFFSET] ++
  [ADD; SUB; MUL; EQ; LT; GT; SHL; SHR; SAR; PARAM; ASSIGN] ++
  [NOP; ASSERT; ASSERT_UNREACHABLE]``;
val ordinary_memory = ``[MLOAD; ILOAD; SHA3] ++
  [MSTORE; MSTORE8; MCOPY; CALLDATACOPY; CODECOPY; RETURNDATACOPY;
   EXTCODECOPY; DLOADBYTES]``;
val ordinary_shared = ``[SLOAD; TLOAD; SSTORE; TSTORE; ISTORE; LOG]``;
val ordinary_external = ``[CALL; STATICCALL; DELEGATECALL] ++ [CREATE; CREATE2]``;

Theorem cut_ordinary_class[local]:
  ~is_terminator op /\ ~MEM op [INVOKE; DALLOCA; RETPC_PARAM; PHI; GAS] /\
  pre_fmp_opcode op /\ op <> ALLOCA /\ op <> MEMTOP ==>
  MEM op ^ordinary_pure \/ MEM op ^ordinary_memory \/
  MEM op ^ordinary_shared \/ MEM op ^ordinary_external
Proof
  Cases_on `op` >> simp[is_terminator_def, pre_fmp_opcode_def]
QED

Theorem cut_ordinary_assign_operand[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  MEM inst (fn_insts fn) /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      (~retpc_var fn out ==> fmp_value_rel sm (op_prov G op) (op_taint tn op) x y)
Proof
  strip_tac >> Cases_on `!v. op = Var v ==> ~retpc_var fn v`
  >- (`inst.inst_opcode <> PHI /\ MEM op inst.inst_operands` by simp[] >>
      drule_all fmp_stage_operand_point >> metis_tac[]) >>
  gvs[] >>
  `retpc_var fn out` by
    (gvs[retpc_var_def] >> irule (cj 2 copy_phi_var_rules) >>
     qexistsl [`inst`, `v`] >> simp[]) >>
  fs[eval_operand_def, lookup_var_def, fmp_stage_rel_def,
     fmp_frame_rel_def, fmp_env_rel_def] >> metis_tac[]
QED

Theorem cut_access_raise_floor[local]:
  eom <= lo /\ access_ok eom G fn inst s ==> access_ok lo G fn inst s
Proof
  simp[access_ok_def] >> strip_tac >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  disch_tac >>
  qpat_x_assum `~in_revert_forward fn s ==> _` (drule_then strip_assume_tac) >>
  conj_tac >> rpt gen_tac >> disch_tac
  >- (qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges inst s) /\ _ ==> _`
        (qspecl_then [`off`,`len`] irule) >>
      fs[] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  qpat_x_assum `!off len. MEM (off,len) (source_memory_read_ranges inst s) /\ _ ==> _`
    (qspecl_then [`off`,`len`] irule) >>
  fs[] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Theorem cut_ordinary_returndata[local]:
  MEM inst.inst_opcode (^ordinary_pure ++ ^ordinary_memory) /\
  step_inst_base inst s = OK s1 ==> s1.vs_returndata = s.vs_returndata
Proof
  strip_tac >>
  irule venomInstProofsTheory.write_effects_sound_returndata >>
  qexistsl [`C`,`k`,`inst`] >>
  gvs[MEM, is_alloca_op_def, is_terminator_def, step_inst_non_invoke,
      venomEffectsTheory.write_effects_def, venomEffectsTheory.empty_effects_def]
QED

(* Use the four integrated effect proofs at the actual point. Only the OK
   arm carries data into the next cursor; terminal results already agree. *)
Theorem cut_ordinary_effect[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  gas_cut n vs s /\ taint_within_upto D n C vs /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  MEM inst (fn_insts fn) /\ inst_wf inst /\ access_ok eom G fn inst s /\
  taint_ok fn tn inst s /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; GAS] /\
  pre_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> ALLOCA /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  eom <= fmp0 /\ step_inst_base inst s = r /\ terminates r ==>
  ?r'. step_inst_base inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
          ?y. FLOOKUP t1.vs_vars v = SOME y /\
            (~retpc_var fn v ==> fmp_value_rel sm
              (FLOOKUP (step_prov PG G inst s1) v)
              (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P fn) inst /\ inst.inst_opcode <> MEMTOP` by
    metis_tac[fn_static_ptr_ok_def] >>
  `fmp0 <= raw0 /\ eom <= lo /\ s.vs_returndata = t.vs_returndata` by
    (fs[fmp_stage_rel_def, fmp_frame_rel_def, fmp_frontier_rel_def] >> decide_tac) >>
  `inst.inst_opcode <> PHI /\ inst.inst_opcode <> RET /\
   inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET` by
    (fs[pre_fmp_opcode_def] >> metis_tac[is_terminator_def]) >>
  `inst.inst_opcode <> ASSIGN ==> !v. MEM (Var v) inst.inst_operands ==>
     ~retpc_var fn v` by metis_tac[ordinary_operand_not_retpc] >>
  let
    val finish_readonly =
      strip_tac >>
      `MEM inst.inst_opcode (^ordinary_pure ++ ^ordinary_memory)` by
        pure_asm_rewrite_tac[MEM_APPEND, boolTheory.OR_CLAUSES] >>
      `!x. step_inst_base inst s = OK x ==> x.vs_returndata = s.vs_returndata` by
        (rpt strip_tac >> drule_all cut_ordinary_returndata >> simp[]) >>
      `!x. step_inst_base inst t = OK x ==> x.vs_returndata = t.vs_returndata` by
        (rpt strip_tac >> drule_all cut_ordinary_returndata >> simp[]) >>
      ntac 2 (qpat_x_assum `MEM inst.inst_opcode _` kall_tac) >>
      qexists `r'` >> Cases_on `r` >> gvs[terminates_def]
  in
  drule_all cut_ordinary_class >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN assume_tac)))
  >- (`access_ok lo G fn inst s` by metis_tac[cut_access_raise_floor] >>
      `(inst.inst_opcode <> ASSIGN ==> !op x.
         MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
         ?y. eval_operand op t = SOME y /\
            fmp_value_rel sm (op_prov G op) (op_taint tn op) x y) /\
       (inst.inst_opcode = ASSIGN ==> !op x out.
         inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
         eval_operand op s = SOME x ==> ?y. eval_operand op t = SOME y /\
         (~retpc_var fn out ==> fmp_value_rel sm (op_prov G op) (op_taint tn op) x y))` by
        (conj_tac
         >- (rpt strip_tac >> `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[] >>
             drule_all fmp_stage_operand_point >> simp[]) >>
         rpt strip_tac >> drule_all cut_ordinary_assign_operand >> simp[]) >>
      drule_all focus_fmp_cut_pure_effect >> finish_readonly)
  >- (`inst.inst_opcode <> ASSIGN` by (strip_tac >> gvs[MEM]) >>
      `!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v` by metis_tac[] >>
      drule_all focus_fmp_cut_memory_effect >> finish_readonly)
  >- (drule_all focus_fmp_cut_shared_effect >> strip_tac >>
      qpat_x_assum `MEM inst.inst_opcode _` kall_tac >>
      qexists `r'` >> Cases_on `r` >> gvs[terminates_def]) >>
  drule_all focus_fmp_cut_external_effect >> strip_tac >>
  qpat_x_assum `MEM inst.inst_opcode _` kall_tac >>
  qexists `r'` >> Cases_on `r` >> gvs[terminates_def]
  end
QED

Theorem focus_fmp_cut_ordinary_segment:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  ssa_form fn /\ fn.fn_fmp_signature = NONE /\ opaque_use_ok fn /\
  active_inst fn inst s /\ frame_reachable vs C stk PG G tn fn inst s /\
  gas_cut n vs s /\ taint_within_upto D n C vs /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\ eom <= fmp0 /\
  EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==> b + z <= fmp_frame_base raw0 stk) PG /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?fn' bb bb' tail r'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    DROP t.vs_inst_idx bb'.bb_instructions = inst::tail /\
    (!k'. step_inst k' C' inst t = r') /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!k'. fmp_target_run k' C' fn.fn_name t 1
          (t1 with vs_inst_idx := SUC t.vs_inst_idx)) /\
        fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
          (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
          (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
          (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ fn_inst_wf fn /\
   (C.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn)` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `pre_fmp_ops fn /\ make_ssa_input_ok fn /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)` by
    (qpat_assum `EVERY (o1_fn_row 3) C.ctx_functions`
       (qspec_then `fn` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[o1_fn_row_def]) >>
  drule_all o1_ctx_shape_active_lookup >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\ EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
  `MEM inst (fn_insts fn) /\ inst_wf inst` by
    metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM, fn_inst_wf_def] >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `step_inst_base inst s = r` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (`?s1. r = OK s1` by
        (qpat_x_assum `step_inst_base inst s = r` (SUBST_ALL_TAC o SYM) >>
         qpat_x_assum `terminates (step_inst_base _ _)` mp_tac >>
         namedCases_on `inst.inst_outputs` ["", "out outs"]
         >- simp[step_inst_base_opcode_eqs, exec_gas_def, terminates_def] >>
         Cases_on `outs`
         >- (Cases_on `s.vs_gas_readings` >>
             simp[step_inst_base_opcode_eqs, exec_gas_def]) >>
         simp[step_inst_base_opcode_eqs, exec_gas_def, terminates_def]) >>
      `step_inst k C inst s = OK s1` by fs[] >>
      drule_all focus_fmp_cut_gas_segment >> strip_tac >>
      rename1 `DROP t.vs_inst_idx btgt.bb_instructions = inst::tail` >>
      `?v. step_inst_base inst t = OK v /\
           (v with vs_inst_idx := SUC t.vs_inst_idx) =
           (u with vs_inst_idx := SUC t.vs_inst_idx)` by
        (qpat_assum `!k'. fmp_target_run k' _ _ _ _ _` (qspec_then `0` mp_tac) >>
         rewrite_tac[fmp_target_run_def] >>
         disch_then (qx_choosel_then [`tf`,`tb`,`v`] strip_assume_tac) >>
         `tf = fn' /\ tb = btgt` by metis_tac[optionTheory.SOME_11] >>
         `EL t.vs_inst_idx btgt.bb_instructions = inst` by
           (mp_tac (Q.ISPECL [`t.vs_inst_idx`,`btgt.bb_instructions`] listTheory.HD_DROP) >>
            fs[]) >>
         qexists `v` >>
         Cases_on `step_inst_base inst t` >>
         gvs[run_insts_def, step_inst_non_invoke, arithmeticTheory.ADD1]) >>
      qexistsl [`fn'`,`bb'`,`btgt`,`tail`,`OK v`] >> simp[step_inst_non_invoke]) >>
  `pre_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> ALLOCA` by
    fs[pre_fmp_ops_def, EVERY_MEM] >>
  `~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; GAS] /\
   ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; SETFMP; PHI] /\
   ~is_alloca_op inst.inst_opcode` by
    (fs[pre_fmp_opcode_def] >> Cases_on `inst.inst_opcode` >>
     simp[NoAsms, is_alloca_op_def] >> metis_tac[]) >>
  drule_all focus_fmp_selected_root_pin >> strip_tac >>
  `~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM]` by fs[MEM] >>
  drule_all cut_ordinary_kept_fetch >> strip_tac >>
  `t.vs_inst_idx < LENGTH bb'.bb_instructions /\ EL t.vs_inst_idx bb'.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `DROP t.vs_inst_idx bb'.bb_instructions = inst::DROP (t.vs_inst_idx+1) bb'.bb_instructions` by
    (drule DROP_EL_CONS >> simp[]) >>
  drule_all cut_ordinary_effect >> strip_tac >>
  qexistsl [`fn'`,`bb`,`bb'`,`DROP (t.vs_inst_idx+1) bb'.bb_instructions`,`r'`] >>
  simp[step_inst_non_invoke] >>
  Cases_on `r` >> fs[terminates_def] >>
  conj_tac
  >- (simp[fmp_target_run_def, run_insts_def, step_inst_non_invoke, arithmeticTheory.ADD1]) >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[make_ssa_input_ok_def, all_reachable_def, fn_reachable_in_cfg_dfs_pre] >>
  `!infos ctx runner rl rp.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\
    ~MEM runner inst.inst_outputs` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!infos ctx runner rl rp. _ ==> _` (drule_all_then strip_assume_tac) >>
     simp[]) >>
  `~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; SETFMP; PHI]` by simp[] >>
  `step_inst_base inst t = OK t1` by simp[] >>
  drule_all cut_ordinary_stage_suc >> simp[]
QED
