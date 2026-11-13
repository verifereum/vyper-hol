Theory fmpStageFmpStepsRetInvokeCode
Ancestors
  fmpStageControl fmpStageOpBase fmpStageRel fmpLowerDefs
  o1PassContract contextCodegenRel venomExecSemantics venomInst
  fmpStageFmpStepsInvokePosition fmpStageFmpStepsRetInvokeObserved
  fmpStageFmpStepsRetInvokeOrigin concretizeAnalysisMetadataOwnership
  concretizeStageLookup fmpStepBridge fmpStepSupply irSupply venomWf
  venomFnScheduleRunner list

Theorem fmp_return_root_excluded:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE /\
  (fn_is_context_entry ctx fn ==> entry_fn_no_params fn) ==>
  !rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\ lbl = rl ==>
    rp <> SUC idx
Proof
  rpt strip_tac >> gvs[] >>
  `INVOKE <> RETPC_PARAM` by simp[] >>
  metis_tac[fmp_stage_root_crossing]
QED

Theorem fmp_return_lowered_at[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb' j. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    j.inst_opcode = INVOKE /\ j.inst_id = (EL i bb.bb_instructions).inst_id /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions i +
      (if (lbl,i) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
      bb'.bb_instructions = j
Proof
  strip_tac >> drule_all fmp_stage_invoke_at >> strip_tac >>
  qexists `bb'` >> simp[] >>
  imp_res_tac fmp_lower_invoke_inst >> gvs[]
QED

Theorem fmp_return_saved_invoke_position[local]:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE ==>
  ?j. active_inst fn' j t /\ MEM j (fn_insts fn') /\
      j.inst_opcode = INVOKE /\ j.inst_id = inst.inst_id
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst` by
    (gvs[contextCodegenRelTheory.active_inst_def] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  gvs[fmp_frame_rel_def] >>
  drule_all fmp_return_lowered_at >> strip_tac >>
  qexists `j` >> simp[] >>
  `MEM bb' fn'.fn_blocks /\ bb'.bb_label = s.vs_current_bb` by
    (fs[lookup_block_def] >> conj_tac
     >- (irule FIND_MEM >> goal_assum (drule_at Any)) >>
     qpat_assum `FIND _ fn'.fn_blocks = SOME bb'`
       (mp_then Any mp_tac FIND_P) >> simp[]) >>
  conj_tac
  >- (simp[contextCodegenRelTheory.active_inst_def] >>
      qexists `bb'` >>
      qpat_x_assum `_ + _ < LENGTH bb'.bb_instructions` mp_tac >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >> strip_tac >>
      qpat_x_assum `EL (_ + _) bb'.bb_instructions = j` mp_tac >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >> strip_tac >> simp[]) >>
  simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
  qexists `bb'` >> simp[] >> metis_tac[EL_MEM]
QED

Theorem fmp_return_saved_invoke_code:
  fmp_stage_ctx rp D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t ==>
  ?j. active_inst fn' j t /\ j.inst_opcode = INVOKE /\
      j.inst_id = inst.inst_id /\ j.inst_outputs = inst.inst_outputs
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmpLowerPropsTheory.fmp_lookup_function_self >> simp[] >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
   fn_inst_ids_distinct fn` by
    gvs[o1_fn_shape_def, wf_function_def, fn_labels_def] >>
  drule_all fmp_return_saved_invoke_position >> strip_tac >>
  `?observed sp out. fn_pass_step rp (CFP_Simple VP_FmpLowering)
      observed sp fn out /\ out.fpo_function = fn' /\
      ctx_fn_names observed.cu_context = ctx_fn_names C /\
      o1_walk_view rp 3 C' fn observed` by
    (qpat_assum `fmp_stage_ctx _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [fmp_stage_ctx_def]) >>
     drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
     qexistsl_tac [`observed`,`s'`,`out`] >> simp[]) >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `!i name args callee sig.
    MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
    i.inst_operands = Label name::args /\
    lookup_function name observed.cu_context.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig ==> ~sig.fms_publishes` by
    (rpt strip_tac >>
     `MEM name (fn_invoke_targets fn)` by
       (simp[invoke_target_instruction] >> metis_tac[]) >>
     drule_all fmp_return_observed_callee_nonpublishing >> simp[]) >>
  drule fmp_return_function_origin >>
  disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >>
  `j.inst_outputs = inst.inst_outputs` by
    metis_tac[venomInstIdsPropsTheory.fn_inst_ids_distinct_inj] >>
  qexists `j` >> simp[]
QED

Theorem fmp_return_saved_invoke_boundary:
  fmp_stage_ctx rp D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  fmp_stage_lowered infos ctx runner fn fn' ==>
  ?j. active_inst fn' j t /\ j.inst_opcode = INVOKE /\
      j.inst_id = inst.inst_id /\ j.inst_outputs = inst.inst_outputs /\
      ~MEM runner j.inst_outputs /\
      (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
        s.vs_current_bb = rl ==> rp <> SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all fmp_return_saved_invoke_code >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `~MEM runner inst.inst_outputs` by
    (spose_not_then assume_tac >>
     qpat_x_assum `fmp_stage_lowered _ _ _ _ _` mp_tac >>
     simp[fmp_stage_lowered_def] >> rpt strip_tac >> gvs[] >>
     Cases_on `fresh_ir_var sp` >> gvs[] >>
     `EVERY (\v. MEM v sp.irs_used_vars) (fn_ir_vars fn)` by
       gvs[ir_supply_covers_fn_def, list_subset_def] >>
     drule_all fresh_ir_var_outside_function >> strip_tac >>
     qpat_x_assum `~MEM _ (fn_ir_vars fn)` mp_tac >>
     simp[fmpStepSupplyTheory.fn_ir_vars_member] >>
     gvs[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  qexists `j` >> simp[] >> rpt strip_tac >>
  `fn_is_context_entry ctx fn ==> entry_fn_no_params fn` by
    (drule_all fmp_stage_witness_pin >>
     gvs[o1_fn_shape_def]) >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  metis_tac[fmp_return_root_excluded]
QED

Theorem fmp_return_invoke_local_nonclearing[local]:
  inst.inst_opcode = INVOKE /\
  fmp_lower_inst infos ctx runner sp inst = SOME ([j],sp') /\
  LENGTH j.inst_outputs = LENGTH inst.inst_outputs ==>
  ~fmp_clears_marks infos inst
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_resolve_invoke_some >> strip_tac >>
  gvs[fmpReclaimDefsTheory.fmp_clears_marks_def,
      fmpReclaimDefsTheory.fmp_callee_info_def,
      fmpAnalysisDefsTheory.fmp_invoke_target_def] >>
  Cases_on `info.fi_publishes_fmp` >> gvs[]
QED

Theorem fmp_return_saved_invoke_nonclearing:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ t.vs_current_bb = lbl /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
    (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) /\
  active_inst fn' j t /\ j.inst_outputs = inst.inst_outputs ==>
  ~fmp_clears_marks infos inst
Proof
  strip_tac >>
  `fn_labels fn' = fn_labels fn` by
    (qpat_x_assum `fmp_stage_lowered _ _ _ _ _` mp_tac >>
     simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> drule fmp_checked_seal_some >> strip_tac >>
     gvs[fmp_seal_def, fn_labels_def] >>
     drule fmpStepLayoutTheory.fmp_install_root_preserves_labels >>
     drule fmpStepLayoutTheory.fmp_lower_blocks_preserves_labels >> simp[]) >>
  gvs[] >> drule_all fmp_stage_invoke_at >> strip_tac >- gvs[] >>
  gvs[active_inst_def] >> rename1 `MEM active_bb fn'.fn_blocks` >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME active_bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[fn_labels_def]) >>
  gvs[] >>
  irule fmp_return_invoke_local_nonclearing >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
