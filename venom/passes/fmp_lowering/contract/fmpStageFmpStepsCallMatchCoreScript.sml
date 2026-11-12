Theory fmpStageFmpStepsCallMatchCore
Ancestors
  fmpStageFmpStepsCallOrdinal fmpStageFmpStepsCallAbi
  fmpStageOpBase fmpStageControl fmpStageRel fmpLowerDefs fmpLowerProps fmpStepLayout fcgBridge
  fmpAnalysisDefs fmpAnalysisProps fmpWfDefs o1PassContract contextCodegenRel
  venomInst venomExecSemantics venomWf list rich_list finite_map words arithmetic combinatorics

Theorem call_collect_member[local]:
  !insts targets inst nm ops.
  fmp_collect_invokes insts = SOME targets /\ MEM inst insts /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) ==>
  MEM nm targets
Proof
  Induct >> simp[fmp_collect_invokes_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  gvs[fmp_invoke_target_def, decode_invoke_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem call_needs_caller[local]:
  analyze_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  FLOOKUP infos nm = SOME ci /\ ci.fi_needs_fmp ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp
Proof
  strip_tac >> drule analyze_fmp_context_valid >>
  simp[fmp_info_valid_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `MEM nm targets` by
    (gvs[fmp_function_targets_def, AllCaseEqs()] >>
     metis_tac[call_collect_member]) >>
  drule fmp_join_target_info_needs_iff >> strip_tac >> metis_tac[]
QED

Theorem call_ordinal_decode[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL idx bb.bb_instructions) = SOME (nm,ops) /\
  EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions)))
    (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) = inst' ==>
  (inst' = EL idx bb.bb_instructions /\ fmp_stage_root infos ctx fn = NONE) \/
  ?callee info sig.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig /\ info = fmp_info_of_signature sig /\
    FLOOKUP infos nm = SOME info /\ inst'.inst_opcode = INVOKE /\
    decode_invoke inst' = SOME (nm,ops ++ if info.fi_needs_fmp then [Var runner] else [])
Proof
  strip_tac >>
  Cases_on `?info. FLOOKUP infos fn.fn_name = SOME info /\
                      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (disj2_tac >> drule_all fmp_stage_lowered_invoke_block >> strip_tac >>
      drule fmp_lower_indexed_invoke_at >>
      disch_then (qspec_then `idx` mp_tac) >> simp[] >> strip_tac >>
      drule_all fmp_lower_inst_invoke_filter >> strip_tac >>
      gvs[] >>
      drule fmp_resolve_invoke_some >> strip_tac >>
      `callee.fn_name = name` by metis_tac[lookup_function_name] >>
      qpat_x_assum `_ with <| inst_operands := _; inst_outputs := _ |> = _`
        (assume_tac o GSYM) >>
      gvs[decode_invoke_def]) >>
  disj1_tac >> drule fmp_stage_unlowered >> simp[] >> strip_tac >>
  gvs[] >> irule passSharedPropsTheory.filter_take_el >> simp[]
QED

Theorem call_needs_root[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp ==>
  IS_SOME (fmp_stage_root infos ctx fn)
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  gvs[fmp_lower_input_def, fmp_stage_root_def, AllCaseEqs()] >>
  Cases_on `fn.fn_blocks` >> gvs[split_fmp_entry_def] >>
  Cases_on `split_fmp_entry_from 0 [] h.bb_instructions` >> gvs[] >>
  Cases_on `x` >> simp[]
QED

Theorem call_unlowered_no_dalloca[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  ~(?info. FLOOKUP infos fn.fn_name = SOME info /\
             (info.fi_needs_fmp \/ info.fi_publishes_fmp)) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  gvs[] >>
  `no_raw_fmp_ops fn` by
    (irule fmp_no_need_input_no_raw >> metis_tac[]) >>
  gvs[no_raw_fmp_ops_def, EVERY_MEM] >>
  metis_tac[is_raw_fmp_opcode_def]
QED

Theorem call_restored_location[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  wf_function fn /\ ALL_DISTINCT (fn_labels fn') /\ active_inst fn inst s /\ active_inst fn' inst' t /\
  inst.inst_opcode = INVOKE /\ s.vs_current_bb = t.vs_current_bb /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) s.vs_current_bb
    (case lookup_block s.vs_current_bb fn.fn_blocks of SOME bb => bb.bb_instructions | NONE => [])
    s.vs_inst_idx +
    (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) /\
  (!rl rp bb idx. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
     lookup_block rl fn.fn_blocks = SOME bb /\ idx < LENGTH bb.bb_instructions /\
     (EL idx bb.bb_instructions).inst_opcode = INVOKE ==> rp <= idx) ==>
  ?bb bb'. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
    bb.bb_label = s.vs_current_bb /\ inst = EL s.vs_inst_idx bb.bb_instructions /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
          (TAKE s.vs_inst_idx bb.bb_instructions)))
       (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) = inst'
Proof
  strip_tac >>
  gvs[active_inst_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
  `lookup_block bb'.bb_label fn'.fn_blocks = SOME bb'` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  Cases_on `?info. FLOOKUP infos fn.fn_name = SOME info /\
                      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (drule fmp_stage_restored_invoke_at >>
      disch_then (qspecl_then [`s.vs_inst_idx`,`bb`] mp_tac) >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      gvs[lookup_block_def, FIND_thm] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> DALLOCA) bb.bb_instructions` by
    (drule_all call_unlowered_no_dalloca >>
     simp[fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  drule fmp_stage_unlowered >> simp[] >> strip_tac >>
  `!j. j < s.vs_inst_idx ==> (EL j bb.bb_instructions).inst_opcode <> DALLOCA` by
    (gvs[EVERY_EL] >> metis_tac[LESS_TRANS]) >>
  `GENLIST (\j. if (EL j bb.bb_instructions).inst_opcode = DALLOCA then (4:num) else 1)
      s.vs_inst_idx = GENLIST (K 1) s.vs_inst_idx` by
    (irule GENLIST_CONG >> simp[]) >>
  gvs[fmp_stage_tidx_def, SUM_GENLIST_K] >>
  simp[passSharedPropsTheory.filter_take_el] >>
  qpat_x_assum `GENLIST _ _ = _` SUBST1_TAC >>
  simp[NoAsms, SUM_GENLIST_K]
QED

Theorem call_frame_witness[local]:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  wf_function fn /\ ALL_DISTINCT (fn_labels fn') /\ fn.fn_fmp_signature = NONE /\
  active_inst fn inst s /\ active_inst fn' inst' t /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  (!infos ctx runner rl rp bb idx.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    lookup_block rl fn.fn_blocks = SOME bb /\ idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_opcode = INVOKE ==> rp <= idx) ==>
  ?infos ctx runner bb bb'.
    fmp_stage_lowered infos ctx runner fn fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
    bb.bb_label = s.vs_current_bb /\
    inst = EL s.vs_inst_idx bb.bb_instructions /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
       (TAKE s.vs_inst_idx bb.bb_instructions)))
       (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) = inst' /\
    (IS_SOME (fmp_stage_root infos ctx fn) ==>
      lookup_var runner t = SOME (n2w lo))
Proof
  simp[fmp_frame_rel_def] >> rpt strip_tac >>
  `!rl rp bb idx. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    lookup_block rl fn.fn_blocks = SOME bb /\ idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_opcode = INVOKE ==> rp <= idx` by metis_tac[] >>
  drule call_restored_location >>
  disch_then (qspecl_then [`t`,`s`,`inst'`,`inst`] mp_tac) >>
  (impl_tac >- (simp[ADD_COMM] >> metis_tac[])) >> strip_tac >>
  qexistsl [`infos`,`ctx`,`runner`,`bb`,`bb'`] >> simp[] >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  `~(t.vs_current_bb = x0 /\ s.vs_inst_idx < x1)` by metis_tac[NOT_LESS] >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[]
QED

Theorem call_lowered_resolve[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) ==>
  ?callee sig. lookup_function nm ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig /\
    FLOOKUP infos nm = SOME (fmp_info_of_signature sig) /\
    MEM fn ctx.ctx_functions
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  `IS_SOME (fmp_resolve_invoke infos ctx inst)` by
    (gvs[fmp_lower_input_def, fmp_lower_blocks_shape_def,
         fmp_lower_insts_shape_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     `fmp_lower_inst_shape infos ctx inst` by metis_tac[] >>
     gvs[fmp_lower_inst_shape_def]) >>
  Cases_on `fmp_resolve_invoke infos ctx inst` >> gvs[] >>
  PairCases_on `x` >> drule fmp_resolve_invoke_some >> strip_tac >>
  gvs[decode_invoke_def] >>
  metis_tac[lookup_function_MEM, fmp_lower_input_def]
QED

Theorem call_witness_decode[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lookup_block bb.bb_label fn'.fn_blocks = SOME bb' /\
  MEM (EL idx bb.bb_instructions) (fn_insts fn) /\ idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL idx bb.bb_instructions) = SOME (nm,ops) /\
  EL (LENGTH (FILTER (\i. i.inst_opcode = INVOKE) (TAKE idx bb.bb_instructions)))
    (FILTER (\i. i.inst_opcode = INVOKE) bb'.bb_instructions) = inst' ==>
  ?callee sig.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig /\
    FLOOKUP infos nm = SOME (fmp_info_of_signature sig) /\
    inst'.inst_opcode = INVOKE /\
    decode_invoke inst' = SOME (nm,ops ++ if sig.fms_has_fmp_param then [Var runner] else []) /\
    (sig.fms_has_fmp_param ==> IS_SOME (fmp_stage_root infos ctx fn))
Proof
  strip_tac >> drule_all call_lowered_resolve >> strip_tac >>
  `sig.fms_has_fmp_param ==> IS_SOME (fmp_stage_root infos ctx fn)` by
    (strip_tac >>
     `analyze_fmp_context ctx = SOME infos` by gvs[fmp_stage_lowered_def] >>
     `?info. FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp` by
       (irule call_needs_caller >> simp[] >>
        reverse conj_tac >- metis_tac[] >>
        qexistsl [`fmp_info_of_signature sig`,`EL idx bb.bb_instructions`,`nm`,`ops`] >>
        simp[fmp_info_of_signature_def]) >>
     irule call_needs_root >> metis_tac[]) >>
  drule_all call_ordinal_decode >> strip_tac >>
  gvs[fmp_info_of_signature_def]
QED

Theorem call_decode_decision[local]:
  decode_invoke inst = SOME (nm,ops ++ if p then [Var x] else []) /\
  decode_invoke inst = SOME (nm,ops ++ if q then [Var y] else []) ==>
  (p <=> q)
Proof
  Cases_on `p` >> Cases_on `q` >> simp[] >> strip_tac >> gvs[]
QED

Theorem call_actual_callee_root[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  lookup_function nm C.ctx_functions = SOME callee /\
  callee.fn_fmp_signature = NONE /\ C.ctx_entry <> SOME nm /\
  o1_walk_view rpolicy 3 C' fn observed /\ MEM nm (fn_invoke_targets fn) /\
  lookup_function nm observed.cu_context.ctx_functions = SOME seen /\
  seen.fn_fmp_signature = SOME sig ==>
  ?callee' infos_c ctx_c runner_c.
    lookup_function nm C'.ctx_functions = SOME callee' /\
    fmp_stage_lowered infos_c ctx_c runner_c callee callee' /\
    ~fn_is_context_entry ctx_c callee /\
    (sig.fms_has_fmp_param <=> IS_SOME (fmp_stage_root infos_c ctx_c callee))
Proof
  strip_tac >> drule_all fmp_call_actual_witness >> strip_tac >>
  `callee.fn_name = nm` by metis_tac[lookup_function_name] >>
  `~fn_is_context_entry observed'.cu_context callee` by
    simp[fn_is_context_entry_def] >>
  drule_all fmp_call_lowered_signature_root >> strip_tac >>
  drule_all fmp_call_walk_signature >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem call_lowered_labels[local]:
  fmp_stage_lowered infos ctx runner fn fn' ==>
  fn_labels fn' = fn_labels fn
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  irule fmp_lower_function_preserves_labels >>
  qexistsl [`ctx`,`sp`,`sp'`] >> simp[fmp_lower_function_def]
QED

Theorem call_match_witnesses[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  wf_function fn /\ fn.fn_fmp_signature = NONE /\
  active_inst fn inst s /\ active_inst fn' inst' t /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  fmp_stage_lowered infos_a observed.cu_context runner_a fn fn' /\
  o1_walk_view rpolicy 3 C' fn observed /\
  lookup_function nm C.ctx_functions = SOME callee /\
  callee.fn_fmp_signature = NONE /\ C.ctx_entry <> SOME nm /\
  (!infos ctx runner rl rp bb idx.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    lookup_block rl fn.fn_blocks = SOME bb /\ idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_opcode = INVOKE ==> rp <= idx) ==>
  ?callee' infos_c ctx_c runner_c extra.
    lookup_function nm C'.ctx_functions = SOME callee' /\
    fmp_stage_lowered infos_c ctx_c runner_c callee callee' /\
    ~fn_is_context_entry ctx_c callee /\ inst'.inst_opcode = INVOKE /\
    decode_invoke inst' = SOME (nm,ops ++ extra) /\
    ((extra = [] /\ fmp_stage_root infos_c ctx_c callee = NONE) \/
     (?runner. extra = [Var runner] /\ lookup_var runner t = SOME (n2w lo) /\
       IS_SOME (fmp_stage_root infos_c ctx_c callee)))
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn')` by
    (drule call_lowered_labels >> gvs[wf_function_def]) >>
  drule_all call_frame_witness >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
   lookup_block bb.bb_label fn'.fn_blocks = SOME bb'` by metis_tac[] >>
  fs[] >>
  `?seen sig. lookup_function nm ctx.ctx_functions = SOME seen /\
    seen.fn_fmp_signature = SOME sig /\
    inst'.inst_opcode = INVOKE /\
    decode_invoke inst' = SOME (nm,ops ++ if sig.fms_has_fmp_param then [Var runner] else []) /\
    (sig.fms_has_fmp_param ==> lookup_var runner t = SOME (n2w lo))` by
    (drule_all call_witness_decode >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `fmp_stage_lowered infos ctx runner fn fn'` kall_tac >>
  drule_all call_witness_decode >> strip_tac >>
  `sig.fms_has_fmp_param = sig'.fms_has_fmp_param` by
    (irule call_decode_decision >> metis_tac[]) >>
  `MEM nm (fn_invoke_targets fn)` by
    (gvs[venomFnScheduleRunnerTheory.fn_invoke_targets_def,
         fcgDefsTheory.fcg_scan_function_def, mem_get_invoke_targets,
         decode_invoke_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all call_actual_callee_root >> strip_tac >>
  rename1 `lookup_function nm C'.ctx_functions = SOME actual` >>
  qexistsl [`actual`,`infos_c`,`ctx_c`,`runner_c`,
    `if sig.fms_has_fmp_param then [Var runner] else []`] >>
  simp[] >> Cases_on `sig.fms_has_fmp_param` >> gvs[] >>
  metis_tac[optionTheory.IS_SOME_EQ_NOT_NONE]
QED

Theorem fmp_call_match_conditional:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm,ops) /\
  C.ctx_entry <> SOME nm /\
  lookup_function nm C.ctx_functions = SOME callee /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t /\
  (!infos ctx runner rl rp bb idx.
    fmp_stage_lowered infos ctx runner fn fn' /\
    fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    lookup_block rl fn.fn_blocks = SOME bb /\ idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_opcode = INVOKE ==> rp <= idx) ==>
  ?callee' infos_c ctx_c runner_c extra.
    lookup_function nm C'.ctx_functions = SOME callee' /\
    fmp_stage_lowered infos_c ctx_c runner_c callee callee' /\
    ~fn_is_context_entry ctx_c callee /\ ivk'.inst_opcode = INVOKE /\
    decode_invoke ivk' = SOME (nm,ops ++ extra) /\
    wf_function callee /\ first_block_no_phi callee /\
    ((extra = [] /\ fmp_stage_root infos_c ctx_c callee = NONE) \/
     (?runner. extra = [Var runner] /\ lookup_var runner t = SOME (n2w lo) /\
       IS_SOME (fmp_stage_root infos_c ctx_c callee)))
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn` by gvs[o1_fn_shape_def] >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  drule_all fmp_call_actual_witness >> strip_tac >> fs[] >>
  `wf_function callee /\ first_block_no_phi callee /\
    callee.fn_fmp_signature = NONE` by
    (`MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, o1_fn_shape_def,
         o1_inv_def, o1_static_inv_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  `fmp_frame_rel sm fmp0 raw0 (fmp_frame_base raw0 stk)
    (fmp_frame_lo fmp0 ts) lo T fn fn' PG G tn.t_var s t` by
    gvs[fmp_stage_rel_def] >>
  gvs[] >> drule_all call_match_witnesses >> strip_tac >>
  qexistsl [`callee'`,`infos_c`,`ctx_c`,`runner_c`,`extra`] >> simp[]
QED
