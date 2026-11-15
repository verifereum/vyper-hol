(*
 * INVOKE's call step, the matching half: the target's INVOKE at the
 * control map's index calls the lowered callee, with the runner appended
 * exactly when the callee takes an FMP parameter.
 *
 * TOP-LEVEL:
 *   fmp_call_match - the target INVOKE matching a source INVOKE
 *)
Theory fmpStageFmpStepsCallMatch
Ancestors
  fmpStageFmpStepsCallAbi
  fmpStageFmpStepsInvokePosition fmpStageRunnerFacts dftGasToListReachBoundary
  venomInstIdsProps unitShapeDefs
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

Theorem call_frame_witness[local]:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  wf_function fn /\ ALL_DISTINCT (fn_labels fn') /\
  active_inst fn inst s /\ active_inst fn' inst' t /\
  inst.inst_opcode = INVOKE ==>
  ?infos ctx runner.
    fmp_stage_lowered infos ctx runner fn fn' /\
    inst'.inst_id = inst.inst_id /\
    (IS_SOME (fmp_stage_root infos ctx fn) ==>
      lookup_var runner t = SOME (n2w lo))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  drule_all fmp_frame_invoke_position >> strip_tac >>
  `j = inst'` by
    (imp_res_tac dftGasToListReachBoundaryTheory.active_inst_lookup_distinct >>
     gvs[]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     s.vs_inst_idx < LENGTH bb.bb_instructions /\
     EL s.vs_inst_idx bb.bb_instructions = inst` by
    (gvs[active_inst_def] >> metis_tac[venomExecProofsTheory.wf_lookup_block]) >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
  qexistsl [`infos`,`ctx`,`runner`] >> gvs[] >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  `~(t.vs_current_bb = x0 /\ s.vs_inst_idx < x1)` by
    (`~MEM (EL s.vs_inst_idx bb.bb_instructions).inst_opcode
        [PARAM; RETPC_PARAM; FMP_PARAM]` by gvs[] >>
     metis_tac[fmp_stage_past_root, NOT_LESS]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[]
QED

Theorem call_lowered_id[local]:
  inst.inst_opcode = INVOKE /\
  fmp_lower_inst infos ctx runner sp inst = SOME ([j],sp') ==>
  j.inst_id = inst.inst_id
Proof
  strip_tac >> drule_all fmp_lower_invoke_inst >> strip_tac >> gvs[]
QED

(* Why: target ids are distinct, so the target INVOKE with the source's id
   is the one any witness of the lowering puts there. *)
Theorem call_witness_target[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\ wf_function fn /\
  fn_inst_ids_distinct fn' /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\
  MEM inst' (fn_insts fn') /\ inst'.inst_id = inst.inst_id ==>
  (fmp_stage_root infos ctx fn = NONE /\ inst' = inst) \/
  ?sp sp'. fmp_lower_inst infos ctx runner sp inst = SOME ([inst'],sp')
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     s.vs_inst_idx < LENGTH bb.bb_instructions /\
     EL s.vs_inst_idx bb.bb_instructions = inst` by
    (gvs[active_inst_def] >> metis_tac[venomExecProofsTheory.wf_lookup_block]) >>
  `!lbl b p. lookup_block lbl fn'.fn_blocks = SOME b /\
     p < LENGTH b.bb_instructions /\
     (EL p b.bb_instructions).inst_id = inst.inst_id ==>
     EL p b.bb_instructions = inst'` by
    (rpt strip_tac >> irule fn_inst_ids_distinct_inj >>
     conj_tac >- simp[] >> qexists `fn'` >> simp[] >>
     simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[venomExecProofsTheory.lookup_block_MEM, EL_MEM]) >>
  qpat_x_assum `EL _ _ = inst` (SUBST_ALL_TAC o SYM) >>
  drule_all fmp_stage_invoke_at >> strip_tac
  >- (disj1_tac >> simp[] >> metis_tac[]) >>
  disj2_tac >> imp_res_tac call_lowered_id >> metis_tac[]
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
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  ((fmp_stage_root infos ctx fn = NONE /\ inst' = inst) \/
   ?sp sp'. fmp_lower_inst infos ctx runner sp inst = SOME ([inst'],sp')) ==>
  ?callee sig.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig /\
    FLOOKUP infos nm = SOME (fmp_info_of_signature sig) /\
    inst'.inst_opcode = INVOKE /\
    decode_invoke inst' = SOME (nm,ops ++ if sig.fms_has_fmp_param then [Var runner] else []) /\
    (sig.fms_has_fmp_param ==> IS_SOME (fmp_stage_root infos ctx fn))
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all call_lowered_resolve >> strip_tac >>
  `sig.fms_has_fmp_param ==> IS_SOME (fmp_stage_root infos ctx fn)` by
    (strip_tac >>
     `analyze_fmp_context ctx = SOME infos` by gvs[fmp_stage_lowered_def] >>
     `?info. FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp` by
       (irule call_needs_caller >> simp[] >>
        reverse conj_tac >- metis_tac[] >>
        qexistsl [`fmp_info_of_signature sig`,`inst`,`nm`,`ops`] >>
        simp[fmp_info_of_signature_def]) >>
     drule_all fmp_stage_root_exists >> strip_tac >> simp[]) >>
  qexistsl [`callee`,`sig`] >> simp[] >>
  qpat_x_assum `_ \/ _` strip_assume_tac >- gvs[] >>
  drule_at (Pos last) fmp_lower_invoke_inst >> simp[] >> strip_tac >>
  drule fmp_resolve_invoke_some >> strip_tac >>
  imp_res_tac lookup_function_name >>
  gvs[decode_invoke_def, fmp_info_of_signature_def]
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
  rename1 `o1_walk_view rpolicy 3 C' callee obs_c` >>
  `callee.fn_name = nm` by metis_tac[lookup_function_name] >>
  `~fn_is_context_entry obs_c.cu_context callee` by
    simp[fn_is_context_entry_def] >>
  drule_all fmp_call_lowered_signature_root >> strip_tac >>
  drule_all fmp_call_walk_signature >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem call_match_witnesses[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  wf_function fn /\ wf_function fn' /\ fn.fn_fmp_signature = NONE /\
  active_inst fn inst s /\ active_inst fn' inst' t /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  fmp_stage_lowered infos_a observed.cu_context runner_a fn fn' /\
  o1_walk_view rpolicy 3 C' fn observed /\
  lookup_function nm C.ctx_functions = SOME callee /\
  callee.fn_fmp_signature = NONE /\ C.ctx_entry <> SOME nm ==>
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
  `ALL_DISTINCT (fn_labels fn') /\ fn_inst_ids_distinct fn'` by
    gvs[wf_function_def] >>
  drule_all call_frame_witness >> strip_tac >>
  `MEM inst' (fn_insts fn')` by
    (gvs[active_inst_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  `?seen sig. lookup_function nm ctx.ctx_functions = SOME seen /\
    seen.fn_fmp_signature = SOME sig /\
    inst'.inst_opcode = INVOKE /\
    decode_invoke inst' = SOME (nm,ops ++ if sig.fms_has_fmp_param then [Var runner] else []) /\
    (sig.fms_has_fmp_param ==> lookup_var runner t = SOME (n2w lo))` by
    (`(fmp_stage_root infos ctx fn = NONE /\ inst' = inst) \/
      ?sp sp'. fmp_lower_inst infos ctx runner sp inst = SOME ([inst'],sp')` by
       metis_tac[call_witness_target] >>
     qpat_assum `fmp_stage_lowered infos ctx runner _ _`
       (mp_then (Pos hd) (qspecl_then [`ops`,`nm`,`inst'`,`inst`] mp_tac)
          call_witness_decode) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> metis_tac[]) >>
  `(fmp_stage_root infos_a observed.cu_context fn = NONE /\ inst' = inst) \/
   ?sp sp'. fmp_lower_inst infos_a observed.cu_context runner_a sp inst =
     SOME ([inst'],sp')` by
    metis_tac[call_witness_target] >>
  qpat_assum `fmp_stage_lowered infos_a _ _ _ _`
    (mp_then (Pos hd) (qspecl_then [`ops`,`nm`,`inst'`,`inst`] mp_tac)
       call_witness_decode) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  rename1 `FLOOKUP infos_a nm = SOME (fmp_info_of_signature sig_a)` >>
  `sig.fms_has_fmp_param = sig_a.fms_has_fmp_param` by
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

Theorem fmp_call_match:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm,ops) /\
  C.ctx_entry <> SOME nm /\
  lookup_function nm C.ctx_functions = SOME callee /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t ==>
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
  `wf_function fn'` by metis_tac[fmp_call_target_wf] >>
  gvs[] >> drule_all call_match_witnesses >> strip_tac >>
  qexistsl [`callee'`,`infos_c`,`ctx_c`,`runner_c`,`extra`] >> simp[]
QED
