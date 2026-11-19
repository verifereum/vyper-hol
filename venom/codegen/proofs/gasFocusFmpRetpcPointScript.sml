Theory gasFocusFmpRetpcPoint
Ancestors
  gasFocusFmpStagePin fmpStageFmpStepsRetpcControl
  fmpStageFmpStepsRetpcPreservation fmpStageFmpStepsRetpcFrame
  fmpStageFmpStepsRetpcLayout fmpStageFmpStepsRetpcPrefix
  fmpStageRel fmpLowerDefs fmpWfDefs contextCodegenRel o1PassContract
  unitShapeDefs venomInst venomState venomExecSemantics list rich_list
  finite_map words

(* At the cut, use the selected lowering and the active frame's own ABI,
   rather than the whole-run FMP stage invariant. *)
Theorem focus_fmp_retpc_point:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  o1_fn_shape C fn /\ fn.fn_fmp_signature = NONE /\
  pre_fmp_ops fn /\ all_reachable fn /\
  active_inst fn inst s /\ inst.inst_opcode = RETPC_PARAM /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = OK s1 ==>
  ?n t1 fn' bb'.
    (n = 1 \/ n = 2) /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!fuel. fmp_target_run fuel C' fn.fn_name t n t1) /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo t1 ts /\
    (if n = 1 then TAKE n (DROP t.vs_inst_idx bb'.bb_instructions) = [inst]
     else ?id runner. TAKE n (DROP t.vs_inst_idx bb'.bb_instructions) =
       [mk_inst id FMP_PARAM [Lit (n2w s.vs_inst_idx)] [runner];
        set_param_index (SUC s.vs_inst_idx) inst])
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `wf_function fn /\ C.ctx_entry <> SOME fn.fn_name` by
    (fs[o1_fn_shape_def, entry_fn_no_params_def, EVERY_MEM] >>
     metis_tac[is_param_opcode_def]) >>
  `terminates (OK s1)` by simp[passSimulationDefsTheory.terminates_def] >>
  drule_all fmp_retpc_source_step >> strip_tac >>
  `retpc_var fn pc` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >> qexists `inst` >> simp[]) >>
  drule_all focus_fmp_selected_root_pin >> strip_tac >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_stage_rel_def]) >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm SUBST_ALL_TAC) `fn'' = fn'`
   >- metis_tac[optionTheory.SOME_11]) >>
  `canonical_param_prefix fn /\ ?info. FLOOKUP infos fn.fn_name = SOME info` by
    (qpat_x_assum `fmp_stage_lowered infos ctx runner fn fn'` mp_tac >>
     simp[fmp_stage_lowered_def] >> strip_tac >>
     gvs[fmp_lower_function_with_info_def, fmp_lower_input_def, AllCaseEqs()] >>
     goal_assum ACCEPT_TAC) >>
  drule_all fmp_retpc_user_arity >> strip_tac >>
  drule_all fmp_retpc_split_location >> strip_tac >>
  qpat_x_assum `pc' = SOME inst` SUBST_ALL_TAC >>
  `?entry rest. fn.fn_blocks = entry::rest` by
    (Cases_on `fn.fn_blocks` >> gvs[split_fmp_entry_def]) >>
  `s.vs_current_bb = entry.bb_label` by simp[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  `fmp_stage_root infos ctx fn <> NONE ==>
     fmp_stage_root infos ctx fn = SOME (s.vs_current_bb,SUC s.vs_inst_idx) /\
     ~fn_is_context_entry ctx fn /\ pc <> runner` by
    (Cases_on `fmp_stage_root infos ctx fn` >> simp[] >> PairCases_on `x` >>
     `~fn_is_context_entry ctx fn /\ pc <> runner` by metis_tac[MEM] >>
     drule_all fmp_retpc_root_location >> gvs[]) >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (`fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        entry.bb_label entry.bb_instructions s.vs_inst_idx =
      s.vs_inst_idx + (case fmp_stage_root infos ctx fn of NONE => 0
        | SOME (rl,rp) => if entry.bb_label = rl /\ rp <= s.vs_inst_idx then 1 else 0)` by
       (irule fmp_retpc_prefix_tidx >> simp[] >> metis_tac[]) >>
     Cases_on `fmp_stage_root infos ctx fn = NONE` >> gvs[]) >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
     s.vs_current_bb entry.bb_instructions (SUC s.vs_inst_idx) =
   t.vs_inst_idx + (if fmp_stage_root infos ctx fn = NONE then 1 else 2)` by
    (`fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        entry.bb_label entry.bb_instructions (SUC (LENGTH users)) =
      LENGTH users + (if fmp_stage_root infos ctx fn = NONE then 1 else 2)` by
       (irule fmp_retpc_successor_tidx >> simp[] >> metis_tac[]) >>
     gvs[]) >>
  `fmp_stage_root infos ctx fn <> NONE ==>
     LENGTH users < LENGTH t.vs_params /\
     EL (LENGTH users) t.vs_params = n2w lo` by
    (strip_tac >> gvs[]) >>
  qpat_assum `fmp_stage_lowered infos ctx runner fn fn'`
    (mp_then (Pat `fmp_stage_lowered _ _ _ _ _`) mp_tac fmp_retpc_target_prefix) >>
  disch_then (qspecl_then [`users`, `tail`, `s.vs_current_bb`, `inst`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `fn'.fn_blocks = bb'::bbs'` >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb'` by
    fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm] >>
  mp_tac (Q.INST [`suffix` |-> `tail`] fmp_retpc_target_run) >>
  (impl_tac >- (Cases_on `fmp_stage_root infos ctx fn = NONE` >> gvs[])) >> strip_tac >>
  qexistsl_tac [`n`, `t1`, `fn'`, `bb'`] >>
  conj_tac >- decide_tac >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule fmp_retpc_preserves >> simp[] >>
      qexistsl_tac [`ctx`, `infos`, `runner`, `t`] >>
      Cases_on `fmp_stage_root infos ctx fn = NONE` >> gvs[] >>
      metis_tac[]) >>
  Cases_on `fmp_stage_root infos ctx fn = NONE` >> gvs[Excl "TAKE1_DROP"]
  >- (qpat_assum `bb'.bb_instructions = _` SUBST1_TAC >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  rename1 `bb'.bb_instructions = _ ++ [mk_inst id FMP_PARAM _ [runner]; _] ++ tail'` >>
  qexistsl_tac [`id`, `runner`] >>
  qpat_assum `bb'.bb_instructions = _` SUBST1_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED
