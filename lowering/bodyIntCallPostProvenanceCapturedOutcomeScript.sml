(* Captured array provenance on the actual base/snapshot/index execution. *)
Theory bodyIntCallPostProvenanceCapturedOutcome
Ancestors
  bodyIntCallPostProvenanceCapturedEntry bodyIntCallPostProvenanceCapturedFrame
  bodyIntCallPostProvenanceCapturedSuffix bodyIntCallPostProvenanceCapture
  bodyIntCallPostProvenanceCallbacks bodyIntCallFamAggSubscriptArraySetup
  bodyIntCallPostProvenanceCaptureAlignment
  exprSimSubscriptArrayCompose exprSimSubscriptMap exprSimHyps exprSimSource
  exprSimAggregateBodyCountedChildren exprLoweringProps gasOutcome gasSummary
  gasSummaryCompose loweringPosts compileEnv context vyperInterpreter
  exprLowering exprSimSubscriptArraySource exprSimSliceOrdinaryContinue
  exprSimExtract32Counted exprSimSliceCompose vyperValue
  vyperTypeExprResult vyperTypeExprSoundness exprSimHypsDefs

Theorem captured_materialize_initial_gas[local]:
  materialize_owned_post ctx func ce cx e (es with gas_obs := gs)
    sa sm sb s0 ee v dst tv t <=>
  materialize_owned_post ctx func ce cx e es sa sm sb s0 ee v dst tv t
Proof
  simp[exprSimAbiEncodeArgsMaterializePathTheory.materialize_owned_post_def,
    wb_frame_def, locals_kept_def, popped_kept_def, pure_frame_def]
QED

Theorem captured_array_code_cuts[local]:
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_snapshot_vv ce T bvv sm = (saved,sn) /\
  lower_value compile_expr ce ty idx sn = (iop,sc) /\
  compile_array_subscript bop iop dyn len scale esz sgn loader sc = (dst,sb) /\
  (!op st. ci_mono st (SND (loader op st))) /\
  fn_has_code sa sb func ==>
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sc /\ ci_mono sc sb /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn sc func /\ fn_has_code sc sb func
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (qpat_assum `compile_expr ce ty obj sa = _` mp_tac >>
     disch_then (mp_tac o MATCH_MP (cj 1 compile_expr_grows)) >> simp[ci_mono_def]) >>
  `ci_mono sm sn` by
    (qspecl_then [`ce`,`T`,`bvv`,`sm`] mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono sn sc` by (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono sc sb` by
    (drule array_subscript_grows >> simp[ci_mono_compile_ptr_load, GSYM ci_mono_def]) >>
  `ci_mono sn sb` by metis_tac[ci_mono_trans] >>
  `ci_mono sm sb` by metis_tac[ci_mono_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >>
  `fn_has_code sn sc func /\ fn_has_code sc sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >> simp[]
QED

Theorem intcall_captured_subscript_outcome:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  ~expr_has_effect (Subscript ann obj idx) /\
  expr_type obj = ArrayT et bd /\ place_type ce obj = ValPT (ArrayT et bd) /\
  copies_subscript_base ce obj idx /\
  expr_vv_case F ctx func ce cx obj /\ expr_sim_case F ctx func ce cx idx /\
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\res ee t. ?raw. res = INL raw /\
      vv_post ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee raw vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (expr_type (Subscript ann obj idx)) sa sb ee raw vv t)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx` by gvs[] >>
  drule_all expr_body_pre_array_subscript_base >> strip_tac >>
  drule_all intcall_array_subscript_annotation >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
    exprCallBoundsTheory.expr_child_callback_def, vyperASTTheory.expr_size_def] >>
  drule_all compile_subscript_capture_array >>
  disch_then (fn th => simp[th, exprCallBoundsTheory.expr_child_callback_def]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce ty obj sa = (bvv,sm)` >>
  rename1 `compile_snapshot_vv ce T bvv sm = (saved,sn)` >>
  rename1 `compile_expr ce ty idx sn = (ivv,si)` >>
  rename1 `unwrap_value ce ivv si = (iop,sc)` >>
  `lower_value compile_expr ce ty idx sn = (iop,sc)` by
    simp[lower_value_def, comp_bind_def] >>
  rename1 `compile_array_subscript _ _ _ _ _ _ _ _ sc = (dst,sb)` >>
  `!op st. ci_mono st (SND
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca
      (case vv_location saved of NONE => LocMemory | SOME l => l) op st))` by
    simp[ci_mono_compile_ptr_load] >>
  drule_all captured_array_code_cuts >> strip_tac >>
  `expr_vv_sim ctx func ce cx ty obj es` by
    (gvs[exprSimHypsDefsTheory.expr_vv_case_def] >> metis_tac[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[exprSimDefsTheory.expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `subscript_reads_base cx obj idx` by
    (metis_tac[body_inv_copies_subscript_base_source]) >>
  drule eval_expr_subscript_capture_bind >> disch_then (qspec_then `ann` SUBST1_TAC) >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  reverse conj_tac >- metis_tac[] >>
  suspend "after_base"
QED

Resume intcall_captured_subscript_outcome[after_base]:
  rpt gen_tac >> strip_tac >>
  drule exprSimAggregateSourceTheory.vv_post_materialises >> strip_tac >>
  `~t.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre ce cx env obj
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `?tv u. evaluate_type (get_tenv cx) (expr_type obj) = SOME tv /\
    value_has_type tv v' /\ val_wf tv v' /\
    gas_marked_path F ctx func t 0 (OK u) /\
    materialize_owned_post ctx func ce cx obj es sa sm sn s0
      (mid with gas_obs := []) v' (vv_operand saved) tv u /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (drule_at (Pat `eval_expr _ _ _ = _`) intcall_captured_snapshot_entry >>
     simp[exprSimPropsTheory.vv_post_initial_gas, captured_materialize_initial_gas] >>
     disch_then drule_all >> simp[]) >>
  `gas_marked_exec F (ctx,func) (read_result cx v)
    (mid with gas_obs := [],t) [] (INL v') mid (OK u)` by
    (simp[gas_marked_exec_def] >>
     metis_tac[bodyIntCallProducerInterfaceTheory.read_result_success_gas_obs_iff]) >>
  irule extract32_outcome_read_prefix >> goal_assum (drule_at Any) >> simp[] >>
  suspend "index_setup"
QED

Resume intcall_captured_subscript_outcome[index_setup]:
  `expr_body_pre ce cx env idx (mid with gas_obs := [])` by
    (drule_at (Pat `eval_expr _ _ _ = _`)
       expr_body_pre_array_subscript_index_after_base >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  `local_ptrs_reserved ce sn` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) u` by
    gvs[exprSimAbiEncodeArgsMaterializePathTheory.materialize_owned_post_def] >>
  `expr_sim ctx func ce cx ty idx (mid with gas_obs := [])` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_sim_case_def] >>
     disch_then irule >> qexists_tac `env` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_sim_def]) >>
  disch_then (qspecl_then [`sn`,`sc`,`iop`,`u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
      expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) exprSimDefsTheory.expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  irule slice_gas_outcome_bind_value >>
  qexists_tac `\iv ee t. expr_post ctx func ce cx idx
    (mid with gas_obs := []) sn sc u ee iv iop t /\
    t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts` >>
  reverse conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ (bind _ _) _ _ _` mp_tac >>
      simp[]) >>
  suspend "after_index"
QED

Resume intcall_captured_subscript_outcome[after_index]:
  rpt gen_tac >> strip_tac >>
  fs[] >>
  `vv_type bvv = ArrayT ann bd` by
    metis_tac[bodyIntCallCompilerTagsTheory.intcall_compile_expr_tag, pairTheory.FST] >>
  Cases_on `compile_materialize_vv ce (ArrayT ann bd) bvv sm` >>
  gvs[compile_snapshot_vv_def, is_word_type_def, comp_bind_def,
      comp_return_def, vv_location_def, mk_ptr_def, vv_operand_def] >>
  rename1 `compile_materialize_vv ce (ArrayT ann bd) bvv sm = (q,sn)` >>
  `!x. q = Var x ==> not_fresh_at sn x` by
    (drule exprOperandVarTheory.compiler_materialize_vv_var >> simp[]) >>
  `!l. q <> Label l` by metis_tac[abiEncodeArgsSimTheory.abi_args_materialize_not_label] >>
  drule_all intcall_captured_index_frame >> strip_tac >>
  `?etv. tv = ArrayTV etv bd /\ evaluate_type (get_tenv cx) ann = SOME etv` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  gvs[] >>
  `?av. v' = ArrayV av` by
    (Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `bind (eval_expr cx idx) (read_result cx)
    (mid with gas_obs := gas_explicit marks' u.vs_gas_readings) =
      (INL v'',mid' with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `?itv. evaluate_type (get_tenv cx) (expr_type idx) = SOME itv /\
      value_has_type itv v''` by
    (`expr_body_pre ce cx env idx
        (mid with gas_obs := gas_explicit marks' u.vs_gas_readings)` by simp[] >>
     `expr_result_typed env idx (Value v'')` by
       metis_tac[exprSimSourceTheory.expr_body_pre_eval] >>
     gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def, expr_body_pre_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >> strip_tac >>
  gvs[] >> suspend "suffix_setup"
QED

Resume intcall_captured_subscript_outcome[suffix_setup]:
  `wb_frame ce es (mid' with gas_obs := []) sa s0 t'` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`mid with gas_obs := []`, `sn`, `u`] >>
     gvs[exprSimAbiEncodeArgsMaterializePathTheory.materialize_owned_post_def,
       expr_post_def, wb_frame_def, ci_mono_def, locals_kept_def] >>
     rpt conj_tac >> metis_tac[]) >>
  `pure_frame ce func es sa s0 t'` by
    (irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
     qexistsl_tac [`mid with gas_obs := []`, `sn`, `u`] >>
     gvs[exprSimAbiEncodeArgsMaterializePathTheory.materialize_owned_post_def,
       expr_post_def, wb_frame_def, ci_mono_def, locals_kept_def] >>
     rpt conj_tac >> metis_tac[]) >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  simp[GSYM mk_ptr_def, gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  simp[vyperASTTheory.expr_type_def] >>
  irule intcall_captured_array_suffix_summary >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt conj_tac
  >- (Cases_on `bd` >> Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def])
  >- metis_tac[slice_marked_read_ok_not_halted]
  >- simp[vyperASTTheory.expr_type_def]
  >- (qexistsl_tac [`sm.cs_next_id`, `w2n w`, `q`, `iop`, `iw`,
        `is_signed_type (expr_type idx)`, `sc`,
        `type_memory_size (ArrayTV etv bd)`, `w`] >> simp[] >>
      rpt conj_tac
      >- (gvs[exprSimAbiEncodeArgsMaterializePathTheory.materialize_owned_post_def,
              ci_mono_def] >> decide_tac)
      >- gvs[ci_mono_def]
      >- metis_tac[targetSubscriptMemoryTheory.target_memory_array_length_bound]
      >- metis_tac[arithmeticTheory.ADD_COMM]
      >- (gvs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
              venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
          `t'.vs_alloca_next < dimword (:256)` by
            (gvs[exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
          qpat_x_assum `!aid base sz. FLOOKUP t'.vs_allocas aid = _ ==> _`
            (qspec_then `sm.cs_next_id` mp_tac) >> simp[] >> decide_tac)
      >- gvs[loweringStateRelDefsTheory.not_fresh_at_def]
      >- gvs[ci_mono_def]
      >- (`elem_size_in_location ce LocMemory ann = type_memory_size etv` by
            metis_tac[elem_size_in_location_def, is_slot_addressed_def,
              expr_body_pre_def, expr_sim_inv_memory_size] >>
          gvs[compileEnvTheory.word_scale_def])
      >- metis_tac[local_ptrs_reserved_next_var])
  >- gvs[expr_post_def]
QED

Finalise intcall_captured_subscript_outcome
