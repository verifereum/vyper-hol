Theory exprSimStructLitBodyCounted
Ancestors
  exprSimAggregateBodyCountedLoops exprSimAggregatesAllocCounted
  exprSimAggregateLayout exprSimAggregateSource exprSimAggregateChildren
  exprSimHyps exprSimHypsDefs exprSimDefs loweringPosts
  aggregateCountedOutcome aggregateCountedOutcomeFacts stmtReasonVvMemory
  exprLoweringProps exprLowering compileEnv valueEncoding valueEncodingProps
  gasOutcome gasSummary gasContext fragGasMode fragGasPath fragGasSeq fragExec
  vyperInterpreter vyperState vyperAST

Theorem compile_struct_lit_body_case:
  !ctx func ce cx ann nsid fields.
    exprs_case F ctx func ce cx (MAP SND fields) /\
    acyclic_struct_metadata ce.ce_struct_fields ==>
    expr_sim_case F ctx func ce cx (StructLit ann nsid fields) /\
    expr_vv_case F ctx func ce cx (StructLit ann nsid fields)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case F ctx func ce cx (StructLit ann nsid fields)` by
    suspend "vv" >>
  conj_tac >- (irule expr_sim_case_of_vv >> simp[post_value_type_def]) >>
  first_assum ACCEPT_TAC
QED

Resume compile_struct_lit_body_case[vv]:
  simp[expr_vv_case_def, expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule compile_struct_literal_inv >> strip_tac >>
  drule_all struct_literal_evaluated_layout >> strip_tac >>
  drule_all struct_literal_lookup_types >> strip_tac >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    (qspec_then `compile_expr` mp_tac ci_mono_compile_struct_lit_cfn >>
     simp[cj 1 compile_expr_ci_mono] >>
     disch_then (qspecl_then [`ce`, `StructT nsid`, `fields`, `ba.buf_operand`, `0`, `sm`] mp_tac) >>
     simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_size_list tvs < dimword (:256)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
          type_memory_bytes_def, wordsTheory.dimword_def] >> decide_tac) >>
  qpat_x_assum `type_memory_size_list tvs < _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all buffer_alloc_counted >> strip_tac >>
  `!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
      expr_body_pre ce cx env e st` by metis_tac[expr_body_pre_struct_field] >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b (type_memory_size_list tvs)` by
    suspend "immutable" >>
  qpat_x_assum `compile_struct_lit _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`) aggregate_struct_fields_body_sim >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
  disch_then (qspecl_then [`env`, `es`, `func`, `ctx`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  suspend "outcome"
QED

Resume compile_struct_lit_body_case[immutable]:
  qpat_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  fs[immutable_alloca_sep_def] >> rpt strip_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` (mp_tac o UNDISCH) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!ii bb nn. MEM ii _ /\ _ ==> regions_disjoint _ _ _ _` irule >>
  goal_assum (drule_at Any) >>
  simp[venomInstTheory.mk_inst_def] >> metis_tac[]
QED

Resume compile_struct_lit_body_case[outcome]:
  `eval_expr cx (StructLit ann nsid fields) =
    bind (eval_exprs cx (MAP SND fields))
      (\vs. return (Value (StructV (ZIP (MAP FST fields,vs)))))` by
    (simp[FUN_EQ_THM] >> gen_tac >>
     Cases_on `eval_exprs cx (MAP SND fields) x'` >>
     drule aggregate_eval_struct >>
     Cases_on `q` >> simp[bind_def, return_def]) >>
  asm_rewrite_tac[] >>
  irule gas_outcome_zero_prefix_any >>
  goal_assum (drule_at Any) >>
  dxrule counted_outcome_normal_facts >>
  disch_then (mp_tac o SIMP_RULE (std_ss ++ boolSimps.CONJ_ss) [GSYM LEFT_EXISTS_AND_THM, GSYM CONJ_ASSOC]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ _ Q _` >>
  `(\res ee r. ?vs. res = INL vs /\ Q (INL vs) ee r) = Q` by
    simp[FUN_EQ_THM, Abbr `Q`] >>
  qpat_assum `(_ : (value list + exception) -> evaluation_state -> venom_state -> bool) = Q`
    (fn eqth => qspecl_then
      [`\vs ee r. Q (INL vs) ee r`,
       `\res ee r. expr_exit res r`,
       `\vs. Value (StructV (ZIP (MAP FST fields,vs)))`]
      (drule o REWRITE_RULE [GSYM AND_IMP_INTRO, eqth] o BETA_RULE)
      (Q.GENL [`P`, `R`, `f`] counted_outcome_map_values)) >>
  impl_tac >- simp[Abbr `Q`] >>
  disch_then (qspec_then `fields` assume_tac) >>
  qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` kall_tac >>
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`) counted_outcome_conseq >>
  disch_then irule >>
  simp[Abbr `Q`] >> rpt gen_tac >> strip_tac >>
  qexists_tac `Value (StructV (ZIP (MAP FST fields,vs)))` >>
  simp[] >>
  drule aggregate_eval_struct >>
  disch_then (qspecl_then [`nsid`, `ann`] assume_tac) >>
  `expr_body_pre ce cx env (StructLit ann nsid fields) (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >>
  simp[] >> strip_tac >>
  simp[vv_post_def, post_value_type_def] >>
  simp[contextTheory.base_ptr_def, expr_type_def] >>
  conj_tac >- suspend "holds" >>
  conj_tac >- suspend "at" >>
  conj_tac >-
    (rpt strip_tac >> irule_at Any EQ_TRANS >>
     goal_assum (drule_at Any) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  conj_tac >- suspend "frame" >>
  fs[locals_kept_def] >> metis_tac[]
QED

Resume compile_struct_lit_body_case[holds]:
  `ann = StructT nsid` by
    (`well_typed_expr env (StructLit ann nsid fields)` by fs[expr_body_pre_def] >>
     drule structFieldsPropsTheory.struct_literal_decl_types >> simp[]) >>
  simp[vv_holds_def, read_result_def, return_def, venomStateTheory.eval_operand_def] >>
  `lookup_var x t' = SOME (n2w b)` by metis_tac[] >>
  simp[] >> rpt strip_tac >>
  gvs[] >>
  fs[val_in_memory_def, compileEnvTheory.is_word_type_def]
QED

Resume compile_struct_lit_body_case[at]:
  `ann = StructT nsid` by
    (`well_typed_expr env (StructLit ann nsid fields)` by fs[expr_body_pre_def] >>
     drule structFieldsPropsTheory.struct_literal_decl_types >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `lookup_var x t' = SOME (n2w b)` by metis_tac[] >>
  simp[vv_at_def, read_result_def, return_def, venomStateTheory.eval_operand_def] >>
  gvs[expr_type_def] >>
  conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  disj1_tac >> qexistsl_tac [`inst.inst_id`, `b`, `type_memory_size_list tvs`] >>
  simp[val_footprint_def, type_memory_size_def] >>
  conj_tac >- fs[ci_mono_def] >>
  conj_tac >-
    (`LENGTH (MAP FST fields) = LENGTH tvs` by
       (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[valueEncodingTypingTheory.type_memory_size_fields_zip]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >> simp[]) >>
  rpt strip_tac >>
  `local_region ce es.scopes t n lb lsz` by
    (`local_ptrs_rel func ce es.scopes t` by fs[stmt_state_rel_def, state_rel_def] >>
     drule exprSimPropsTheory.local_region_frame >>
     disch_then (qspec_then `sm` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `local_region ce es.scopes s0 n lb lsz` by metis_tac[] >>
  qpat_x_assum `!name p n. local_region _ _ s0 _ _ _ ==> _`
    (drule_then mp_tac) >>
  simp[regions_disjoint_def]
QED

Resume compile_struct_lit_body_case[frame]:
  rpt strip_tac >>
  qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` irule >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >-
    (qexists_tac `aid` >> conj_tac >- fs[ci_mono_def] >> metis_tac[]) >>
  qpat_x_assum `!aid p n. aid < sa.cs_next_id /\ _ ==> _` drule_all >>
  simp[regions_disjoint_def]
QED

Finalise compile_struct_lit_body_case
