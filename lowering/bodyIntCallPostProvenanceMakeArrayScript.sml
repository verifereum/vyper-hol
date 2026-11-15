(* MakeArray allocation certificates on the element fold's own witness. *)
Theory bodyIntCallPostProvenanceMakeArray
Ancestors
  bodyIntCallProducerInterface exprSimAggregateBodyLoops
  exprSimAggregatesAllocCounted exprSimAggregateLayout exprSimAggregateSource
  exprSimAggregateChildren exprSimHyps exprSimHypsDefs exprSimDefs loweringPosts
  aggregateCountedOutcome aggregateCountedOutcomeFacts stmtReasonVvMemory
  exprLoweringProps exprLowering compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs valueEncodingProps
  gasOutcome gasSummary gasContext fragGasMode fragGasPath fragGasSeq fragExec
  vyperInterpreter vyperState vyperAST

Theorem intcall_tuple_literal_outcome:
  exprs_case F ctx func ce cx args /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  expr_body_pre ce cx env (Builtin ann (MakeArray NONE bnd) args) es /\
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) args) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx (Builtin ann (MakeArray NONE bnd) args)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Builtin ann (MakeArray NONE bnd) args)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (Builtin ann (MakeArray NONE bnd) args) es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (expr_type (Builtin ann (MakeArray NONE bnd) args))
        sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule compile_tuple_literal_inv >> strip_tac >>
  drule make_tuple_evaluated_layout >> strip_tac >>
  gvs[tuple_literal_types_def] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    (qspec_then `compile_expr` mp_tac ci_mono_compile_make_tuple_cfn >>
     simp[cj 1 compile_expr_ci_mono] >>
     disch_then (qspecl_then [`ce`, `args`, `tys`, `ba.buf_operand`, `0`, `sm`] mp_tac) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes ce (TupleT tys) < 2 ** 64` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def]) >>
  `type_memory_size_list tvs < dimword (:256)` by
    (qpat_x_assum `type_memory_bytes ce (TupleT tys) < _` mp_tac >>
     pure_rewrite_tac[type_memory_bytes_def] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     asm_rewrite_tac[] >> simp[wordsTheory.dimword_def]) >>
  qpat_x_assum `type_memory_size_list tvs < _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all buffer_alloc_counted >> strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
      expr_body_pre ce cx env e st` by
    (rpt strip_tac >> irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >>
     qexistsl_tac [`TupleT tys`, `args`, `MakeArray NONE bnd`, `es`] >> simp[]) >>
  suspend "fold"
QED

Resume intcall_tuple_literal_outcome[fold]:
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b (type_memory_size_list tvs)` by
    suspend "immutable" >>
  qpat_x_assum `compile_make_tuple _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`) aggregate_body_make_tuple_fits_sim >>
  disch_then (drule_at (Pat `LIST_REL _ _ _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
  disch_then (qspecl_then [`env`, `es`, `func`, `ctx`] mp_tac) >>
  impl_tac >- (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> metis_tac[]) >> strip_tac >>
  suspend "outcome"
QED

Resume intcall_tuple_literal_outcome[immutable]:
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

Resume intcall_tuple_literal_outcome[outcome]:
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `eval_expr cx (Builtin (TupleT tys) (MakeArray NONE bnd) args) =
    bind (eval_exprs cx args) (\vs. return (Value (ArrayV (TupleV vs))))` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `eval_exprs cx args x'` >>
     drule_all aggregate_eval_make_tuple >>
     Cases_on `q` >> simp[bind_def, return_def]) >>
  asm_rewrite_tac[] >>
  irule gas_outcome_zero_prefix_any >> goal_assum (drule_at Any) >>
  dxrule counted_outcome_normal_facts >>
  disch_then (mp_tac o SIMP_RULE (std_ss ++ boolSimps.CONJ_ss) [GSYM LEFT_EXISTS_AND_THM, GSYM CONJ_ASSOC]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ _ Q _` >>
  `(\res ee r. ?vs. res = INL vs /\ Q (INL vs) ee r) = Q` by
    simp[FUN_EQ_THM, Abbr `Q`] >>
  qpat_assum `(_ : (value list + exception) -> evaluation_state -> venom_state -> bool) = Q`
    (fn eqth => qspecl_then
      [`\vs ee r. Q (INL vs) ee r`, `\res ee r. expr_exit res r`,
       `\vs. Value (ArrayV (TupleV vs))`]
      (drule o REWRITE_RULE [GSYM AND_IMP_INTRO, eqth] o BETA_RULE)
      (Q.GENL [`P`, `R`, `f`] counted_outcome_map_values)) >>
  impl_tac >- simp[Abbr `Q`] >>
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` kall_tac >>
  suspend "post"
QED

Resume intcall_tuple_literal_outcome[post]:
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`) counted_outcome_conseq >>
  disch_then irule >> simp[Abbr `Q`] >> rpt gen_tac >> strip_tac >>
  qexists_tac `Value (ArrayV (TupleV vs))` >> simp[] >>
  drule_all aggregate_eval_make_tuple >>
  disch_then (qspec_then `TupleT tys` assume_tac) >>
  `expr_body_pre ce cx env (Builtin (TupleT tys) (MakeArray NONE bnd) args) (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[] >> strip_tac >>
  reverse conj_tac >- suspend "provenance" >>
  simp[vv_post_def, post_value_type_def] >>
  simp[contextTheory.mk_ptr_def, contextTheory.base_ptr_def, expr_type_def] >>
  conj_tac >- suspend "holds" >>
  conj_tac >- suspend "at" >>
  conj_tac >-
    (rpt strip_tac >> irule_at Any EQ_TRANS >> goal_assum (drule_at Any) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  conj_tac >- suspend "frame" >>
  reverse conj_tac >- suspend "pure_frame" >>
  irule exprBopSimPropsTheory.locals_kept_trans >>
  qexistsl_tac [`es`, `sa`, `t`] >> simp[] >>
  irule exprSimPropsTheory.locals_kept_mem >> simp[]
QED

Resume intcall_tuple_literal_outcome[holds]:
  simp[vv_holds_def, read_result_def, return_def, venomStateTheory.eval_operand_def] >>
  `lookup_var x t' = SOME (n2w b)` by metis_tac[] >>
  simp[] >> rpt strip_tac >> gvs[] >>
  fs[val_in_memory_def, compileEnvTheory.is_word_type_def]
QED

Resume intcall_tuple_literal_outcome[at]:
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
  suspend "separation"
QED

Resume intcall_tuple_literal_outcome[separation]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >> simp[]) >>
  rpt strip_tac >>
  `local_region ce es.scopes t n lb lsz` by
    (`local_ptrs_rel func ce es.scopes t` by fs[stmt_state_rel_def, state_rel_def] >>
     drule exprSimPropsTheory.local_region_frame >>
     disch_then (qspec_then `sm` mp_tac) >> simp[] >> metis_tac[]) >>
  `local_region ce es.scopes s0 n lb lsz` by metis_tac[] >>
  qpat_x_assum `!name p n. local_region _ _ s0 _ _ _ ==> _`
    (drule_then mp_tac) >> simp[regions_disjoint_def]
QED

Resume intcall_tuple_literal_outcome[frame]:
  rpt strip_tac >>
  qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` irule >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >-
    (qexists_tac `aid` >> conj_tac >- fs[ci_mono_def] >> metis_tac[]) >>
  qpat_x_assum `!aid p n. aid < sa.cs_next_id /\ _ ==> _` drule_all >>
  simp[regions_disjoint_def]
QED

Resume intcall_tuple_literal_outcome[pure_frame]:
  rewrite_tac[expr_has_effect_thm] >> strip_tac >>
  `EVERY ($~ o expr_has_effect) args` by gvs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, combinTheory.o_DEF] >>
  qpat_x_assum `EVERY ($~ o expr_has_effect) _ ==> _` drule >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  irule aggregate_pure_frame_buffer >>
  qpat_assum `MEM (venomInst$mk_inst _ ALLOCA _ _) _` (irule_at Any) >>
  `FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,type_memory_size_list tvs)` by metis_tac[] >>
  qexistsl_tac [`t`, `sm`, `b`, `type_memory_size_list tvs`] >>
  gvs[] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Resume intcall_tuple_literal_outcome[provenance]:
  `lookup_var x t' = SOME (n2w b)` by metis_tac[] >>
  simp[intcall_vv_provenance_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def, expr_type_def,
       read_result_def, return_def, venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  disj1_tac >> qexistsl [`inst.inst_id`, `b`, `type_memory_size_list tvs`] >>
  simp[val_footprint_def, type_memory_size_def] >>
  conj_tac >- (fs[ci_mono_def] >> metis_tac[]) >>
  suspend "owned_separation"
QED

Resume intcall_tuple_literal_outcome[owned_separation]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >> simp[]) >>
  rpt strip_tac >>
  `local_region ce es.scopes t n lb lsz` by
    (`local_ptrs_rel func ce es.scopes t` by fs[stmt_state_rel_def, state_rel_def] >>
     drule exprSimPropsTheory.local_region_frame >>
     disch_then (qspec_then `sm` mp_tac) >> simp[] >> metis_tac[]) >>
  `local_region ce es.scopes s0 n lb lsz` by metis_tac[] >>
  qpat_x_assum `!name p n. local_region _ _ s0 _ _ _ ==> _`
    (drule_then mp_tac) >> simp[regions_disjoint_def]
QED

Finalise intcall_tuple_literal_outcome

Theorem intcall_array_literal_outcome:
  exprs_case F ctx func ce cx args /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es /\
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) bnd) args) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (Builtin ann (MakeArray (SOME et) bnd) args) es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (expr_type (Builtin ann (MakeArray (SOME et) bnd) args))
        sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule compile_array_literal_inv >> strip_tac >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    (qspec_then `compile_expr` mp_tac ci_mono_compile_make_array_cfn >>
     simp[cj 1 compile_expr_ci_mono] >>
     disch_then (qspecl_then [`ce`, `args`, `et`, `type_memory_bytes ce et`,
       `(case bnd of Dynamic _ => T | _ => F)`, `ba.buf_operand`, `sm`] mp_tac) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes ce (ArrayT et bnd) < 2 ** 64` by
    fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
       allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def] >>
  `type_memory_bytes ce (ArrayT et bnd) < dimword (:256)` by
    (qpat_x_assum `type_memory_bytes ce (ArrayT et bnd) < _` mp_tac >>
     simp[wordsTheory.dimword_def]) >>
  drule_all buffer_alloc_counted >> strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
      expr_body_pre ce cx env e st` by
    (rpt strip_tac >> irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >>
     qexistsl_tac [`ArrayT et bnd`, `args`, `MakeArray (SOME et) bnd`, `es`] >> simp[]) >>
  suspend "fold"
QED

Resume intcall_array_literal_outcome[fold]:
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b
      ((if (case bnd of Dynamic _ => T | _ => F) then 32 else 0) + LENGTH args * type_memory_size tv)` by
    suspend "immutable" >>
  qpat_x_assum `compile_make_array _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) aggregate_body_make_array_sim >>
  disch_then (drule_at (Pat `EVERY _ args`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = _`)) >>
  disch_then (qspecl_then [`env`, `es`, `func`, `ctx`] mp_tac) >>
  impl_tac >-
    (simp[] >> qpat_x_assum `ce.ce_is_ctor ==> _` mp_tac >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >> strip_tac >>
  suspend "outcome"
QED

Resume intcall_array_literal_outcome[immutable]:
  qpat_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  fs[immutable_alloca_sep_def] >> rpt strip_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` (mp_tac o UNDISCH) >>
  disch_then drule_all >> strip_tac >>
  `regions_disjoint io (type_memory_size itv) b (type_memory_bytes ce (ArrayT et bnd))` by
    (qpat_x_assum `!ii bb nn. MEM ii _ /\ _ ==> regions_disjoint _ _ _ _` irule >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  fs[regions_disjoint_def] >>
  qpat_x_assum `LENGTH args * _ + _ <= _` mp_tac >>
  qpat_x_assum `b + type_memory_bytes ce (ArrayT et bnd) <= io` mp_tac >>
  decide_tac
QED

Resume intcall_array_literal_outcome[outcome]:
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  `eval_expr cx (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args) =
    bind (eval_exprs cx args) (\vs. return (Value (ArrayV (make_array_value tv bnd vs))))` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `eval_exprs cx args x'` >>
     drule_at (Pat `eval_exprs _ _ _ = _`) aggregate_eval_make_array >>
     disch_then (drule_at (Pat `compatible_bound _ _`)) >>
     disch_then (qspecl_then [`tv`, `et`, `ArrayT et bnd`] mp_tac) >>
     Cases_on `q` >> simp[bind_def, return_def]) >>
  asm_rewrite_tac[] >>
  irule gas_outcome_zero_prefix_any >> goal_assum (drule_at Any) >>
  dxrule counted_outcome_normal_facts >>
  disch_then (mp_tac o SIMP_RULE (std_ss ++ boolSimps.CONJ_ss) [GSYM LEFT_EXISTS_AND_THM, GSYM CONJ_ASSOC]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ _ Q _` >>
  `(\res ee r. ?vs. res = INL vs /\ Q (INL vs) ee r) = Q` by
    simp[FUN_EQ_THM, Abbr `Q`] >>
  qpat_assum `(_ : (value list + exception) -> evaluation_state -> venom_state -> bool) = Q`
    (fn eqth => qspecl_then
      [`\vs ee r. Q (INL vs) ee r`, `\res ee r. expr_exit res r`,
       `\vs. Value (ArrayV (make_array_value tv bnd vs))`]
      (drule o REWRITE_RULE [GSYM AND_IMP_INTRO, eqth] o BETA_RULE)
      (Q.GENL [`P`, `R`, `f`] counted_outcome_map_values)) >>
  impl_tac >- simp[Abbr `Q`] >>
  disch_then (qspecl_then [`tv`, `bnd`] assume_tac) >>
  qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` kall_tac >>
  suspend "post"
QED

Resume intcall_array_literal_outcome[post]:
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`) counted_outcome_conseq >>
  disch_then irule >> simp[Abbr `Q`] >> rpt gen_tac >> strip_tac >>
  qexists_tac `Value (ArrayV (make_array_value tv bnd vs))` >> simp[] >>
  drule_at (Pat `eval_exprs _ _ _ = _`) aggregate_eval_make_array >>
  disch_then (drule_at (Pat `compatible_bound _ _`)) >>
  disch_then (qspecl_then [`tv`, `et`, `ArrayT et bnd`] mp_tac) >>
  impl_tac >- simp[] >> disch_tac >>
  `expr_body_pre ce cx env (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args) (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[] >> strip_tac >>
  reverse conj_tac >- suspend "provenance" >>
  simp[vv_post_def, post_value_type_def] >>
  simp[contextTheory.mk_ptr_def, contextTheory.base_ptr_def, expr_type_def] >>
  conj_tac >- suspend "holds" >> conj_tac >- suspend "at" >>
  conj_tac >-
    (rpt strip_tac >> irule_at Any EQ_TRANS >> goal_assum (drule_at Any) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  conj_tac >- suspend "frame" >> reverse conj_tac >- suspend "pure_frame" >>
  irule exprBopSimPropsTheory.locals_kept_trans >>
  qexistsl_tac [`es`, `sa`, `t`] >> simp[] >>
  irule exprSimPropsTheory.locals_kept_mem >> simp[]
QED

Resume intcall_array_literal_outcome[holds]:
  simp[vv_holds_def, read_result_def, return_def, venomStateTheory.eval_operand_def,
       compileEnvTheory.is_word_type_def] >>
  `lookup_var x t' = SOME (n2w b)` by metis_tac[] >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule eval_exprs_length >> strip_tac >>
  irule bodyMemArrayLayoutTheory.array_from_dense_memory >>
  Cases_on `bnd` >> fs[]
QED

Resume intcall_array_literal_outcome[at]:
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `lookup_var x t' = SOME (n2w b)` by metis_tac[] >>
  simp[vv_at_def, read_result_def, return_def, venomStateTheory.eval_operand_def] >>
  gvs[expr_type_def] >>
  conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  disj1_tac >> qexistsl_tac [`inst.inst_id`, `b`, `type_memory_bytes ce (ArrayT et bnd)`] >>
  simp[val_footprint_def] >>
  conj_tac >- fs[ci_mono_def] >>
  conj_tac >- suspend "capacity" >>
  suspend "separation"
QED

Resume intcall_array_literal_outcome[capacity]:
  `type_memory_bytes ce (ArrayT et bnd) = type_memory_size (ArrayTV tv bnd)` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  Cases_on `bnd` >> fs[type_memory_size_def]
QED

Resume intcall_array_literal_outcome[separation]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >> simp[]) >>
  rpt strip_tac >>
  `local_region ce es.scopes t n lb lsz` by
    (`local_ptrs_rel func ce es.scopes t` by fs[stmt_state_rel_def, state_rel_def] >>
     drule exprSimPropsTheory.local_region_frame >>
     disch_then (qspec_then `sm` mp_tac) >> simp[] >> metis_tac[]) >>
  `local_region ce es.scopes s0 n lb lsz` by metis_tac[] >>
  qpat_x_assum `!name p n. local_region _ _ s0 _ _ _ ==> _`
    (drule_then mp_tac) >> simp[regions_disjoint_def]
QED

Resume intcall_array_literal_outcome[frame]:
  rpt strip_tac >>
  qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` irule >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >-
    (qexists_tac `aid` >> conj_tac >- fs[ci_mono_def] >> metis_tac[]) >>
  qpat_x_assum `!aid p n. aid < sa.cs_next_id /\ _ ==> _` drule_all >>
  simp[regions_disjoint_def]
QED

Resume intcall_array_literal_outcome[pure_frame]:
  rewrite_tac[expr_has_effect_thm] >> strip_tac >>
  `EVERY ($~ o expr_has_effect) args` by gvs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, combinTheory.o_DEF] >>
  qpat_x_assum `EVERY ($~ o expr_has_effect) _ ==> _` drule >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  irule aggregate_pure_frame_buffer >>
  qpat_assum `MEM (venomInst$mk_inst _ ALLOCA _ _) _` (irule_at Any) >>
  `FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,type_memory_bytes ce (ArrayT et bnd))` by metis_tac[] >>
  qexistsl_tac [`t`, `sm`, `b`, `type_memory_bytes ce (ArrayT et bnd)`] >>
  gvs[] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Resume intcall_array_literal_outcome[provenance]:
  `lookup_var x t' = SOME (n2w b)` by metis_tac[] >>
  simp[intcall_vv_provenance_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def, expr_type_def,
       read_result_def, return_def, venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  disj1_tac >> qexistsl [`inst.inst_id`, `b`, `type_memory_bytes ce (ArrayT et bnd)`] >>
  simp[val_footprint_def] >>
  conj_tac >- (fs[ci_mono_def] >> metis_tac[]) >>
  conj_tac >- suspend "owned_capacity" >>
  suspend "owned_separation"
QED

Resume intcall_array_literal_outcome[owned_capacity]:
  `type_memory_bytes ce (ArrayT et bnd) = type_memory_size (ArrayTV tv bnd)` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  Cases_on `bnd` >> fs[type_memory_size_def]
QED

Resume intcall_array_literal_outcome[owned_separation]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >> simp[]) >>
  rpt strip_tac >>
  `local_region ce es.scopes t n lb lsz` by
    (`local_ptrs_rel func ce es.scopes t` by fs[stmt_state_rel_def, state_rel_def] >>
     drule exprSimPropsTheory.local_region_frame >>
     disch_then (qspec_then `sm` mp_tac) >> simp[] >> metis_tac[]) >>
  `local_region ce es.scopes s0 n lb lsz` by metis_tac[] >>
  qpat_x_assum `!name p n. local_region _ _ s0 _ _ _ ==> _`
    (drule_then mp_tac) >> simp[regions_disjoint_def]
QED

Finalise intcall_array_literal_outcome
