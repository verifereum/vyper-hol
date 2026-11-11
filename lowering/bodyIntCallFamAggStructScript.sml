(* Seam 2 joint induction, a family leaf of the agg step: struct literals. *)
Theory bodyIntCallFamAggStruct
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggStructFields
  bodyIntCallFamAggStructSource bodyIntCallFamAggStructCode
  bodyIntCallFamAggStructLoop bodyIntCallJointAggCore
  exprSimAggregateLayout exprSimHypsDefs exprSimHyps structFieldsProps

Theorem intcall_struct_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a nm fields. e = StructLit a nm fields) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> gvs[] >>
  reverse conj_tac
  >- (irule intcall_map_producer_other >> simp[]) >>
  rw[intcall_expr_producer_def] >>
  drule compile_struct_literal_inv >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  drule struct_literal_lookup_types >> strip_tac >>
  `a = StructT nm` by
    (fs[expr_body_pre_def] >> metis_tac[struct_literal_decl_types]) >>
  gvs[] >>
  `type_memory_bytes ce (StructT nm) = type_memory_size_list tvs` by
    (`LENGTH (MAP FST fields) = LENGTH tvs` by
       metis_tac[vyperTypeABITheory.OPT_MMAP_LENGTH, listTheory.LENGTH_MAP] >>
     `expr_sim_inv ce fp.jc_cx env es` by fs[expr_body_pre_def] >>
     drule_all expr_sim_inv_memory_size >>
     simp[valueEncodingTheory.type_memory_size_def, struct_layout_size_zip]) >>
  `type_memory_size_list tvs < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def] >>
     fs[wordsTheory.dimword_def]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    (irule fragExecTheory.fn_has_code_split >>
     simp[] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
       exprLoweringPropsTheory.ci_mono_compile_struct_lit_cfn,
       exprLoweringPropsTheory.compile_expr_ci_mono,
       exprLoweringPropsTheory.ci_mono_def, pairTheory.SND]) >>
  drule intcall_alloc_landing >>
  disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  rename1 `gas_marked_path _ _ _ s 0 (OK landed)` >>
  `!child ee. MEM child (MAP SND fields) /\ expr_sim_inv ce fp.jc_cx env ee ==>
      expr_body_pre ce fp.jc_cx env child ee` by
    metis_tac[exprSimAggregateSourceTheory.expr_body_pre_struct_field] >>
  suspend "allocated"
QED

Resume intcall_struct_literal_step[allocated]:
  `!child. MEM child (MAP SND fields) ==>
     intcall_expr_producer fp child /\
     supportedExprs$supported_expr fp.jc_tops child /\
     calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr child)`
    by suspend "children" >>
  `EVERY (\tv. type_memory_size tv + 64 < dimword (:256)) tvs`
    by suspend "sizes" >>
  suspend "traversal"
QED

Resume intcall_struct_literal_step[children]:
  gen_tac >> disch_tac >> conj_tac
  >- (`expr_size child < expr_size (StructLit (StructT nm) nm fields)` by
        metis_tac[exprCallbackContractsTheory.struct_callback_child_bound] >>
      fs[vyperASTTheory.expr_size_def] >>
      qpat_x_assum `!e'. _ ==> _` (qspec_then `child` mp_tac) >> simp[]) >>
  conj_tac
  >- (fs[supportedExprsTheory.supported_expr_def,
          supportedExprsTheory.supported_pure_expr_def,
          supportedExprsTheory.supported_effect_expr_def,
          supportedExprsTheory.supported_pure_fields_every,
          listTheory.EVERY_MEM, listTheory.MEM_MAP] >> metis_tac[]) >>
  `!c. MEM c (int_calls_expr child) ==> MEM c (int_calls_named_exprs fields)` by
    (rpt strip_tac >>
     irule (cj 4 exprSimAggregateSourceTheory.aggregate_named_child_body_syntax) >>
     fs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
        byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def] >> metis_tac[]) >>
  fs[vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def,
     vyperTypeCallGraphTheory.int_calls_expr_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Resume intcall_struct_literal_step[sizes]:
  `type_memory_size_list tvs < 2 ** 64` by
    fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  `type_memory_size tv <= type_memory_size_list tvs` by
    (rewrite_tac[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule listTheory.SUM_MAP_MEM_bound >> simp[]) >>
  fs[wordsTheory.dimword_def]
QED

Resume intcall_struct_literal_step[traversal]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `fp.jc_lo <= w2n w` by
    (fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def,
        intCallFrameTheory.allocas_above_def] >> metis_tac[]) >>
  `!name a n. local_region ce es.scopes s name a n ==>
     regions_disjoint (w2n w) (type_memory_size_list tvs) a n` by
    (rpt strip_tac >>
     `local_region ce es.scopes landed name a n` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s`,`sa`,`es.scopes`] >>
        fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def]) >>
     metis_tac[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)
    intcall_struct_fields_counted >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[venomInstTheory.mk_inst_def] >>
  impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    metis_tac[]) >>
  strip_tac >> suspend "result"
QED

Resume intcall_struct_literal_step[result]:
  drule_all stmtReasonVvMemoryTheory.gas_outcome_zero_prefix_any >>
  disch_tac >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (StructLit (StructT nm) nm fields)) (es,s)
    (\res ee u. ?vs. res = INL (Value (StructV (ZIP (MAP FST fields,vs)))) /\
       LENGTH vs = LENGTH fields /\
       fields_in_memory (ZIP (MAP FST fields,vs)) (ZIP (MAP FST fields,tvs))
         (w2n w) u.vs_memory /\
       intcall_expr_cont fp ce env es sa s ee sb u /\
       FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size_list tvs) /\
       eval_operand ba.buf_operand u = SOME w /\
       (!name a n. local_region ce ee.scopes u name a n ==>
         regions_disjoint (w2n w) (type_memory_size_list tvs) a n))
    (\res ee r. expr_exit res r)` by
    (PairCases_on `nm` >>
     simp[Once vyperInterpreterTheory.evaluate_def] >>
     irule (BETA_RULE (Q.ISPEC `\vs. Value (StructV (ZIP (MAP FST fields,vs)))`
       (Q.GEN `f` gas_outcome_return_map))) >> goal_assum (drule_at Any) >>
     conj_tac
     >- (Cases >> simp[exprSimDefsTheory.expr_exit_INL,
       stmtSimPropsTheory.expr_exit_INR_type]) >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  suspend "post"
QED

Resume intcall_struct_literal_step[post]:
  qpat_x_assum `gas_outcome _ _ _ (eval_expr _ _) (es,s) _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def,
    gasSummaryTheory.gas_summary_at_def] >>
  strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
      suspend "normal")
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`r`] >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Resume intcall_struct_literal_step[normal]:
  gvs[] >>
  `val_wf (StructTV (ZIP (MAP FST fields,tvs)))
      (StructV (ZIP (MAP FST fields,vs)))` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     irule exprSimAggregateSourceTheory.aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     qexistsl_tac [`ce`,`env`] >>
     simp[vyperASTTheory.expr_type_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  simp[fragExecTheory.exit_result_def, vyperASTTheory.expr_type_def] >>
  simp[loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
    contextTheory.base_ptr_def, contextTheory.vv_operand_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
  suspend "ownership"
QED

Resume intcall_struct_literal_step[ownership]:
  `LENGTH (MAP FST fields) = LENGTH tvs` by
    metis_tac[vyperTypeABITheory.OPT_MMAP_LENGTH, listTheory.LENGTH_MAP] >>
  `sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_struct_lit_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  conj_tac
  >- (pure_rewrite_tac[Once valueEncodingDefsTheory.val_in_memory_def] >> simp[]) >>
  reverse conj_tac
  >- (conj_tac
      >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      qexistsl_tac [`w2n w`,`type_memory_size_list tvs`] >>
      simp[valueEncodingTheory.type_memory_size_def, struct_layout_size_zip]) >>
  disj1_tac >>
  qexistsl_tac [`sa.cs_next_id`,`w2n w`,`type_memory_size_list tvs`] >>
  simp[loweringPostsTheory.val_footprint_def,
    valueEncodingTheory.type_memory_size_def, struct_layout_size_zip] >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Finalise intcall_struct_literal_step
