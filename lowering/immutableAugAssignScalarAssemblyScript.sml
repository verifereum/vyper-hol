(* Scalar constructor entry, source replay, and memory-safe suffix assembly. *)
Theory immutableAugAssignScalarAssembly
Ancestors
  bodyMemoryPreds immutableAugAssignRootEntry immutableAugAssignSuffixMemory
  immutableAugAssignSourceOutcome augAssignPlaceCompositeMemory stmtReasonVvMemory

Theorem immutable_augassign_scalar_assembly:
  (!s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx (TopLevelNameTarget nsid) s = (INL p,s1) /\
    read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty (TopLevelNameTarget nsid) bop e) /\
  body_stmt_safe tops (AugAssign ty (TopLevelNameTarget nsid) bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty (TopLevelNameTarget nsid) bop e) ==>
     occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget nsid) bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty (TopLevelNameTarget nsid) bop e)) /\
  frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
  immutable_root cx (TopLevelNameTarget nsid) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e))
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e)) es
Proof
  strip_tac >> PairCases_on `nsid` >>
  rw[stmtSimDefsTheory.stmt_frag_mem_def] >>
  `alloca_inv s0` by metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule_all immutable_augassign_root_entry >> strip_tac >>
  `body_expr_mem_ok cx e` by metis_tac[] >>
  `supported_expr tops e` by fs[supportedStmtsTheory.supported_stmt_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule bodyAugAssignOtherTheory.augassign_rhs_pre >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx ty e es` by metis_tac[body_expr_mem_ok_def] >>
  drule_all immutable_augassign_root_metadata >> strip_tac >> gvs[] >>
  drule_all immutableAugAssignSourceContinuationTheory.immutable_augassign_root_replay >>
  disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  irule gas_outcome_zero_prefix_any >> goal_assum (drule_at Any) >>
  irule immutable_augassign_root_source_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  irule_at Any immutable_augassign_scalar_suffix_mem >>
  qpat_assum `lower_value _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_binop _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >> simp[] >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  qexistsl [`sa`, `s0`, `lctx`, `es`] >> simp[] >>
  suspend "suffix_preparation"
QED

Resume immutable_augassign_scalar_assembly[suffix_preparation]:
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[stmtSimAugAssignTheory.well_typed_binop_augassign_word] >>
  `word_value iv` by metis_tac[exprSimSourceTheory.word_value_type_typed] >>
  `type_memory_size tv = 32` by
    metis_tac[bodyImmutableAugAssignStoreTheory.immutable_augassign_word_encoding] >>
  `type_bits ty MOD 8 = 0` by
    (irule stmtSimAugAssignTheory.well_formed_type_bits >>
     qexists `get_tenv cx` >> simp[vyperTypeSystemTheory.well_formed_type_def] >>
     metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv es u` by
    (irule stmtSimDefsTheory.alloca_frame_of_mem_frame >> metis_tac[]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  simp[exprSimPropsTheory.typed_val_to_w256_word_value] >>
  (conj_tac >- metis_tac[stmtSimDeclMemTheory.emit_void_nonterminator_open,
                        venomInstTheory.is_terminator_def]) >>
  (conj_tac >- fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `is_word_type (expr_type e)` by
    metis_tac[exprSimSourceTheory.word_value_type_word] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >> simp[] >>
  (conj_tac >- (
    drule_all immutableAugAssignSourceContinuationTheory.immutable_augassign_source_replay >>
    strip_tac >> fs[gasContextTheory.gas_admissible_def] >> metis_tac[])) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[stmtSimPropsTheory.stmt_env_reserved,
              stmtLoweringMonoTheory.compile_stmt_cs_mono] >>
  rpt gen_tac >> strip_tac >> metis_tac[aug_place_memory_post]
QED

Finalise immutable_augassign_scalar_assembly
