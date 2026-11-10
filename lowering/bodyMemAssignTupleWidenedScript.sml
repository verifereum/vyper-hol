(* Memory case of the body induction, tuple assignment (bodyMemAssignTuple's
   dispatch): a right-hand side whose lowered type is not its type (an
   internal call whose return type the call's type widens), assigned to
   memory locals, scalar toplevels and storage word fields (the targets
   bodyMemAssignTupleTargets covers); other targets are
   bodyMemAssignTupleOther's body_assign_tuple_widened_other_mem.  HELD with S1's
   body_assign_tuple_widened_call (bodySimStmtCases), still admitted there. *)
Theory bodyMemAssignTupleWidened
Ancestors
  tupleWidenedReadiness bodyMemAssignTupleWidenedWrapper exprSimIfExp
  bodyMemAssignTupleTargetsFacts bodyExprPreFacts tupleTargetStoreProps
  bodyMemAssignTupleLocalsPrep exprLoweringProps
  bodySimStmtCases bodyMemoryDefs exprSimDefs exprSimHypsDefs
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants supportedStmts supportedExprs
  stmtSimDefs loweringPosts list rich_list compileEnv vyperTypeValues
  vyperTyping vyperTypeDefaults vyperTypeExprSoundness exprSimSource
  bodyMemoryPreds tupleWidenedTargetStore tupleWidenedLayout tupleUnstagedParts typedCopyPrimitivePathMem typedCopyArrayPathMem typedCopyDynarrayPathMem typedCopyFieldsPathMem typedCopyRankPathMem

Theorem body_assign_tuple_widened_call_mem:
  !cx gs e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_mem_ok cx (TupleTarget gs) v) /\
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    lowered_value_type cenv e <> expr_type e /\
    EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                         FLOOKUP env.var_types id = SOME ty /\
                         0 < type_memory_bytes cenv ty) \/
                (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                        supported_scalar_target tops nsid) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env
                     (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt strip_tac >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (simp[stmt_frag_mem_def] >> rpt strip_tac >>
      fs[stmt_state_rel_def, state_rel_def]) >>
  drule tuple_targets_typing >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (irule body_assign_tuple_rhs_pre >> metis_tac[]) >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs` by
    metis_tac[LIST_REL_LENGTH] >>
  drule tuple_widened_source_ready >> simp[] >> strip_tac >>
  `!i. i < LENGTH gs ==>
     tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
     (~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
     !ee v. expr_sim_inv cenv cx env ee /\ value_has_type (EL i tvs) v ==>
       tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs) v` by
    metis_tac[tuple_targets_destination_ready] >>
  irule compile_assign_tuple_widened_stmt_frag_mem >>
  simp[] >> rpt conj_tac
  >~ [`expr_sim_mem _ _ _ _ _ _ _`]
  >- metis_tac[body_expr_mem_ok_def]
  >~ [`0 < type_memory_size_list _`]
  >- (qexistsl_tac [`tvs`, `tys`, `env`] >> simp[] >>
      reverse conj_tac >- metis_tac[] >>
      `0 < type_memory_size (TupleTV tvs')` suffices_by
        simp[valueEncodingTheory.type_memory_size_def] >>
      irule ifexp_physical_source_positive >> metis_tac[])
  >> metis_tac[]
QED
