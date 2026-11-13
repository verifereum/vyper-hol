(* Memory case of the body induction, assignment to a tuple of locals
   (bodyMemAssignTuple's dispatch): the memory twin of S1's
   body_assign_tuple_locals (bodySimStmtCases). *)
Theory bodyMemAssignTupleLocals
Ancestors
  bodyMemoryPreds bodyMemAssignTupleLocalsPrep bodyMemAssignTupleLocalsOutcome
  bodySimStmtCases
  bodySim bodyExprPreFacts vyperTypeSystem vyperTypeInvariants
  exprSimHyps exprSimHypsDefs exprSimDefs valueEncoding finite_map list
  valueTypingMemoryProps vyperTypeValues vyperTyping vyperTypeDefaults
  vyperTypeExprSoundness compileVyper vyperCompiler exprSimSource bodySimStmtCases
Libs
  monadsyntax

(* S1 bodySimStmtCases.expr_body_pre_eval_gas [local]. *)
Theorem expr_body_pre_eval_gas[local]:
  !cenv cx env e es gs res es'.
    expr_body_pre cenv cx env e es /\
    (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := gs) = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==> value_runtime_typed env (expr_type e) v
Proof
  rpt gen_tac >> strip_tac >> irule bodySimStmtCasesTheory.expr_body_pre_eval >>
  qexists_tac `es with gas_obs := gs` >> fs[]
QED

Theorem body_assign_tuple_locals_mem:
  !cx ids e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_stmt_safe tops (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    body_expr_mem_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids /\
    lowered_value_type cenv e = expr_type e ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (eval_stmt cx
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  rpt strip_tac >>
  drule_all tuple_locals_source_types >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule body_assign_tuple_rhs_pre >> metis_tac[]) >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  irule compile_assign_tuple_locals_memory_stmt_frag_mem >>
  simp[] >> rpt conj_tac
  >~ [`expr_sim_mem _ _ _ _ _ _ _`] >- metis_tac[body_expr_mem_ok_def]
  >~ [`cenv.ce_target CapMcopy`] >- metis_tac[body_inv_mcopy]
  >~ [`type_memory_size (TupleTV _) < _`]
  >- (strip_tac >> irule tuple_staging_bound >> metis_tac[])
  >~ [`FLOOKUP cenv.ce_vars _`]
  >- (rpt strip_tac >>
      `EVERY (\id. !ty. FLOOKUP env.var_types id = SOME ty ==>
         0 < type_memory_bytes cenv ty) ids` by
        metis_tac[assign_tuple_locals_bytes_pos] >>
      `0 < type_memory_bytes cenv (EL i tys)` by
        (fs[EVERY_EL] >> metis_tac[]) >>
      irule tuple_target_local_ptr >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`store_lays_out _ _ _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval_gas >> strip_tac >>
      `value_has_type (EL i tvs) (EL i vs)` by
        gvs[value_runtime_typed_def, value_has_type_def,
            values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
      irule tuple_target_local_lays_out >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (rpt strip_tac >> drule_all expr_body_pre_eval_gas >> strip_tac >>
      gvs[value_runtime_typed_def]) >> simp[]
QED
