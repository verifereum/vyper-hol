(* Body adapter for the checked compatible-local pointer fragment. *)
Theory assignTuplePtrBodyLocals
Ancestors
  assignTuplePtrBodyReady assignTuplePtrLocals bodyPtrPreds bodySim
  bodySimStmtCases bodyExprPreFacts gasContext supportedStmtTraverse
  vyperTypeInvariants vyperTypeCallGraph vyperTypeCallStackSoundness vyperTypeValues
  exprSimHyps exprSimHypsDefs exprSimAggregateLayout
  stmtSimReturn stmtSimDeclStore supportedStmts vyperTypeSystem vyperTypeEnv
  vyperTypeExprSoundness vyperTyping vyperTypeDefaults
  vyperInterpreter vyperState vyperValue compileEnv exprLoweringProps
  stmtLowering loweringPosts list finite_map words arithmetic
Libs
  monadsyntax


Theorem body_assign_tuple_locals_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) ==>
     occurs_abi_decode_target target tops) /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty
    (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
  ids <> [] /\
  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                   0 < type_memory_bytes cenv ty) ids /\
  lowered_value_type cenv e = expr_type e ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
    (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tys. expr_type e = TupleT tys /\ well_typed_expr env e /\
         assignable_type (get_tenv cx) (TupleT tys) /\
         LENGTH tys = LENGTH ids /\
         !i. i < LENGTH ids ==>
             FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by
    gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
        LIST_REL_EL_EQN, EL_MAP, well_typed_target_def,
        well_typed_expr_def, AllCaseEqs()] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
     qexists_tac `[]` >> simp[] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  suspend "apply"
QED

Resume body_assign_tuple_locals_ptr[apply]:
  irule compile_assign_tuple_locals_memory_stmt_frag_ptr >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`tvs`, `tys`] >> rpt conj_tac
  >~ [`expr_sim_ptr _ _ _ _ _ _ _ _ _`] >- metis_tac[body_expr_ptr_ok_def]
  >~ [`cenv.ce_target CapMcopy`] >- metis_tac[body_inv_mcopy_ptr]
  >~ [`type_memory_size (TupleTV _) < _`]
  >- (strip_tac >> irule tuple_staging_bound_ptr >> metis_tac[])
  >~ [`FLOOKUP cenv.ce_vars _`]
  >- (rpt strip_tac >>
      `FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)` by simp[] >>
      `0 < type_memory_bytes cenv (EL i tys)` by
        (qpat_x_assum `EVERY _ ids` mp_tac >> simp[EVERY_EL] >>
         disch_then drule >> strip_tac >> gvs[]) >>
      irule tuple_target_local_ready_ptr >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`if is_word_type _ then _ else _`]
  >- (rpt strip_tac >> drule_all (GEN_ALL expr_body_pre_eval_gas_ptr) >> strip_tac >>
      `value_has_type (EL i tvs) (EL i vs)` by
        gvs[value_runtime_typed_def, value_has_type_def,
            values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
      irule tuple_target_local_value_layout_ptr >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (rpt strip_tac >> drule_all (GEN_ALL expr_body_pre_eval_gas_ptr) >> strip_tac >>
      gvs[value_runtime_typed_def]) >>
  fs[]
QED

Finalise body_assign_tuple_locals_ptr
