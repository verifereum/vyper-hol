(* Body adapter for the checked supported mixed-target pointer fragment. *)
Theory assignTuplePtrBodyTargets
Ancestors
  assignTuplePtrMixedReady assignTuplePtrBodyReady assignTuplePtrTargets
  bodyPtrPreds bodySim bodySimStmtCases bodyExprPreFacts gasContext
  supportedStmtTraverse supportedStmts exprSimHyps exprSimHypsDefs
  exprSimAggregateLayout stmtSimReturn stmtSimDeclStore
  tupleTargetStoreProps vyperTypeInvariants vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeValues vyperTypeSystem vyperTypeEnv
  vyperTypeExprSoundness vyperTyping vyperTypeDefaults
  vyperInterpreter vyperState vyperValue compileEnv exprLoweringProps
  stmtLowering loweringPosts list finite_map words arithmetic
Libs
  monadsyntax

Theorem tuple_rhs_body_pre_ptr:
  body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==>
     occurs_abi_decode_target target tops) /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem tuple_locals_bytes_pos_ptr:
  !cenv cx env es ret_ty ids e env'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty
      (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) = SOME env' ==>
    EVERY (\id. !ty. FLOOKUP env.var_types id = SOME ty ==>
                     0 < type_memory_bytes cenv ty) ids
Proof
  rpt strip_tac >>
  `?tys. LIST_REL (\tgt ty. well_typed_atarget env tgt ty)
           (MAP (BaseTarget o NameTarget) ids) tys /\
         assignable_type env.type_defs (TupleT tys)` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
         AllCaseEqs()] >> metis_tac[]) >>
  `EVERY (assignable_type env.type_defs) tys` by fs[assignable_type_def, EVERY_MEM] >>
  rw[EVERY_EL] >>
  `n < LENGTH tys /\
   well_typed_atarget env (BaseTarget (NameTarget (EL n ids))) (EL n tys)` by
    (fs[LIST_REL_EL_EQN] >> first_x_assum (qspec_then `n` mp_tac) >> simp[EL_MAP]) >>
  `ty = EL n tys` by
    gvs[well_typed_atarget_def, well_typed_target_def,
        vyperTypeEnvTheory.type_place_target_NameTarget, AllCaseEqs()] >>
  `assignable_type env.type_defs ty` by metis_tac[EVERY_EL] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  irule expr_sim_inv_memory_bytes_pos >> metis_tac[]
QED

Theorem body_assign_tuple_targets_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==>
     occurs_abi_decode_target target tops) /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  lowered_value_type cenv e = expr_type e /\
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
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
    (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt strip_tac >>
  drule tuple_targets_typing >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tup_tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tup_tv` by
    fs[assignable_type_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by (irule tuple_rhs_body_pre_ptr >> metis_tac[]) >>
  `LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `!i. i < LENGTH gs ==>
     tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
     (~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
     !es1 v. expr_sim_inv cenv cx env es1 /\ value_has_type (EL i tvs) v ==>
       tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) v` by
    (qx_gen_tac `i` >> disch_tac >> irule tuple_target_body_ready_ptr >>
     fs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `gs <> []` by (strip_tac >> gvs[assignable_type_def]) >>
  suspend "apply"
QED

Resume body_assign_tuple_targets_ptr[apply]:
  irule compile_assign_tuple_targets_stmt_frag_ptr >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`tvs`, `tys`] >> rpt conj_tac
  >~ [`expr_sim_ptr _ _ _ _ _ _ _ _ _`] >- metis_tac[body_expr_ptr_ok_def]
  >~ [`cenv.ce_target CapMcopy`] >- metis_tac[body_inv_mcopy_ptr]
  >~ [`type_memory_size (TupleTV _) < _`]
  >- (strip_tac >> irule tuple_staging_bound_ptr >> metis_tac[])
  >~ [`tuple_target_layout _ _ _ _ _`]
  >- (rpt strip_tac >> drule_all (GEN_ALL expr_body_pre_eval_gas_ptr) >> strip_tac >>
      gvs[value_runtime_typed_def, value_has_type_def,
          values_have_types_LIST_REL, LIST_REL_EL_EQN] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (rpt strip_tac >> drule_all (GEN_ALL expr_body_pre_eval_gas_ptr) >> strip_tac >>
      gvs[value_runtime_typed_def]) >> metis_tac[]
QED

Finalise body_assign_tuple_targets_ptr
