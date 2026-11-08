Theory bodyForArrayPtr
Ancestors forPtrArrayFrag bodyPtrPreds bodyPtrDefs bodySimDeclCases
  stmtSimForArray exprSimHypsDefs exprSimHyps bodySim bodyExprPreFacts
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeValues
  supportedStmts supportedStmtTraverse allocLimits compileVyper
  vyperTypeCallGraph exprLoweringProps finite_map list vyperTypeCallStackSoundness
Libs monadsyntax

val _ = Parse.hide "body";

Theorem body_for_array_ptr:
  (!tenv s'' tyv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array e) s3 = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tyv id body vs) ==>
  body_stmt_ptr_ok cx (For id typ (Array e) n body)
Proof
  strip_tac >> rewrite_tac[body_stmt_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all array_for_hypotheses >> strip_tac >> gvs[] >>
  drule_all array_name_local_binding >> strip_tac >>
  rename1 `lookup_scopes name es.scopes = SOME entry` >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `?al. entry.value = ArrayV (SArrayV al)` by
    (Cases_on `entry.value` >> gvs[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >>
     gvs[value_has_type_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT typ (Fixed n)) =
     SOME (ArrayTV tv (Fixed n))` by
    (fs[expr_sim_inv_def, well_typed_expr_def, env_consistent_def,
        env_scopes_consistent_def] >> metis_tac[]) >>
  `!gs. eval_iterator cx (Array (Name (ArrayT typ (Fixed n)) name))
          (es with gas_obs := gs) =
        (INL (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)),
         es with gas_obs := gs)` by
    (gen_tac >> irule eval_iterator_fixed_name >> simp[]) >>
  qabbrev_tac `vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV al)` >>
  `LENGTH vs = n` by simp[Abbr `vs`, fixed_array_elements_length] >>
  `body_for_ptr_ok cx tv id body vs` by
    (qpat_x_assum `!s'' tyv t s3 vs t' s4 t''. _` mp_tac >>
     simp[lift_option_type_def, return_def, check_def, assert_def,
          compatible_bound_def] >> disch_then irule >> simp[] >>
     qexistsl_tac [`es`, `es`] >> simp[] >>
     simp[Abbr `vs`] >> irule eval_iterator_fixed_name >> simp[]) >>
  `body_stmts_ptr_ok cx body` by
    (fs[body_for_ptr_ok_def] >> `vs <> []` by (strip_tac >> gvs[]) >> metis_tac[]) >>
  suspend "fragment"
QED

Resume body_for_array_ptr[fragment]:
  `!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops` by
    (qpat_x_assum `!target. supported_stmt_expr_exists _ _ ==> _` mp_tac >>
     simp[supported_stmt_expr_exists_def]) >>
  `FLOOKUP env.var_types name = SOME (ArrayT typ (Fixed n))` by
    fs[well_typed_expr_def, expr_type_def] >>
  `EVERY (stmt_exprs_ok cenv) body /\ type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_EVERY, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  `type_memory_bytes cenv typ = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv typ + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  qpat_x_assum `LENGTH vs = n` (SUBST_ALL_TAC o SYM) >>
  irule compile_for_array_frag_ptr >>
  simp[IgnAsm `vs = _`] >> metis_tac[]
QED

Finalise body_for_array_ptr
