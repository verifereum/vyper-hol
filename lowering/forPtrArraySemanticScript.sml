(* Source-semantic predicate boundaries for the array pointer loop.
   Pointer execution does not establish source typing; retain it separately. *)
Theory forPtrArraySemantic
Ancestors bodyPtrPreds bodyPtrDefs bodySim bodyExprPreFacts bodySimDeclCases forPtrSourceScopes
  forPtrArraySnapshot forPtrRangeCallback exprSimHypsDefs stmtLoweringProps
  stmtSimProps compileEnv finite_map list vyperState vyperInterpreter
Libs monadsyntax

Theorem for_array_body_fragment_ptr:
  body_stmts_ptr_ok cx stmts /\ body_inv tops ctx cenv cx /\
  supported_stmts tops bindings stmts /\
  (!target. supported_stmts_expr_exists
    (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env ei /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  EVERY (stmt_exprs_ok cenv) stmts /\
  type_memory_bytes cenv typ < 2 ** 64 /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
  declare_local cenv id typ st0 = (bc,sd) ==>
  stmt_frag_ptr d ctx PG func cx (InLoop ex inc) RetQ bc
    (stmts_env bc (InLoop ex inc) ret_ty stmts) (eval_stmts cx stmts)
    (ei with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: ei.scopes)
Proof
  strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[ce_locals_declared_def] >> metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv bc` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx bc cx` by metis_tac[body_inv_same_frame] >>
  qpat_x_assum `body_stmts_ptr_ok _ _`
    (irule o REWRITE_RULE [body_stmts_ptr_ok_def]) >>
  simp[] >> rpt conj_tac
  >- metis_tac[stmt_exprs_ok_same_frame]
  >- (qexistsl_tac [`bindings`, `tops`] >> simp[])
  >- (qexistsl_tac [`extend_local env id typ F`, `env_b`] >> simp[] >>
      `bc.ce_struct_fields = cenv.ce_struct_fields` by
        metis_tac[same_frame_struct_fields] >>
      conj_tac >- metis_tac[ce_locals_declared_declare_local] >>
      conj_tac >- metis_tac[locals_alloc_ok_extend] >>
      irule expr_sim_inv_for_scope >> metis_tac[]) >>
  fs[frame_ret_ok_ptr_def] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> metis_tac[same_frame_trans]
QED

Theorem for_array_body_pop_semantic:
  expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmts tops bindings stmts /\
  eval_stmts cx stmts (es with scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) = (r,ef) /\
  (r = INL () \/ r = INR ContinueException) ==>
  expr_sim_inv cenv cx env (ef with scopes := TL ef.scopes) /\
  lookup_scopes id (TL ef.scopes) = NONE
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = NONE` by metis_tac[expr_sim_inv_absent_local] >>
  drule_all fresh_body_scope_shape >> strip_tac >> simp[] >>
  irule expr_sim_inv_for_pop >> metis_tac[]
QED

(* Continuation rounds are exactly normal/continue source results.  Break
   produces INL T instead and does not need the next-header predicate. *)
Theorem for_array_handled_pop_semantic:
  expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmts tops bindings stmts /\
  finally (try (ignore_bind (eval_stmts cx stmts) (return F))
    handle_loop_exception) pop_scope
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) =
      (INL F,ee) ==>
  expr_sim_inv cenv cx env ee /\ lookup_scopes id ee.scopes = NONE
Proof
  strip_tac >>
  Cases_on `eval_stmts cx stmts (es with scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes)` >>
  rename1 `_ = (raw,after)` >>
  `lookup_scopes id es.scopes = NONE` by metis_tac[expr_sim_inv_absent_local] >>
  drule_all fresh_body_scope_shape >> strip_tac >>
  Cases_on `raw`
  >- (gvs[finally_def, try_def, ignore_bind_def, bind_def, return_def, pop_scope_def] >>
      irule expr_sim_inv_for_pop >> metis_tac[]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[finally_def, try_def, ignore_bind_def, bind_def, return_def,
    pop_scope_def, raise_def, handle_loop_exception_def] >>
  irule expr_sim_inv_for_pop >> metis_tac[]
QED

Theorem for_scope_cons_update[local]:
  !es sc. es with scopes updated_by CONS sc =
    es with scopes := sc :: es.scopes
Proof
  Cases >> simp[evaluation_state_fn_updates]
QED

Theorem for_array_round_semantic:
  expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmts tops bindings stmts /\
  (do push_scope_with_var id tv v;
      finally (try (do eval_stmts cx stmts; return F od)
        handle_loop_exception) pop_scope od) es = (INL F,ee) ==>
  expr_sim_inv cenv cx env ee /\ lookup_scopes id ee.scopes = NONE
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env (es with gas_obs := [])` by simp[] >>
  qpat_x_assum `(do _ od) es = _` mp_tac >>
  simp[push_scope_with_var_def, push_scope_def, new_variable_def,
    bind_def, ignore_bind_def, return_def] >> strip_tac >>
  fs[GSYM ignore_bind_def, for_scope_cons_update] >>
  drule_all for_array_handled_pop_semantic >> simp[]
QED
