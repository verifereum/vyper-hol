(* Source typing at the actual, gas-replay reachable internal-call endpoint. *)
Theory tupleAssignImmutableDeployIntSourceTyping
Ancestors
  bodyIntCallSeams bodySim exprSimHypsDefs vyperTypeStmtSoundness vyperTypeBindArguments
  vyperTypeEvalSoundness vyperTypeSystem vyperTypeInvariants
  vyperTypeStmtResult vyperTypeExprSoundness finite_map
  vyperInterpreter vyperState vyperContext vyperValue
Libs
  monadsyntax

Theorem tuple_immutable_intcall_source_return_typed:
  !tops ctx func cenv cx tenv ann name es dflt es0 sa sb vv s0
   mut args ret ss rr prev penv rtv es1 t.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
      (mut,args,ret,ss,rr) prev penv rtv es1 t ==>
    !gs v ee.
      intcall_callee_src cx name ss (es1 with gas_obs := gs) = (INL v,ee) ==>
      value_has_type rtv v
Proof
  rpt gen_tac >> strip_tac >>
  `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `IS_SOME (FLOOKUP tenv.fn_sigs (NONE,name))` by
    (fs[expr_body_pre_def, Once well_typed_expr_def] >> simp[]) >>
  `functions_well_typed cx /\ env_consistent tenv cx es0` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  drule_all callable_body_typing_from_env_consistent >>
  strip_tac >>
  `evaluate_type (get_tenv cx) ret = SOME rtv /\
   call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
     (int_calls_stmts ss) /\ es1.scopes = [penv] /\
   expr_sim_inv cenv cx tenv (es1 with scopes := prev) /\
   ?vs. bind_arguments (get_tenv cx) args vs = SOME penv` by
    (fs[intcall_entry_def] >> metis_tac[]) >>
  qhdtm_x_assum `intcall_entry` kall_tac >>
  `scope_well_typed penv` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `env_scopes_consistent env_body cx (es1 with scopes := [penv])` by
    (irule bind_arguments_env_scopes_consistent >>
     qexistsl [`args`, `get_tenv cx`, `vs`] >> simp[] >> metis_tac[]) >>
  `env_consistent tenv cx (es1 with scopes := prev) /\
   state_well_typed (es1 with scopes := prev) /\
   context_well_typed cx /\ accounts_well_typed es1.accounts /\
   functions_well_typed cx` by fs[expr_sim_inv_def] >>
  qpat_x_assum `env_consistent tenv cx es0` kall_tac >>
  drule intcall_default_env_side_conditions >>
  disch_then (qspecl_then [`env_body`, `NONE`, `name`] mp_tac) >>
  simp[] >> strip_tac >>
  `env_consistent env_body (cx with stk updated_by CONS (NONE,name)) es1` by
    (fs[env_consistent_def, env_immutables_consistent_def,
        env_scopes_consistent_stk_irrelevant, env_scopes_consistent_def,
        vyperContextTheory.get_tenv_def, vyperContextTheory.get_module_code_def] >>
     metis_tac[]) >>
  `state_well_typed es1` by
    fs[state_well_typed_def] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `intcall_callee_src` mp_tac >>
  simp[intcall_callee_src_def, try_def, bind_def, return_def] >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss
              (es1 with gas_obs := gs)` >>
  (Cases_on `q`
  >- (simp[ignore_bind_def, bind_def, return_def] >> strip_tac >>
      gvs[evaluate_type_def, vyperTypingTheory.value_has_type_def] >>
      imp_res_tac (cj 2 no_fallthrough_eval_no_success) >>
      Cases_on `x` >> gvs[]) >>
  simp[ignore_bind_def, bind_def, return_def] >>
  Cases_on `y` >> simp[handle_function_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  `env_consistent env_body (cx with stk updated_by CONS (NONE,name))
     (es1 with gas_obs := gs) /\
   state_well_typed (es1 with gas_obs := gs) /\
   accounts_well_typed (es1 with gas_obs := gs).accounts` by simp[] >>
  drule_all eval_stmts_type_preservation_exception >>
  simp[stmt_error_ok_def, return_exception_typed_def,
       value_runtime_typed_def] >>
  gvs[])
QED
