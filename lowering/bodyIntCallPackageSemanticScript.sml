(* Consumer-facing semantic inputs for a callee's statement producer. *)
Theory bodyIntCallPackageSemantic
Ancestors
  bodyIntCallProducerSemantic bodyIntCallEntryInputs bodyIntCallSeamDefs
  bodyIntCallHandler bodyIntCallBodyTyping vyperInterpreter vyperState
  bodyIntCallJointContract bodySim exprSimHypsDefs
Libs
  monadsyntax

Theorem intcall_rest_stmts_admissible:
  gas_admissible (intcall_rest cx name mut ss prev rtv) expr_vv_res_ok es ==>
  gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
    (stmt_res_ok NoLoop) es
Proof
  `ignore_bind (pop_function prev) (unlock_if_nr cx F (is_view_mut mut)) =
    set_scopes prev` by
    simp[pop_function_def, unlock_if_nr_def, ignore_bind_def, bind_def,
         set_scopes_def, return_def, FUN_EQ_THM] >>
  simp[intcall_rest_def] >>
  metis_tac[function_rest_body_admissible]
QED

Theorem intcall_entry_body_typing:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,F,args,[],ret,ss) /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t ==>
  ?env_body env_after.
    env_body.current_src = NONE /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = tenv.fn_sigs /\
    env_body.bare_globals = tenv.bare_globals /\
    env_body.bare_global_assignable = tenv.bare_global_assignable /\
    env_body.toplevel_vtypes = tenv.toplevel_vtypes /\
    env_body.flag_members = tenv.flag_members /\
    type_stmts env_body ret ss = SOME env_after /\
    IS_SOME (type_stmts (env_body with bare_global_assignable := FEMPTY) ret ss) /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\ stmts_no_control_escape ss /\
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env_body.var_types id = SOME ty /\
      IS_SOME (FLOOKUP env_body.var_assignable id)) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==> ?ty. MEM (n,ty) args) /\
    env_consistent env_body (cx with stk updated_by CONS (NONE,name)) es1
Proof
  strip_tac >> drule intcall_entry_semantic_inputs >> strip_tac >>
  drule intcall_entry_source >> strip_tac >>
  drule internal_decl_lookup_not_none >> strip_tac >>
  fs[cenv_module_pins_def] >>
  drule_all pinned_internal_bound_body_typing >> strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  `es1 with scopes := [penv] = es1` by simp[evaluation_state_component_equality] >>
  fs[] >> metis_tac[]
QED
