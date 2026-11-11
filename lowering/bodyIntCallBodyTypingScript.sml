(* Caller invariants discharge the public callable-typing entry interface. *)
Theory bodyIntCallBodyTyping
Ancestors
  bodyIntCallSemanticEntry bodyIntCallResourceEntry bodySim exprSimHypsDefs
  vyperContext vyperState vyperInterpreter finite_map

Theorem pinned_internal_bound_body_typing:
  body_inv tops ctx ce cx /\ ce.ce_module = NONE /\
  ce.ce_module_vars = add_immutable_locations sft tops 0
    (add_module_var_locations tops FEMPTY) /\
  stmt_state_rel ctx func ce cx st s /\ expr_sim_inv ce cx env st /\
  MEM (FunctionDecl Internal fm nr raw name args dflts ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (fm,nr,args,dflts,ret,ss) /\
  bind_arguments (get_tenv cx) args vs = SOME sc ==>
  ?env_body ret_tv env_after.
    env_body.current_src = NONE /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret ss = SOME env_after /\
    (lookup_function NONE name Internal tops <> NONE ==>
       IS_SOME (type_stmts (env_body with bare_global_assignable := FEMPTY) ret ss)) /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\ stmts_no_control_escape ss /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id ty. MEM (id,ty) args ==>
       FLOOKUP env_body.var_types id = SOME ty /\
       IS_SOME (FLOOKUP env_body.var_assignable id)) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?ty. MEM (n,ty) args) /\
    env_consistent env_body (cx with stk updated_by CONS (NONE,name))
      (st with scopes := [sc])
Proof
  strip_tac >>
  `env_consistent env cx st` by fs[expr_sim_inv_def] >>
  `IS_SOME (FLOOKUP env.fn_sigs (NONE,name))` by
    (irule body_inv_pinned_internal_signature >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule intcall_bound_body_typing >>
  goal_assum (drule_at Any) >>
  fs[expr_sim_inv_def, body_inv_def] >> metis_tac[]
QED
