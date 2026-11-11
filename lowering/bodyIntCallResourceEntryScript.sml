(* Packaged internal entry transfer; source typing is kept independent of
   compiler local-map construction. *)
Theory bodyIntCallResourceEntry
Ancestors
  bodySim bodySimEntry compileEnv loweringStateRelDefs intCallCallee compileVyper
  bodyIntCallResourceAllocation
  vyperInterpreter vyperContext vyperState list finite_map
  vyperTypeEvalSoundness vyperTypeBindArguments vyperTypeInvariants
  vyperTypeContract exprLoweringProps

Theorem body_inv_push_stack:
  body_inv tops ctx cenv cx ==>
  body_inv tops ctx cenv (cx with stk updated_by CONS src_fn)
Proof
  simp[body_inv_def, get_module_code_def, get_tenv_def]
QED

Theorem body_inv_push_function:
  body_inv tops ctx cenv cx /\
  push_function src_fn sc cx st = (INL cxf,st') ==>
  body_inv tops ctx cenv cxf
Proof
  simp[push_function_def, return_def] >> strip_tac >>
  gvs[] >> irule body_inv_push_stack >> simp[]
QED

Theorem body_inv_internal_prologue:
  body_inv tops ctx cenv cx /\
  compile_internal_prologue cenv params has_rb rt st0 = ((ce,pc),st1) ==>
  body_inv tops ctx (ce with ce_alloca_locals := T) cx
Proof
  strip_tac >> drule_all compile_internal_prologue_body_inv >>
  strip_tac >> fs[body_inv_def] >> metis_tac[]
QED

Theorem body_inv_packaged_internal_entry:
  body_inv tops ctx caller cx /\ target = caller.ce_target /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys caller.ce_is_ctor 0
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,pc),st1) /\
  push_function src_fn sc cx es = (INL cxf,es') ==>
  body_inv tops ctx (ce2 with ce_alloca_locals := T) cxf
Proof
  strip_tac >> drule_all body_inv_push_function >> strip_tac >>
  `body_inv tops ctx
     (build_compile_env tops Internal mut name args ret ss use_trans
        with <| ce_target := caller.ce_target;
                ce_is_ctor := caller.ce_is_ctor |>) cxf` by
    (irule body_inv_build_internal_env >> goal_assum drule) >>
  irule body_inv_internal_prologue >> goal_assum drule >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def, body_inv_def] >> metis_tac[]
QED

Theorem bind_arguments_pushed_env_consistent:
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\
  functions_well_typed cx /\
  env_body.current_src = src /\ env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  (!id ty. MEM (id,ty) args ==>
    FLOOKUP env_body.var_types id = SOME ty /\
    IS_SOME (FLOOKUP env_body.var_assignable id)) /\
  (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
  (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
    ?ty. MEM (n,ty) args) /\
  bind_arguments (get_tenv cx) args vs = SOME sc ==>
  env_consistent env_body (cx with stk updated_by CONS (src,fn))
    (st with scopes := [sc])
Proof
  rpt strip_tac >> drule_all intcall_default_env_side_conditions >>
  disch_then (qspec_then `fn` strip_assume_tac) >>
  simp[env_consistent_def] >> conj_tac
  >- (irule bind_arguments_env_scopes_consistent >>
      qexistsl_tac [`args`, `get_tenv cx`, `vs`] >>
      simp[get_tenv_def] >> metis_tac[]) >>
  qpat_x_assum `env_immutables_consistent _ _ _` mp_tac >>
  simp[env_immutables_consistent_def] >> metis_tac[]
QED

Theorem intcall_bound_body_typing:
  functions_well_typed cx /\ env_consistent env cx st /\
  state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\
  IS_SOME (FLOOKUP env.fn_sigs (src,fn)) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,ss) /\
  bind_arguments (get_tenv cx) args vs = SOME sc ==>
  ?env_body ret_tv env_after.
    env_body.current_src = src /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret ss = SOME env_after /\
    (lookup_function NONE fn Internal ts <> NONE ==>
       IS_SOME (type_stmts (env_body with bare_global_assignable := FEMPTY) ret ss)) /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\ stmts_no_control_escape ss /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id ty. MEM (id,ty) args ==>
       FLOOKUP env_body.var_types id = SOME ty /\
       IS_SOME (FLOOKUP env_body.var_assignable id)) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?ty. MEM (n,ty) args) /\
    env_consistent env_body (cx with stk updated_by CONS (src,fn))
      (st with scopes := [sc])
Proof
  strip_tac >> drule_all callable_body_typing_from_env_consistent >> strip_tac >>
  `env_consistent env_body (cx with stk updated_by CONS (src,fn))
     (st with scopes := [sc])` by
    (irule bind_arguments_pushed_env_consistent >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`args`, `vs`] >> simp[] >> metis_tac[]) >>
     qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`env_body`, `ret_tv`, `env_after`] >> simp[] >>
  metis_tac[]
QED

(* Allocation makes all declarations of a loaded module live, independently
   of the syntactic call-closure roots. *)
Theorem allocated_module_context_function_live:
  get_module_code cx src = SOME tops /\
  module_allocated cx.layouts cx.txn.target src tops ==>
  context_function_live cx (src,name)
Proof
  simp[get_module_code_def, context_function_live_def] >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >> simp[] >>
  strip_tac >> simp[function_live_def]
QED

Theorem allocated_module_declared_signature:
  env_context_consistent env cx /\
  get_module_code cx src = SOME tops /\
  module_allocated cx.layouts cx.txn.target src tops /\
  MEM (FunctionDecl vis fm nr raw name args dflts ret ss) tops /\
  (vis = Internal \/ (cx.in_deploy /\ vis = Deploy)) /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (fm,nr,args,dflts,ret,ss) ==>
  FLOOKUP env.fn_sigs (src,name) =
    SOME <| param_types := MAP SND args; num_defaults := LENGTH dflts;
            ret_ty := ret |>
Proof
  strip_tac >>
  `context_function_live cx (src,name)` by
    (drule_all allocated_module_context_function_live >> simp[]) >>
  gvs[] >> fs[env_context_consistent_def, fn_sigs_declared_complete_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The two module pins are explicit: no held module-pins admission is used. *)
Theorem body_inv_pinned_internal_signature:
  body_inv tops ctx ce cx /\
  ce.ce_module = NONE /\
  ce.ce_module_vars = add_immutable_locations sft tops 0
    (add_module_var_locations tops FEMPTY) /\
  stmt_state_rel ctx func ce cx es s /\ env_consistent env cx es /\
  MEM (FunctionDecl Internal fm nr raw name args dflts ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (fm,nr,args,dflts,ret,ss) ==>
  IS_SOME (FLOOKUP env.fn_sigs (NONE,name))
Proof
  strip_tac >>
  `module_allocated cx.layouts cx.txn.target NONE tops` by
    (irule pinned_module_allocated >>
     fs[body_inv_def, stmt_state_rel_def, state_rel_def] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `sft` >> simp[]) >>
  drule_at (Pat `MEM _ _`) allocated_module_declared_signature >>
  fs[body_inv_def, env_consistent_def] >>
  disch_then (qspecl_then [`NONE`, `env`, `cx`] mp_tac) >> simp[]
QED
