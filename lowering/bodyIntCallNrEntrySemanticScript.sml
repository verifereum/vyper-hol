(* Source resources of the actual internal package, before taking its guard. *)
Theory bodyIntCallNrEntrySemantic
Ancestors
  bodyIntCallSeamDefs bodyIntCallNrSemantic bodyIntCallPackageRootSemantic
  supportedProgram exprSimHypsDefs bodyIntCallProducerSemantic
  bodyIntCallActualEntryFields
  bodyIntCallPackageProducerEntry bodyIntCallEntryInputs bodyIntCallJointInputs
  bodyIntCallPackageBounds bodyIntCallPackageRootResource
  calleeTransport intCallCallee vyperTypeCallGraph vyperContext
  bodySim compileVyper moduleLowering compileEnv vyperState

Theorem intcall_entry_semantic_inputs_nr:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t ==>
  call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
    (int_calls_stmts ss) /\
  es1.scopes = [penv] /\
  gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es1 /\
  stmt_state_rel ctx func cenv cx (es1 with scopes := prev) t /\
  expr_sim_inv cenv cx tenv (es1 with scopes := prev)
Proof
  simp[intcall_entry_def] >> rpt strip_tac >> simp[]
QED

Theorem intcall_entry_root_expr_inv_nr:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  env_body.current_src = NONE /\ env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = tenv.fn_sigs /\ env_body.bare_globals = tenv.bare_globals /\
  env_body.bare_global_assignable = tenv.bare_global_assignable /\
  env_body.toplevel_vtypes = tenv.toplevel_vtypes /\
  env_body.flag_members = tenv.flag_members /\
  (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
  env_consistent env_body (cx with stk updated_by CONS (NONE,name)) es1 /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,nr,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor ilen' rt entry =
    ((ce2,pc,imm),body_start) ==>
  expr_sim_inv (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    (cx with stk updated_by CONS (NONE,name)) env_body es1
Proof
  strip_tac >>
  `supported_function_body tops Internal args ss` by
    (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)
       supported_program_function >> fs[body_inv_def]) >>
  drule intcall_entry_semantic_inputs_nr >> strip_tac >>
  drule intcall_entry_source >> strip_tac >>
  qhdtm_assum `cenv_module_pins`
    (strip_assume_tac o REWRITE_RULE [cenv_module_pins_def]) >>
  `cenv.ce_is_ctor <=> cx.in_deploy` by fs[body_inv_def] >>
  drule_all packaged_internal_entry_expr_inv_scopes >> simp[]
QED

Theorem intcall_entry_producer_semantics_nr:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,nr,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor ilen' rt entry =
    ((ce2,rpc,imm),body_start) ==>
  ?env env_after bindings.
    env.current_src = NONE /\ env.type_defs = get_tenv cx /\
    env.fn_sigs = tenv.fn_sigs /\ env.bare_globals = tenv.bare_globals /\
    env.bare_global_assignable = tenv.bare_global_assignable /\
    env.toplevel_vtypes = tenv.toplevel_vtypes /\ env.flag_members = tenv.flag_members /\
    (!n ty. MEM (n,ty) args ==> FLOOKUP env.var_types n = SOME ty) /\
    (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
    env_consistent env (cx with stk updated_by CONS (NONE,name)) es1 /\
    body_inv tops ctx (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      (cx with stk updated_by CONS (NONE,name)) /\
    supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
      occurs_abi_decode_target target tops) /\
    type_stmts env ret ss = SOME env_after /\
    IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY) ret ss) /\
    stmts_exprs_ok (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) ss /\
    calls_follow_call_graph E (NONE,name) (int_calls_stmts ss) /\
    (!locked. lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) ==>
      gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
        (stmt_res_ok NoLoop) locked) /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\
    expr_sim_inv (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      (cx with stk updated_by CONS (NONE,name)) env es1
Proof
  strip_tac >> drule_all intcall_entry_body_typing_nr >> strip_tac >>
  drule_all body_inv_packaged_actual_entry >>
  disch_then (qspec_then `(NONE,name)` assume_tac) >>
  drule_all packaged_internal_entry_alloc_env_agree >> strip_tac >>
  drule_all body_inv_internal_allocs_ok >> strip_tac >>
  `~(ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).ce_is_external` by
    (drule compile_internal_entry_fields >>
     simp[compile_env_component_equality] >> strip_tac >>
     gvs[package_internal_fn_def, set_internal_package_target_def,
         update_cenv_nonreentrant_def, build_compile_env_def, pairTheory.ELIM_UNCURRY]) >>
  drule_all internal_body_traversal_bounds >> strip_tac >>
  `supported_function_body tops Internal args ss` by
    (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)
       supported_program_function >> fs[body_inv_def]) >>
  `get_module_code (cx with stk updated_by CONS (NONE,name)) NONE = SOME tops` by
    fs[body_inv_def, get_module_code_def] >>
  `calls_follow_call_graph E (NONE,name) (int_calls_stmts ss)` by
    (drule callable_body_follows_graph >> simp[]) >>
  drule declared_body_abi_targets >> strip_tac >>
  drule_all intcall_entry_root_expr_inv_nr >> strip_tac >>
  `!locked. lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) ==>
      gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
        (stmt_res_ok NoLoop) locked` by
    (rpt strip_tac >> drule intcall_entry_semantic_inputs_nr >> strip_tac >>
     drule_all intcall_rest_stmts_admissible_locked >> simp[]) >>
  qexistsl [`env_body`, `env_after`,
    `args ++ supported_stmts_bindings T ss ++ supported_stmts_bindings F ss`] >>
  fs[supported_function_body_def]
QED
