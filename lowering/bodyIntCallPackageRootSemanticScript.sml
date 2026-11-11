(* Semantic resources of the actual root, from the frozen call boundary. *)
Theory bodyIntCallPackageRootSemantic
Ancestors
  bodyIntCallPackageSemantic bodyIntCallActualEntrySemantic
  bodyIntCallEntryInputs bodyIntCallSeamDefs bodyIntCallJointContract supportedProgram bodySim
  compileVyper moduleLowering compileEnv vyperState

Theorem packaged_internal_entry_expr_inv_scopes:
  body_inv tops ctx caller cx /\
  caller.ce_module = NONE /\
  caller.ce_module_var_type = build_var_type_map tops /\
  caller.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
  caller.ce_flag_member_id = FST (build_flag_info tops (K (K 0)) (K 0)) /\
  caller.ce_flag_n_members = SND (build_flag_info tops (K (K 0)) (K 0)) /\
  caller.ce_method_id = (\s tys. w2n (calldata_method_id
    (function_selector s (vyper_to_abi_types (type_env tops) tys)))) /\
  expr_sim_inv caller cx env (st with scopes := prev) /\
  supported_function_body tops Internal args ss /\
  env_body.current_src = NONE /\ env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
  env_consistent env_body (cx with stk updated_by CONS (NONE,name)) st /\
  st.scopes = [sc] /\
  bind_arguments (get_tenv cx) args vs = SOME sc /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  expr_sim_inv (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    (cx with stk updated_by CONS (NONE,name)) env_body st
Proof
  strip_tac >>
  `st with scopes := [sc] = st` by simp[evaluation_state_component_equality] >>
  qpat_assum `st with scopes := [sc] = st`
    (fn th => drule_all (REWRITE_RULE [th]
      (Q.INST [`st` |-> `st`, `sc` |-> `sc`] packaged_internal_entry_expr_inv))) >>
  simp[]
QED

Theorem intcall_entry_root_expr_inv:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  env_body.current_src = NONE /\ env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = tenv.fn_sigs /\ env_body.bare_globals = tenv.bare_globals /\
  env_body.bare_global_assignable = tenv.bare_global_assignable /\
  env_body.toplevel_vtypes = tenv.toplevel_vtypes /\
  env_body.flag_members = tenv.flag_members /\
  (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
  env_consistent env_body (cx with stk updated_by CONS (NONE,name)) es1 /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([]:expr list),ret,ss)) =
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
  drule intcall_entry_semantic_inputs >> strip_tac >>
  drule intcall_entry_source >> strip_tac >>
  qhdtm_assum `cenv_module_pins`
    (strip_assume_tac o REWRITE_RULE [cenv_module_pins_def]) >>
  drule_all packaged_internal_entry_expr_inv_scopes >> simp[]
QED
