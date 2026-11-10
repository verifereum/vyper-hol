(* Semantic premises at the actual internal body entry. *)
Theory bodyIntCallPackageProducerEntry
Ancestors
  bodyIntCallPackageRootSemantic bodyIntCallSourceJointInit
  bodyIntCallResourceNormalize calleeTransport intCallCallee
  bodyIntCallPackageBounds bodyIntCallPackageRun
  bodyIntCallPackageSemantic bodyIntCallProducerSemantic bodyIntCallPackageRoot
  bodyIntCallActualEntryFields supportedProgram bodySim compileEnv
  bodyIntCallJointInputs vyperTypeCallGraph vyperContext compileVyper moduleLowering

Theorem intcall_entry_producer_semantics:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,F,args,[],ret,ss) /\
  functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([]:expr list),ret,ss)) =
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
    EVERY (stmt_exprs_ok (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)) ss /\
    calls_follow_call_graph E (NONE,name) (int_calls_stmts ss) /\
    gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
      (stmt_res_ok NoLoop) es1 /\
    (ret = NoneT \/ stmts_no_fallthrough ss)
Proof
  strip_tac >> drule_all intcall_entry_body_typing >> strip_tac >>
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
  `gas_admissible (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
      (stmt_res_ok NoLoop) es1` by
    (drule bodyIntCallEntryInputsTheory.intcall_entry_semantic_inputs >> strip_tac >>
     drule intcall_rest_stmts_admissible >> simp[]) >>
  qexistsl [`env_body`, `env_after`,
    `args ++ supported_stmts_bindings T ss ++ supported_stmts_bindings F ss`] >>
  fs[supported_function_body_def]
QED

Theorem intcall_entry_producer_resources:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,F,args,[],ret,ss) /\
  functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME entered /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor ilen' rt entry =
    ((ce2,rpc,imm),body_start) /\
  fn_has_code entry body_start callee /\ fn_inst_ids_distinct callee /\
  run_inst_seq (emitted_insts entry body_start) entered = OK u /\
  (!a k. P a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint a k off asz) /\
  (!b z. staged b z <=> ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) /\
  intcall_frame_ok fp /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
  fp.jc_cx = (cx with stk updated_by CONS (NONE,name)) /\
  fp.jc_root_ce = (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
  fp.jc_oorig = u /\ fp.jc_morig = t /\ fp.jc_lo = t.vs_alloca_next /\
  fp.jc_prot = P /\ fp.jc_staged = staged /\
  fp.jc_rb = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
  (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at body_start x) ==>
  ?env env_after bindings.
    body_inv tops ctx fp.jc_root_ce fp.jc_cx /\
    supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
      occurs_abi_decode_target target tops) /\
    type_stmts env ret ss = SOME env_after /\
    IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY) ret ss) /\
    EVERY (stmt_exprs_ok fp.jc_root_ce) ss /\
    calls_follow_call_graph E (NONE,name) (int_calls_stmts ss) /\
    gas_admissible (eval_stmts fp.jc_cx ss) (stmt_res_ok NoLoop) es1 /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\
    intcall_joint_res fp fp.jc_root_ce env es1 body_start
      (u with vs_inst_idx := LENGTH body_start.cs_current_insts)
Proof
  strip_tac >> drule_all intcall_entry_producer_semantics >>
  disch_then (qx_choose_then `env` (qx_choose_then `env_after`
    (qx_choose_then `bindings` (fn th => map_every assume_tac (CONJUNCTS th))))) >>
  drule_all bodyIntCallPackageInputsTheory.intcall_entry_package_inputs >> strip_tac >>
  drule_all bodyIntCallPackageInputsTheory.intcall_entry_package_separation >> strip_tac >>
  drule_all bodyIntCallPackageGeometryTheory.intcall_entry_root_geometry >> strip_tac >>
  drule_all bodyIntCallPackageRootResourceTheory.packaged_internal_entry_return_fields >> strip_tac >>
  drule_all intcall_entry_root_expr_inv >> strip_tac >>
  drule_all bodyIntCallActualEntrySemanticTheory.packaged_internal_entry_locals_declared >> strip_tac >>
  drule_all body_inv_internal_allocs_ok >> strip_tac >>
  drule_all bodyIntCallActualEntrySemanticTheory.packaged_internal_entry_locals_alloc_ok >> strip_tac >>
  `supported_function_body tops Internal args ss` by
    (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)
       supported_program_function >> fs[body_inv_def]) >>
  drule_all bodyIntCallPackageRootResourceTheory.packaged_internal_entry_reserved >> strip_tac >>
  `es1 with scopes := [penv] = es1` by
    (drule bodyIntCallEntryInputsTheory.intcall_entry_semantic_inputs >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  drule internal_parameter_staged_containment >> strip_tac >>
  `!w cap. fp.jc_rb = SOME (w,cap) /\ fp.jc_root_ce.ce_is_ctor ==>
    !nm tv iv io.
    FLOOKUP fp.jc_root_ce.ce_module_vars (fp.jc_root_ce.ce_module,nm) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables fp.jc_root_ce.ce_module imms) nm = SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n w) cap` by
    (qpat_assum `compile_internal_function_entry _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `fp.jc_root_ce = _` mp_tac >>
     qpat_assum `fp.jc_rb = _` mp_tac >>
     qpat_assum `has_rb /\ ce.ce_is_ctor ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >> drule_all internal_entry_root_buffer_separation >> simp[]) >>
  `state_rel func ce (cx with stk updated_by CONS (NONE,name))
     (es1 with scopes := []) t` by
    asm_rewrite_tac[bodyIntCallPackageRootResourceTheory.state_rel_call_stack] >>
  `internal_immutable_regions ce (cx with stk updated_by CONS (NONE,name))
     es1 t.vs_alloca_next` by asm_rewrite_tac[internal_immutable_regions_stack_update] >>
  `expr_sim_inv fp.jc_root_ce fp.jc_cx env (es1 with scopes := [penv])` by
    asm_rewrite_tac[] >>
  `ce_locals_declared fp.jc_root_ce env /\ locals_alloc_ok fp.jc_root_ce env /\
    local_ptrs_reserved fp.jc_root_ce body_start` by asm_rewrite_tac[] >>
  `!a k. P a k ==> mem_bytes_at a k entered.vs_memory = mem_bytes_at a k t.vs_memory` by
    (drule setup_callee_shared_fields >> simp[]) >>
  `has_rb ==> (?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
    w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next` by
    (strip_tac >> simp[]) >>
  `intcall_joint_res fp fp.jc_root_ce env es1 body_start
     (u with vs_inst_idx := LENGTH body_start.cs_current_insts)` by
    suspend "joint_init" >>
  qexistsl [`env`, `env_after`, `bindings`] >> asm_rewrite_tac[]
QED

Resume intcall_entry_producer_resources[joint_init]:
  irule internal_entry_source_joint_res_init >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `fp.jc_cx = _`)) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `fp.jc_rb = _`)) >>
  goal_assum (drule_at (Pat `state_rel _ _ _ _ _`)) >>
  qexists `P` >>
  qexists `ctx` >> qexists `t` >> qexists `penv` >> qexists `staged` >>
  conj_tac >- (qpat_assum `es1 with scopes := [penv] = es1` ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[evaluation_context_accfupds] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Finalise intcall_entry_producer_resources
