(* Source and semantic projections at actual internal entry. *)
Theory bodyIntCallActualEntrySemantic
Ancestors
  bodyIntCallActualEntryFields bodyIntCallActualEntryResource bodyIntCallPrologueInit bodyIntCallSemanticEntry
  bodyIntCallResourceEntry bodySim bodySimEntry exprSimHypsDefs
  compileEnv context compileVyper moduleLowering intCallCallee
  exprLoweringProps loweringPosts allocLimitsProps fragExec
  vyperInterpreter vyperContext vyperState vyperTypeBindArguments
  finite_map list rich_list pair

Theorem internal_entry_param_ptr:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) /\ MEM n (MAP FST params) /\
  (?off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz)) ==>
  ?p sz. FLOOKUP ce2.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  strip_tac >> drule internal_entry_environment >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  drule compile_internal_param_decls_shape >> strip_tac >> gvs[] >>
  `MAP FST caps = MAP FST params` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >> simp[]) >>
  `EVERY (\c. ?p. SND (SND c) = Var p) caps` by
    (simp[EVERY_EL] >> rpt strip_tac >> simp[]) >>
  irule materialize_internal_params_ptrs >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem internal_entry_locals_declared:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) /\ ce_locals_declared ce env /\
  (!n. MEM n (MAP FST params) ==> n IN FDOM env.var_types) ==>
  ce_locals_declared (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) env
Proof
  strip_tac >> drule internal_entry_environment >> strip_tac >>
  drule internal_entry_prefix_shapes >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  gvs[] >> fs[ce_locals_declared_def] >> rpt strip_tac >>
  Cases_on `MEM n (MAP FST caps)` >- metis_tac[] >>
  gvs[]
QED

Theorem packaged_internal_entry_locals_declared:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) /\
  (!n ty. MEM (n,ty) args ==> FLOOKUP env.var_types n = SOME ty) ==>
  ce_locals_declared (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) env
Proof
  strip_tac >> irule internal_entry_locals_declared >>
  goal_assum (drule_at Any) >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  simp[cj 1 MAP_ZIP, LENGTH_compute_pass_via_stack, LENGTH_MAP] >>
  conj_tac
  >- (rpt strip_tac >> gvs[MEM_MAP, FORALL_PROD] >>
      rename1 `MEM binding args` >> PairCases_on `binding` >>
      first_x_assum drule >> simp[FLOOKUP_DEF]) >>
  simp[ce_locals_declared_def] >> rpt strip_tac >>
  drule build_compile_env_bound >> simp[MEM_MAP, FORALL_PROD] >>
  strip_tac >> rename1 `MEM binding args` >> PairCases_on `binding` >> gvs[] >>
  first_x_assum drule >> simp[FLOOKUP_DEF]
QED

Theorem packaged_internal_entry_param_type:
  supported_function_body tops Internal args ss /\ MEM (n,ty) args /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  ce2.ce_var_type n = SOME ty
Proof
  strip_tac >> drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  irule supported_build_internal_env_param_type >> metis_tac[]
QED

Theorem internal_entry_landing_rooms:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\ fn_has_code st0 st1 func /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  mat_frame st0 s0 u /\ alloca_room ctx func s0 /\ fmp_room ctx func s0 ==>
  alloca_room ctx func u /\ fmp_room ctx func u
Proof
  strip_tac >> drule compile_internal_entry_shape >> strip_tac >>
  `EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE)
    (emitted_insts st0 st1)` by
    (fs[EVERY_MEM, emitted_insts_def, DROP_LENGTH_APPEND] >>
     rpt strip_tac >> qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fragExecTheory.fn_has_code_def] >> strip_tac >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     fs[IS_PREFIX_APPEND] >> gvs[]) >>
  conj_tac
  >- (irule run_inst_seq_alloca_room >>
      qexistsl [`emitted_insts st0 st1`, `s0`] >> simp[]) >>
  irule run_inst_seq_fmp_room >>
  qexistsl [`emitted_insts st0 st1`, `s0`] >> fs[mat_frame_def] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
QED

(* Semantic bridge depends on the body's compiler fields, not on which
   entry instruction sequence establishes its local pointers. *)
Theorem packaged_internal_fields_expr_inv:
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
  env_body.current_src = NONE /\ env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  env_consistent env_body (cx with stk updated_by CONS (NONE,name))
    (st with scopes := [sc]) /\
  bind_arguments (get_tenv cx) args vs = SOME sc /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  body_ce with <|ce_vars := ce.ce_vars; ce_return_buf := ce.ce_return_buf;
    ce_return_pc := ce.ce_return_pc; ce_imm_alloca := ce.ce_imm_alloca;
    ce_alloca_locals := ce.ce_alloca_locals|> = ce /\
  (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
     ?p sz. FLOOKUP body_ce.ce_vars n = SOME (PtrVar (Var p) sz)) /\
  (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
     body_ce.ce_var_type n = SOME ty) ==>
  expr_sim_inv body_ce (cx with stk updated_by CONS (NONE,name)) env_body
    (st with scopes := [sc])
Proof
  strip_tac >> drule_all intcall_bound_source_invariants >>
  disch_then (qspec_then `name` strip_assume_tac) >>
  fs[compile_env_component_equality, expr_sim_inv_def] >>
  qpat_x_assum `body_inv tops ctx caller cx` mp_tac >>
  simp[body_inv_def] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def, build_compile_env_def, pairTheory.ELIM_UNCURRY] >>
  fs[get_module_code_def, get_tenv_def] >>
  conj_tac >- (qpat_x_assum `!n fs. FLOOKUP (make_struct_fields_map tops) n = SOME fs ==> _`
                ACCEPT_TAC) >>
  reverse conj_tac >-
    (rpt strip_tac >> qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> _`
       drule >> simp[]) >>
  irule (iffRL placeTypingPropsTheory.place_map_tables_agree_on_defined_cong) >>
  qexistsl [`caller`, `env`] >> simp[]
QED

Theorem packaged_internal_entry_locals_alloc_ok:
  fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,ss) /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) ==>
  locals_alloc_ok (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) env
Proof
  strip_tac >> drule_all packaged_internal_entry_alloc_env_agree >>
  strip_tac >> drule_all fn_allocs_ok_body >> strip_tac >>
  irule locals_alloc_ok_params >> goal_assum (drule_at Any) >> simp[]
QED

Theorem packaged_internal_entry_param_ptr:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) /\ MEM (n,ty) args ==>
  ?p sz. FLOOKUP ce2.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  strip_tac >> irule internal_entry_param_ptr >>
  goal_assum (drule_at Any) >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  conj_tac >-
    (irule (cj 1 build_compile_env_vars) >>
     simp[MEM_MAP] >> qexists `(n,ty)` >> simp[]) >>
  simp[cj 1 MAP_ZIP, LENGTH_compute_pass_via_stack, LENGTH_MAP] >>
  simp[MEM_MAP] >> qexists `(n,ty)` >> simp[]
QED

Theorem packaged_internal_entry_expr_inv:
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
  env_consistent env_body (cx with stk updated_by CONS (NONE,name))
    (st with scopes := [sc]) /\
  bind_arguments (get_tenv cx) args vs = SOME sc /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  expr_sim_inv (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    (cx with stk updated_by CONS (NONE,name)) env_body (st with scopes := [sc])
Proof
  strip_tac >>
  `!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
    ?p sz. FLOOKUP ce2.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt strip_tac >> irule packaged_internal_entry_param_ptr >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!n ty. FLOOKUP env_body.var_types n = SOME ty ==> ce2.ce_var_type n = SOME ty` by
    (rpt strip_tac >> irule packaged_internal_entry_param_type >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  irule packaged_internal_fields_expr_inv >>
  qpat_assum `set_internal_package_target _ _ = _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists `ctx` >> simp[compile_env_component_equality] >> gvs[]
QED
