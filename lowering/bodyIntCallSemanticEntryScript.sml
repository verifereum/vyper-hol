(* Source and compiler projections at the packaged body's entry. *)
Theory bodyIntCallSemanticEntry
Ancestors
  bodyIntCallResourceEntry bodySimEntry bodySim exprSimHypsDefs
  compileVyper compileEnv moduleLowering intCallCallee
  supportedProgram supportedStmtTraverse supportedNames
  vyperInterpreter vyperState vyperContext vyperTypeBindArguments
  vyperTypeInvariants vyperTypeStoragePreservation vyperTypeEvalStoragePreservation
  vyperStorageLayoutSafety vyperLookupStorage vyperStorageBackend
  list alist finite_map pair

Theorem locals_alloc_ok_params:
  EVERY (\(_,ty). type_memory_bytes cenv ty < 2 ** 64) params /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) params) ==>
  locals_alloc_ok cenv env
Proof
  simp[locals_alloc_ok_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem bind_arguments_state_well_typed:
  state_well_typed st /\ bind_arguments tenv args vs = SOME sc ==>
  state_well_typed (st with scopes := [sc])
Proof
  strip_tac >> drule bind_arguments_scope_well_typed_from_success >>
  gvs[state_well_typed_def]
QED

Theorem bind_arguments_popped_empty:
  !tenv args vs sc n entry.
    bind_arguments tenv args vs = SOME sc /\ FLOOKUP sc n = SOME entry ==>
    entry.popped = []
Proof
  Induct_on `args` >-
    (Cases_on `vs` >> simp[bind_arguments_def, FLOOKUP_DEF]) >>
  Cases >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  rename1 `FLOOKUP sc n = SOME entry` >>
  metis_tac[]
QED

Theorem bind_arguments_popped_keys_indexed:
  bind_arguments tenv args vs = SOME sc ==> popped_keys_indexed [sc]
Proof
  simp[popped_keys_indexed_def] >> rpt strip_tac >>
  drule_all bind_arguments_popped_empty >> simp[]
QED

Theorem intcall_entry_storage:
  (contract_storage_well_formed (cx with stk updated_by f)
     (st with scopes := scopes) <=> contract_storage_well_formed cx st) /\
  (oracle_storage_ok (cx with stk updated_by f) (st with scopes := scopes) <=>
     oracle_storage_ok cx st)
Proof
  conj_tac
  >- simp[contract_storage_well_formed_def, well_formed_storage_def,
          storage_var_in_range_def, get_storage_backend_eq, oneline get_storage_def] >>
  simp[oracle_storage_ok_outcomes]
QED

(* Materialization's public shape theorem confines all changes to ce_vars. *)
Theorem compile_internal_prologue_fields:
  compile_internal_prologue cenv params has_rb ret st = ((cenv',pc),st') ==>
  cenv' with <| ce_vars := cenv.ce_vars;
                ce_return_buf := cenv.ce_return_buf;
                ce_return_pc := cenv.ce_return_pc |> = cenv
Proof
  strip_tac >> drule internal_prologue_stages >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >>
  strip_tac >> gvs[] >> simp[compile_env_component_equality]
QED

Theorem internal_param_type_lookup:
  ALL_DISTINCT (MAP FST args) /\
  (!n ty. MEM (n,ty) args ==> ~MEM n (MAP FST (collect_locals ss))) /\
  MEM (n,ty) args ==>
  ALOOKUP (REVERSE (args ++ collect_locals ss)) n = SOME ty
Proof
  strip_tac >> simp[REVERSE_APPEND, ALOOKUP_APPEND] >>
  `ALOOKUP (REVERSE (collect_locals ss)) n = NONE` by
    (simp[ALOOKUP_NONE, MAP_REVERSE] >> metis_tac[]) >>
  simp[] >> irule ALOOKUP_ALL_DISTINCT_MEM >>
  simp[MAP_REVERSE, ALL_DISTINCT_REVERSE]
QED

Theorem collect_locals_supported_bindings:
  !ss. MEM p (collect_locals ss) <=>
       MEM p (supported_stmts_bindings T ss) \/
       MEM p (supported_stmts_bindings F ss)
Proof
  recInduct collect_locals_ind >>
  simp[collect_locals_def, supported_stmt_bindings_def] >> metis_tac[]
QED

Theorem supported_body_param_separation:
  supported_function_body tops vis args ss ==>
  ALL_DISTINCT (MAP FST args) /\
  (!n ty. MEM (n,ty) args ==> ~MEM n (MAP FST (collect_locals ss)))
Proof
  simp[supported_function_body_def, supported_function_bindings_def,
       ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  gvs[MEM_MAP] >>
  drule (iffLR collect_locals_supported_bindings) >> strip_tac >>
  metis_tac[MEM_MAP, FST]
QED

Theorem supported_build_internal_env_param_type:
  supported_function_body tops vis args ss /\ MEM (n,ty) args ==>
  (build_compile_env tops Internal mut name args ret ss use_trans).ce_var_type n =
    SOME ty
Proof
  strip_tac >> drule supported_body_param_separation >> strip_tac >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  irule internal_param_type_lookup >> metis_tac[]
QED

(* Applies uniformly to runtime and deployment packages and arbitrary targets. *)
Theorem packaged_internal_prologue_param_type:
  supported_function_body tops Internal args ss /\ MEM (n,ty) args /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_prologue ce params has_rb rt st = ((cenv',pc),st') ==>
  cenv'.ce_var_type n = SOME ty
Proof
  strip_tac >> drule compile_internal_prologue_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  irule supported_build_internal_env_param_type >> metis_tac[]
QED

(* Source hypotheses not carried by the compiler prologue. The environment
   projections here are exactly the public source-typing interface. *)
Theorem intcall_bound_source_invariants:
  expr_sim_inv caller cx env (st with scopes := prev) /\
  env_body.current_src = src /\ env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  bind_arguments (get_tenv cx) args vs = SOME sc ==>
  state_well_typed (st with scopes := [sc]) /\
  accounts_well_typed st.accounts /\
  context_well_typed (cx with stk updated_by CONS (src,name)) /\
  functions_well_typed (cx with stk updated_by CONS (src,name)) /\
  outcomes_accounts_typed st.outcomes /\ IS_SOME st.outcomes /\
  contract_storage_well_formed (cx with stk updated_by CONS (src,name))
    (st with scopes := [sc]) /\
  storage_layout_safe (cx with stk updated_by CONS (src,name)) /\
  oracle_storage_ok (cx with stk updated_by CONS (src,name))
    (st with scopes := [sc]) /\
  popped_keys_indexed [sc]
Proof
  strip_tac >>
  `context_well_typed (cx with stk updated_by CONS (src,name)) /\
   functions_well_typed (cx with stk updated_by CONS (src,name))` by
    (drule_at (Pat `env_body.current_src = _`)
       vyperTypeEvalSoundnessTheory.intcall_default_env_side_conditions >>
     fs[expr_sim_inv_def] >>
     disch_then (qspecl_then [`env`, `cx`, `st with scopes := prev`, `name`] mp_tac) >>
     simp[]) >>
  `state_well_typed (st with scopes := [sc])` by
    (drule bind_arguments_scope_well_typed_from_success >>
     fs[expr_sim_inv_def, state_well_typed_def]) >>
  drule bind_arguments_popped_keys_indexed >>
  fs[expr_sim_inv_def, intcall_entry_storage,
     contract_storage_well_formed_def, well_formed_storage_def,
     storage_var_in_range_def, get_storage_backend_eq, oneline get_storage_def,
     oracle_storage_ok_payload] >> metis_tac[]
QED

(* General prologue interface, independent of package target overrides. *)
Theorem internal_prologue_param_ptr:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,pc),st1) /\
  MEM n (MAP FST params) /\
  (?off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz)) ==>
  ?p sz. FLOOKUP ce2.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  strip_tac >> drule internal_prologue_stages >> strip_tac >>
  drule compile_internal_param_decls_shape >> strip_tac >>
  gvs[] >>
  `MAP FST caps = MAP FST params` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >> simp[]) >>
  `EVERY (\c. ?p. SND (SND c) = Var p) caps` by
    (simp[EVERY_EL] >> rpt strip_tac >> simp[]) >>
  irule materialize_internal_params_ptrs >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem packaged_internal_body_expr_inv:
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
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,pc),st1) ==>
  expr_sim_inv (ce2 with ce_alloca_locals := T)
    (cx with stk updated_by CONS (NONE,name)) env_body (st with scopes := [sc])
Proof
  strip_tac >>
  `!n ty. FLOOKUP env_body.var_types n = SOME ty ==> ce2.ce_var_type n = SOME ty` by
    (rpt strip_tac >> irule packaged_internal_prologue_param_type >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all intcall_bound_source_invariants >>
  disch_then (qspec_then `name` strip_assume_tac) >>
  drule compile_internal_prologue_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  `!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
     ?p sz. FLOOKUP ce2.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt strip_tac >> irule internal_prologue_param_ptr >>
     goal_assum (drule_at Any) >>
     gvs[package_internal_fn_def, set_internal_package_target_def,
         update_cenv_nonreentrant_def] >>
     conj_tac >-
       (irule (cj 1 build_compile_env_vars) >>
        simp[MEM_MAP] >> qexists `(n,ty)` >> simp[]) >>
     simp[cj 1 MAP_ZIP, LENGTH_compute_pass_via_stack, LENGTH_MAP] >>
     simp[MEM_MAP] >>
     qexists `(n,ty)` >> simp[]) >>
  fs[expr_sim_inv_def] >>
  qpat_x_assum `body_inv tops ctx caller cx` mp_tac >>
  simp[body_inv_def] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def, build_compile_env_def, ELIM_UNCURRY] >>
  fs[get_module_code_def, get_tenv_def] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (rpt strip_tac >>
       qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> _`
         drule >> simp[] >> NO_TAC)
  >~ [`bare_globals_layout`]
  >- (qpat_x_assum `bare_globals_layout _ _ _ _ _ _` mp_tac >>
      fs[bare_globals_layout_def]) >>
  irule (iffRL placeTypingPropsTheory.place_map_tables_agree_on_defined_cong) >>
  qexistsl [`caller`, `env`] >> simp[]
QED

Theorem internal_prologue_locals_declared:
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,pc),st1) /\
  ce_locals_declared ce env /\
  (!n. MEM n (MAP FST params) ==> n IN FDOM env.var_types) ==>
  ce_locals_declared (ce2 with ce_alloca_locals := T) env
Proof
  strip_tac >> drule internal_prologue_stages >> strip_tac >>
  drule compile_internal_param_decls_shape >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  gvs[] >>
  `MAP FST caps = MAP FST params` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >> simp[]) >>
  fs[ce_locals_declared_def] >> rpt strip_tac >>
  Cases_on `MEM n (MAP FST params)` >- simp[] >>
  qpat_x_assum `!n. ~MEM n (MAP FST params) ==> _` drule >>
  simp[] >> strip_tac >>
  qpat_x_assum `!n l. FLOOKUP ce.ce_vars n = SOME l ==> _` irule >>
  qexists `l` >> simp[]
QED

Theorem packaged_internal_body_locals_declared:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,pc),st1) /\
  (!n ty. MEM (n,ty) args ==> FLOOKUP env.var_types n = SOME ty) ==>
  ce_locals_declared (ce2 with ce_alloca_locals := T) env
Proof
  strip_tac >> irule internal_prologue_locals_declared >>
  goal_assum (drule_at Any) >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  simp[cj 1 MAP_ZIP, LENGTH_compute_pass_via_stack, LENGTH_MAP] >>
  conj_tac >-
    (rpt strip_tac >> gvs[MEM_MAP, FORALL_PROD] >>
     rename1 `MEM binding args` >> PairCases_on `binding` >> first_x_assum drule >> simp[FLOOKUP_DEF]) >>
  simp[ce_locals_declared_def] >> rpt strip_tac >>
  drule build_compile_env_bound >> simp[MEM_MAP, FORALL_PROD] >>
  strip_tac >> rename1 `MEM binding args` >> PairCases_on `binding` >> gvs[] >>
  first_x_assum drule >> simp[FLOOKUP_DEF]
QED
