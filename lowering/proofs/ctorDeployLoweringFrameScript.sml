(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringFrame
Ancestors
  ctorDeployLoweringDefs ctorDeployImmBudget o1PassContract bodySim e2eDefs callTrace
  ctorDeployLoweringFramePayload ctorDeployDefs e2eDeployDefs e2eEntry
  vyperTypeStoragePreservation list supportedDecls supportedProgram
  compileEnv compileVyper moduleLowering entryLocals ctorEntryLocals bodySimEntry
  exprLoweringProps context finite_map stmtLoweringMono freshWrites fragExec vyperScopePreservation
  vyperPlaceInvariants vyperInterpreter vyperState vyperMisc
  vyperTypeDeploymentMachine vyperTypeBindArguments vyperTypeInvariants
  vyperTypeContract vyperContext vyperTypeInitialState vyperTypeContractFunction
  vyperTypeDeploymentSoundness vyperTypeContractSoundness
  vyperTypeContractStaticMaps vyperTypeEvalStoragePreservation
  typedCopyProducer typedCopyMetadata vyperTypeContractContext
  placeTypingBuildProps structFieldsProps pair allocLimitsProps alist
  ctorDeployLoweringFrameStmtWidths ctorDeployLoweringFrameSupport vyperTypeSystem
  bodyExprPreFacts immutableLocationProps entryStateRel
Libs
  monadsyntax

Theorem deploy_frame_supported_constructor_nr[local]:
  !tops env fname mut nr args dflts ret body.
    EVERY (supported_declaration_header env) tops /\
    lookup_function NONE fname Deploy tops =
      SOME (mut,nr,args,dflts,ret,body) ==> ~nr
Proof
  Induct_on `tops` >> simp[vyperInterpreterTheory.lookup_function_def] >>
  Cases_on `h` >>
  simp[supported_declaration_headers_def, supported_declaration_header_def,
       vyperInterpreterTheory.lookup_function_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
  >~ [`lookup_function _ _ _ (VariableDecl vis _ _ _ _ :: _) = _`]
  >- (Cases_on `vis` >> gvs[vyperInterpreterTheory.lookup_function_def] >> metis_tac[])
  >~ [`lookup_function _ _ _ (HashMapDecl vis _ _ _ _ _ :: _) = _`]
  >- (Cases_on `vis` >> gvs[vyperInterpreterTheory.lookup_function_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem deploy_ctor_not_nonreentrant:
  deploy_source_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==> ~nr
Proof
  pure_rewrite_tac[deploy_source_ok_def, deploy_ctor_start_def] >>
  strip_tac >> irule deploy_frame_supported_constructor_nr >>
  goal_assum (drule_at Any) >>
  gvs[supported_program_def, supported_declaration_headers_def] >>
  qexists `tops` >> simp[]
QED

Theorem deploy_ctor_immutable_size:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) ==>
  LENGTH runtime_bc + imm_len tops < dimword(:256)
Proof
  strip_tac >> drule deploy_imm_budget_ok >> simp[]
QED

Theorem deploy_ctor_oracle_storage:
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  oracle_storage_ok (deploy_evaluation_context tops am tx)
    (es0 with outcomes := SOME vs.vs_outcomes)
Proof
  strip_tac >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    (qpat_x_assum `gas_variant _ _` mp_tac >>
     simp[gas_variant_def] >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_outcomes`) >>
     simp[deploy_entry_state_def, entry_venom_state_def]) >>
  fs[deploy_oracle_storage_payload] >>
  qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
  simp[deploy_state_rel_def] >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  irule contract_storage_well_formed_backends_frame >>
  qexists `initial_state (am with <|accounts := co.co_accounts;
                                  tStorage := co.co_tStorage|>) []` >>
  simp[vyperInterpreterTheory.initial_state_def] >>
  metis_tac[]
QED

Theorem compile_register_constructor_args_return_pc:
  !args cenv off dsz st cenv' st'.
    compile_register_constructor_args cenv args off dsz st = (cenv', st') ==>
    cenv'.ce_return_pc = cenv.ce_return_pc
Proof
  Induct >- simp[moduleLoweringTheory.compile_register_constructor_args_def,
                 comp_return_def] >>
  PairCases >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp[Once moduleLoweringTheory.compile_register_constructor_args_def]
  >- metis_tac[] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >- metis_tac[] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem deploy_ctor_return_metadata:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
     st_epilogue,st_final,func) ==>
  cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE
Proof
  simp[deploy_ctor_code_def] >> rpt strip_tac >>
  drule compile_register_constructor_args_fields >>
  drule compile_register_constructor_args_return_pc >>
  rpt strip_tac >>
  qpat_x_assum `set_constructor_package_target _ _ = _` mp_tac >>
  PairCases_on `cf` >>
  simp[set_constructor_package_target_def, package_constructor_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_ctor_target_package_immutable[local]:
  !target tops use_trans nkeys cf cenv args rest.
    set_constructor_package_target target
      (package_constructor tops use_trans nkeys cf) = (cenv,args,rest) ==>
    cenv.ce_imm_alloca = NONE
Proof
  rpt gen_tac >> PairCases_on `cf` >>
  simp[set_constructor_package_target_def, package_constructor_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_frame_outcomes_accounts_typed:
  call_outcomes_ok am tx os ==> outcomes_accounts_typed (SOME os)
Proof
  simp[call_outcomes_ok_def, exprSimHypsDefsTheory.outcomes_accounts_typed_def,
       EVERY_MEM] >> metis_tac[]
QED

Theorem compile_register_constructor_args_body_inv:
  !args cenv off dsz st cenv' st' tops ctx cx.
    body_inv tops ctx cenv cx /\
    compile_register_constructor_args cenv args off dsz st = (cenv',st') ==>
    body_inv tops ctx cenv' cx
Proof
  Induct >- simp[compile_register_constructor_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp[Once compile_register_constructor_args_def] >- metis_tac[] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >- metis_tac[] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  gvs[body_inv_def] >> metis_tac[]
QED

Theorem deploy_ctor_target_reserved_entry:
  !target tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   cenv0 pos_args rest cap data_size st0 imm st1 cenv st2.
    set_constructor_package_target target
      (package_constructor tops use_trans nkey_map
        (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
      (cenv0,pos_args,rest) /\
    (if cap > 0 then
       do r <- compile_fixed_region_with_id cap;
          comp_return (SND r).buf_operand
       od
     else comp_return (Lit 0w)) st0 = (imm,st1) /\
    compile_register_constructor_args
      (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
      pos_args 0 data_size st1 = (cenv,st2) ==>
    local_ptrs_reserved cenv st2 /\
    EVERY (\a. ?p sz.
      FLOOKUP cenv.ce_vars (FST a) = SOME (PtrVar (Var p) sz)) fargs /\
    cenv.ce_is_ctor /\
    cenv.ce_imm_alloca = (if cap > 0 then SOME imm else NONE) /\
    (cap > 0 ==> ?x. imm = Var x /\
      not_fresh_at st1 x /\ not_fresh_at st2 x)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops Deploy mut fname fargs ret fbody
                      use_trans).ce_vars /\
   MAP FST pos_args = MAP FST fargs /\ cenv0.ce_is_ctor` by
    gvs[set_constructor_package_target_def, package_constructor_def,
        update_cenv_nonreentrant_def, build_positional_args_FST] >>
  `cap > 0 ==> ?x. imm = Var x /\ not_fresh_at st1 x` by
    (strip_tac >>
     qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     simp[comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     rename1 `compile_fixed_region_with_id cap st0 = (r,sa)` >>
     PairCases_on `r` >>
     drule compile_fixed_region_with_id_result >> strip_tac >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  drule compile_register_constructor_args_fields >> simp[] >> strip_tac >>
  qspecl_then [`tops`, `Deploy`, `mut`, `fname`, `fargs`, `ret`, `fbody`,
               `use_trans`] strip_assume_tac build_compile_env_vars >>
  drule compile_register_constructor_args_reserved >>
  impl_tac >- (simp[build_positional_args_FST] >>
              Cases_on `cap > 0` >> gvs[] >> metis_tac[]) >>
  strip_tac >> simp[] >> conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
      gvs[MEM_MAP] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[local_ptrs_reserved_def]
QED

Theorem deploy_frame_register_constructor_args_bound[local]:
  !args cenv off dsz st cenv' st' n l.
    compile_register_constructor_args cenv args off dsz st = (cenv',st') /\
    FLOOKUP cenv'.ce_vars n = SOME l ==>
    ?l0. FLOOKUP cenv.ce_vars n = SOME l0
Proof
  Induct >- simp[compile_register_constructor_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  simp[Once compile_register_constructor_args_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  first_x_assum drule_all >> simp[FLOOKUP_UPDATE] >> rw[] >> gvs[]
QED

Theorem deploy_ctor_target_entry_declared:
  !target tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   cenv0 pos_args rest cap imm dsz st cenv st' n l.
    set_constructor_package_target target
      (package_constructor tops use_trans nkey_map
        (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
      (cenv0,pos_args,rest) /\
    compile_register_constructor_args
      (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
      pos_args 0 dsz st = (cenv,st') /\
    FLOOKUP cenv.ce_vars n = SOME l ==>
    MEM n (MAP FST fargs)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops Deploy mut fname fargs ret fbody
                      use_trans).ce_vars` by
    gvs[set_constructor_package_target_def, package_constructor_def,
        update_cenv_nonreentrant_def] >>
  drule_all deploy_frame_register_constructor_args_bound >> strip_tac >>
  gvs[] >> drule build_compile_env_bound >> simp[]
QED

Theorem deploy_ctor_target_locals_declared:
  !target tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   cenv0 pos_args rest cap imm dsz st cenv st' env_t.
    set_constructor_package_target target
      (package_constructor tops use_trans nkey_map
        (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
      (cenv0,pos_args,rest) /\
    compile_register_constructor_args
      (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
      pos_args 0 dsz st = (cenv,st') /\
    (!n. MEM n (MAP FST fargs) ==> n IN FDOM env_t.var_types) ==>
    ce_locals_declared cenv env_t
Proof
  rpt strip_tac >> rw[ce_locals_declared_def] >>
  drule_all deploy_ctor_target_entry_declared >> simp[]
QED

Theorem deploy_ctor_formal_ptrs_domain:
  !cenv fargs env_t.
    EVERY (\a : string # type. ?p sz.
      FLOOKUP cenv.ce_vars (FST a) = SOME (PtrVar (Var p) sz)) fargs /\
    (!n. n IN FDOM env_t.var_types ==> MEM n (MAP FST fargs)) ==>
    !n. n IN FDOM env_t.var_types ==>
      ?p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  simp[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem deploy_ctor_immutable_epilogue:
  !tops am tx mut nr body am_c es0 rpolicy runtime_bc dunit cenv nkey ut
   imm exit_lbl sa sb sj st_exit st_epilogue st_final func.
    deploy_source_ok tops am tx /\
    deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) ==>
    (imm_len tops <> 0 ==>
      cenv.ce_imm_alloca = SOME imm /\
      !x. imm = Var x ==> not_fresh_at st_epilogue x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_not_nonreentrant >> strip_tac >>
  qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  simp[deploy_ctor_code_def, comp_return_def] >> strip_tac >>
  PairCases_on `cf` >>
  drule_all deploy_ctor_target_reserved_entry >> strip_tac >>
  strip_tac >> gvs[] >>
  `st2.cs_next_var <= sa.cs_next_var` by
    (mp_tac (Q.SPECL [`"ctor_exit"`, `st2`] ci_mono_fresh_label) >>
     simp[ci_mono_def]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (CONJUNCT2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `sb.cs_next_var <= sj.cs_next_var` by
    (Cases_on `block_is_terminated sb` >> gvs[comp_return_def] >>
     mp_tac (Q.SPECL [`JMP`, `[Label exit_lbl]`, `[]`, `sb`]
               ci_mono_emit_inst) >> simp[ci_mono_def]) >>
  `sj.cs_next_var <= st_epilogue.cs_next_var` by
    (mp_tac (Q.SPECL [`exit_lbl`, `sj`] ci_mono_new_block) >>
     simp[ci_mono_def]) >>
  irule not_fresh_at_mono >> qexists `st2` >>
  gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem deploy_frame_bind_arguments_popped:
  !args tenv vals env.
    bind_arguments tenv args vals = SOME env ==>
    !n entry. FLOOKUP env n = SOME entry ==> entry.popped = []
Proof
  Induct >- (Cases_on `vals` >> simp[bind_arguments_def]) >>
  PairCases >> rpt gen_tac >> Cases_on `vals` >>
  simp[bind_arguments_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> fs[FLOOKUP_UPDATE] >> Cases_on `n = h0` >> gvs[] >>
  metis_tac[]
QED

Theorem deploy_frame_bound_arguments_indexed:
  bind_arguments tenv args vals = SOME env ==> popped_keys_indexed [env]
Proof
  strip_tac >> simp[exprSimHypsDefsTheory.popped_keys_indexed_def] >>
  rpt strip_tac >> drule_all deploy_frame_bind_arguments_popped >>
  simp[popped_history_typed_def]
QED

Theorem deploy_frame_send_value_scopes:
  send_call_value mut cx st = (res,st') ==> st'.scopes = st.scopes
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

Theorem deploy_frame_transfer_value_tStorage:
  !f t a st res st'.
    transfer_value f t a st = (res,st') ==> st'.tStorage = st.tStorage
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def,
     return_def, check_def, type_check_def, assert_def, update_accounts_def] >>
  gvs[AllCaseEqs(), raise_def]
QED

Theorem deploy_frame_send_value_tStorage:
  send_call_value mut cx st = (res,st') ==> st'.tStorage = st.tStorage
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac deploy_frame_transfer_value_tStorage >> gvs[]
QED

Theorem deploy_frame_module_constants_tStorage:
  !mods cx am addr am'.
    evaluate_module_constants cx am addr mods = SOME am' ==>
    am'.tStorage = am.tStorage
Proof
  Induct >- simp[evaluate_module_constants_def] >>
  PairCases >> rpt gen_tac >>
  simp[evaluate_module_constants_def, AllCaseEqs()] >> rpt strip_tac >>
  first_x_assum drule >> simp[merge_constants_def]
QED

Theorem deploy_frame_all_constants_tStorage:
  evaluate_all_constants cx am addr mods = SOME am' ==>
  am'.tStorage = am.tStorage
Proof
  simp[evaluate_all_constants_def] >>
  metis_tac[deploy_frame_module_constants_tStorage]
QED

Theorem deploy_frame_module_constants_accounts:
  !mods cx am addr am'.
    evaluate_module_constants cx am addr mods = SOME am' ==>
    am'.accounts = am.accounts
Proof
  Induct >- simp[evaluate_module_constants_def] >>
  PairCases >> rpt gen_tac >>
  simp[evaluate_module_constants_def, AllCaseEqs()] >> rpt strip_tac >>
  first_x_assum drule >> simp[merge_constants_def]
QED

Theorem deploy_frame_all_constants_accounts:
  evaluate_all_constants cx am addr mods = SOME am' ==>
  am'.accounts = am.accounts
Proof
  simp[evaluate_all_constants_def] >>
  metis_tac[deploy_frame_module_constants_accounts]
QED

Theorem deploy_frame_ctor_start_scopes:
  !tops am tx mut body am_c es0.
    deploy_ctor_start tops am tx (mut,F,body,am_c,es0) ==>
    popped_keys_indexed es0.scopes /\ es0.tStorage = am.tStorage
Proof
  rpt gen_tac >> simp[deploy_ctor_start_def] >> strip_tac >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp[lock_if_nr_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule deploy_frame_send_value_scopes >> disch_then assume_tac >>
  drule deploy_frame_send_value_tStorage >> disch_then assume_tac >>
  gvs[initial_state_def] >> conj_tac
  >- (irule deploy_frame_bound_arguments_indexed >>
      goal_assum (drule_at Any)) >>
  drule deploy_frame_all_constants_tStorage >> simp[]
QED

Theorem deploy_frame_checked_body_setup:
  !layouts tx mods deploy_art runtime_art sources ts mut nr args dflts ret body
   cx vals scope st.
    check_contract T layouts tx.target mods = SOME deploy_art /\
    check_contract F layouts tx.target mods = SOME runtime_art /\
    ALOOKUP sources tx.target = SOME mods /\ ALOOKUP mods NONE = SOME ts /\
    lookup_function NONE tx.function_name Deploy ts =
      SOME (mut,nr,args,dflts,ret,body) /\
    cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) /\
    bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
    ALL_DISTINCT (MAP FST args) /\ st.scopes = [scope] /\ state_well_typed st /\
    env_immutables_consistent (artifact_env deploy_art mods NONE) cx st /\
    context_well_typed cx ==>
    ?env_body env_after.
      env_body.current_src = NONE /\
      env_body.type_defs = type_env_all_modules mods /\
      env_body.fn_sigs = deploy_art.cta_fn_sigs /\
      env_body.bare_globals = deploy_art.cta_bare_globals /\
      env_body.bare_global_assignable = deploy_art.cta_bare_global_assignable /\
      env_body.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
      env_body.flag_members = deploy_art.cta_flag_members /\
      type_stmts env_body ret body = SOME env_after /\
      (!id typ. MEM (id,typ) args ==>
        FLOOKUP env_body.var_types id = SOME typ /\
        IS_SOME (FLOOKUP env_body.var_assignable id)) /\
      (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
        ?id. MEM (id,ty) args /\ n = id) /\
      (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
        ?id typ. MEM (id,typ) args /\ n = id) /\
      env_consistent env_body cx st /\ functions_well_typed cx
Proof
  rpt gen_tac >> strip_tac >>
  `env_context_consistent (artifact_env deploy_art mods NONE) cx` by
    (gvs[] >> irule checked_deployment_env_context_consistent >> simp[]) >>
  `functions_well_typed cx` by
    (gvs[] >> irule check_contract_functions_well_typed_deploy >> simp[]) >>
  drule_all checked_constructor_body_typing_package >> strip_tac >>
  `env_consistent env_body cx st` by
   (rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env deploy_art mods NONE` >>
      gvs[artifact_env_def, get_tenv_def, initial_evaluation_context_def])
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def, artifact_env_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`env_body`, `env_after`] >> simp[] >> metis_tac[]
QED

Theorem deploy_frame_bound_start_typing:
  !am tx mods deploy_art runtime_art cx imms exps am_c args vals scope mut st.
    check_contract T am.layouts tx.target mods = SOME deploy_art /\
    check_contract F am.layouts tx.target mods = SOME runtime_art /\
    machine_well_typed am /\
    cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
            NONE with in_deploy := T) /\ context_well_typed cx /\
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    evaluate_all_constants cx
      (am with <|immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps)|>)
      tx.target mods = SOME am_c /\
    bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
    send_call_value mut cx
      (initial_state am_c [scope] with <|outcomes := NONE; requests := []|>) =
      (INL (),st) ==>
    state_well_typed st /\ accounts_well_typed st.accounts /\
    st.scopes = [scope] /\
    env_immutables_consistent (artifact_env deploy_art mods NONE) cx st
Proof
  rpt gen_tac >> strip_tac >>
  `machine_well_typed am_c` by
    (drule_all checked_constructor_constants_exist >>
     disch_then (qspec_then `exps` mp_tac) >> strip_tac >> gvs[]) >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `state_well_typed
     (initial_state am_c [scope] with <|outcomes := NONE; requests := []|>) /\
   accounts_well_typed am_c.accounts` by
    gvs[machine_well_typed_def, state_well_typed_def, initial_state_def] >>
  `state_well_typed st /\ accounts_well_typed st.accounts /\
   st.immutables = am_c.immutables` by
    (`accounts_well_typed
        (initial_state am_c [scope] with <|outcomes := NONE; requests := []|>).accounts`
       by simp[initial_state_def] >>
     drule_all send_call_value_state_sound_c53 >> simp[initial_state_def]) >>
  drule deploy_frame_send_value_scopes >> simp[initial_state_def] >> strip_tac >>
  simp[] >>
  drule_all checked_constructor_initial_immutables_consistent >>
  disch_then (qspecl_then [`scope`, `[]`, `NONE`, `[]`] assume_tac) >>
  irule (iffLR env_immutables_consistent_immutables_cong) >>
  qexists `initial_state am_c [scope] with <|outcomes := NONE; requests := []; gas_obs := []|>` >>
  gvs[initial_state_def]
QED

Theorem deploy_frame_source_start_setup:
  !tops am tx mut nr body am_c es0.
  deploy_source_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) ==>
  ?deploy_art runtime_art args env_body env_after.
    check_contract T am.layouts tx.target [(NONE,tops)] = SOME deploy_art /\
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME runtime_art /\
    lookup_function NONE tx.function_name Deploy tops =
      SOME (mut,nr,args,[],NoneT,body) /\
    env_body.current_src = NONE /\
    env_body.type_defs = type_env_all_modules [(NONE,tops)] /\
    env_body.fn_sigs = deploy_art.cta_fn_sigs /\
    env_body.bare_globals = deploy_art.cta_bare_globals /\
    env_body.bare_global_assignable = deploy_art.cta_bare_global_assignable /\
    env_body.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
    env_body.flag_members = deploy_art.cta_flag_members /\
    type_stmts env_body NoneT body = SOME env_after /\
    (!id typ. MEM (id,typ) args ==>
      FLOOKUP env_body.var_types id = SOME typ /\
      IS_SOME (FLOOKUP env_body.var_assignable id)) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
      ?id. MEM (id,ty) args /\ n = id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
      ?id typ. MEM (id,typ) args /\ n = id) /\
    env_consistent env_body (deploy_evaluation_context tops am tx) es0 /\
    functions_well_typed (deploy_evaluation_context tops am tx) /\
    context_well_typed (deploy_evaluation_context tops am tx) /\
    state_well_typed es0 /\ accounts_well_typed es0.accounts /\
    call_evaluation_safe (deploy_evaluation_context tops am tx) (int_calls_stmts body)
Proof
  rpt gen_tac >> strip_tac >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >>
  gvs[deploy_source_ok_def, deploy_typing_ok_def, deploy_ctor_start_def] >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp[lock_if_nr_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `context_well_typed (deploy_evaluation_context tops am tx)` by
    gvs[deploy_evaluation_context_def, call_tx_well_typed_def,
        context_well_typed_def, initial_evaluation_context_def] >>
  drule_all (SRULE [GSYM deploy_evaluation_context_def]
    (Q.SPECL [`am`, `tx`, `[(NONE,tops)]`] deploy_frame_bound_start_typing)) >>
  strip_tac >>
  `ALOOKUP [(NONE:num option,tops)] NONE = SOME tops /\
   ALOOKUP ((tx.target,[(NONE,tops)])::am.sources) tx.target =
     SOME [(NONE,tops)] /\
   deploy_evaluation_context tops am tx =
     (initial_evaluation_context ((tx.target,[(NONE,tops)])::am.sources)
       am.layouts tx NONE with in_deploy := T)` by
    simp[deploy_evaluation_context_def] >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all checked_constructor_args_distinct >> simp[]) >>
  drule_all deploy_frame_checked_body_setup >> strip_tac >>
  drule_all checked_constructor_call_evaluation_safe >> strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >> metis_tac[]
QED

Theorem deploy_frame_supported_body:
  !tops fname mut nr args dflts ret stmts.
    supported_program tops /\
    lookup_function NONE fname Deploy tops = SOME (mut,nr,args,dflts,ret,stmts) ==>
    ?bindings. supported_stmts tops bindings stmts
Proof
  rpt gen_tac >> strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[]
  >- simp[supportedStmtsTheory.supported_stmt_def] >>
  drule_all supported_program_function >>
  simp[supported_function_body_def] >> metis_tac[]
QED

Theorem deploy_frame_send_value_storage:
  send_call_value mut cx st = (res,st') /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx st'
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  metis_tac[transfer_value_preserves_contract_storage_well_formed]
QED

Theorem deploy_frame_start_storage:
  !tops am tx mut nr stmts am_c es0.
    deploy_source_ok tops am tx /\
    deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
    storage_layout_safe (deploy_evaluation_context tops am tx) /\
    contract_storage_well_formed (deploy_evaluation_context tops am tx) es0 /\
    popped_keys_indexed es0.scopes
Proof
  rpt gen_tac >> strip_tac >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >> gvs[] >>
  drule deploy_frame_ctor_start_scopes >> strip_tac >>
  gvs[deploy_source_ok_def, deploy_storage_ok_def, deploy_ctor_start_def] >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp[lock_if_nr_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `am_c.accounts = am.accounts /\ am_c.tStorage = am.tStorage` by
    (drule deploy_frame_all_constants_accounts >>
     drule deploy_frame_all_constants_tStorage >> simp[]) >>
  irule deploy_frame_send_value_storage >> goal_assum (drule_at Any) >>
  irule contract_storage_well_formed_backends_frame >>
  qexists `initial_state am []` >> simp[initial_state_def]
QED

Theorem deploy_frame_semantic_setup:
  !tops am tx mut nr stmts am_c es0 deploy_bc es vs prog cplan.
  deploy_source_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  deploy_state_rel tops deploy_bc am tx es /\
  call_outcomes_ok am tx (MAP SND (call_trace es)) /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  ?deploy_art runtime_art args bindings env_t env'.
    check_contract T am.layouts tx.target [(NONE,tops)] = SOME deploy_art /\
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME runtime_art /\
    lookup_function NONE tx.function_name Deploy tops =
      SOME (mut,nr,args,[],NoneT,stmts) /\
    env_t.current_src = NONE /\
    env_t.type_defs = type_env_all_modules [(NONE,tops)] /\
    env_t.fn_sigs = deploy_art.cta_fn_sigs /\
    env_t.bare_globals = deploy_art.cta_bare_globals /\
    env_t.bare_global_assignable = deploy_art.cta_bare_global_assignable /\
    env_t.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
    env_t.flag_members = deploy_art.cta_flag_members /\
    (!id typ. MEM (id,typ) args ==>
      FLOOKUP env_t.var_types id = SOME typ /\
      IS_SOME (FLOOKUP env_t.var_assignable id)) /\
    (!n ty. FLOOKUP env_t.var_types n = SOME ty ==>
      ?id. MEM (id,ty) args /\ n = id) /\
    (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
      ?id typ. MEM (id,typ) args /\ n = id) /\
    supported_stmts tops bindings stmts /\
    type_stmts env_t NoneT stmts = SOME env' /\
    call_evaluation_safe (deploy_evaluation_context tops am tx) (int_calls_stmts stmts) /\
    env_consistent env_t (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes) /\
    state_well_typed (es0 with outcomes := SOME vs.vs_outcomes) /\
    accounts_well_typed es0.accounts /\
    context_well_typed (deploy_evaluation_context tops am tx) /\
    functions_well_typed (deploy_evaluation_context tops am tx) /\
    storage_layout_safe (deploy_evaluation_context tops am tx) /\
    contract_storage_well_formed (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes) /\
    popped_keys_indexed es0.scopes /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    oracle_storage_ok (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_frame_source_start_setup >> strip_tac >>
  drule_all deploy_frame_start_storage >> strip_tac >>
  `supported_program tops` by gvs[deploy_source_ok_def] >>
  drule_all deploy_frame_supported_body >> strip_tac >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    (qpat_x_assum `gas_variant _ _` mp_tac >>
     simp[gas_variant_def] >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_outcomes`) >>
     simp[deploy_entry_state_def, entry_venom_state_def]) >>
  `outcomes_accounts_typed (SOME vs.vs_outcomes)` by
    metis_tac[deploy_frame_outcomes_accounts_typed] >>
  `oracle_storage_ok (deploy_evaluation_context tops am tx)
      (es0 with outcomes := SOME vs.vs_outcomes)` by
    (irule deploy_ctor_oracle_storage >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  qexistsl [`deploy_art`, `runtime_art`, `args`, `bindings`, `env_body`, `env_after`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  irule contract_storage_well_formed_backends_frame >>
  qexists `es0` >> simp[]
QED

Theorem deploy_frame_register_static_fields:
  !args cenv off dsz st cenv' st'.
    compile_register_constructor_args cenv args off dsz st = (cenv',st') ==>
    cenv'.ce_var_type = cenv.ce_var_type /\
    cenv'.ce_flag_member_id = cenv.ce_flag_member_id /\
    cenv'.ce_flag_n_members = cenv.ce_flag_n_members /\
    cenv'.ce_struct_fields = cenv.ce_struct_fields /\
    cenv'.ce_hashmap_info = cenv.ce_hashmap_info /\
    cenv'.ce_module_var_type = cenv.ce_module_var_type /\
    cenv'.ce_module_vars = cenv.ce_module_vars /\
    cenv'.ce_func_return_type = cenv.ce_func_return_type /\
    cenv'.ce_method_id = cenv.ce_method_id /\
    cenv'.ce_module = cenv.ce_module /\
    cenv'.ce_event_info = cenv.ce_event_info /\
    cenv'.ce_is_external = cenv.ce_is_external
Proof
  Induct >- simp[compile_register_constructor_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp[Once compile_register_constructor_args_def] >- metis_tac[] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >- metis_tac[] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem deploy_ctor_static_tables:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) ==>
    ?exts ints fb mut nr0 rr fname args dflts ret.
      classify_functions tops =
        (exts,ints,fb,SOME (mut,nr0,rr,fname,args,dflts,ret,body)) /\
      cenv.ce_var_type = (\id. ALOOKUP (REVERSE (args ++ collect_locals body)) id) /\
      (cenv.ce_flag_member_id,cenv.ce_flag_n_members) =
        build_flag_info tops (K (K 0)) (K 0) /\
      cenv.ce_struct_fields = make_struct_fields_map tops /\
      cenv.ce_hashmap_info = build_hashmap_info tops /\
      cenv.ce_module_var_type = build_var_type_map tops /\
      cenv.ce_module = NONE /\
      cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
      ~cenv.ce_is_external
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule deploy_frame_register_static_fields >> strip_tac >>
  PairCases_on `cf` >>
  gvs[set_constructor_package_target_def, package_constructor_def,
      update_cenv_nonreentrant_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

(* The constructor's env reads the module's variables and the internal
   functions' return types as build_compile_env does, as fn_allocs_ok_body
   needs. *)
Theorem deploy_ctor_alloc_env_agree:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) ==>
    ?exts ints fb mut nr0 rr fname args dflts ret.
      classify_functions tops =
        (exts,ints,fb,SOME (mut,nr0,rr,fname,args,dflts,ret,body)) /\
      alloc_env_agree (build_compile_env tops Internal mut fname args ret body F)
        cenv
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule deploy_frame_register_static_fields >> strip_tac >>
  PairCases_on `cf` >>
  gvs[set_constructor_package_target_def, package_constructor_def,
      alloc_env_agree_def] >>
  rw[update_cenv_nonreentrant_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

(* The constructor's method ids are the selectors over the deploy context's
   type environment, as expr_sim_inv asks. *)
Theorem deploy_ctor_method_id:
  !tops am tx rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) ==>
    !fname tys.
      cenv.ce_method_id fname tys =
      w2n (calldata_method_id
             (function_selector fname
                (vyper_to_abi_types
                   (get_tenv (deploy_evaluation_context tops am tx)) tys)))
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule deploy_frame_register_static_fields >> strip_tac >>
  PairCases_on `cf` >>
  gvs[set_constructor_package_target_def, package_constructor_def] >>
  rw[update_cenv_nonreentrant_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[deploy_evaluation_context_def, get_tenv_def,
       initial_evaluation_context_def, get_module_code_def,
       type_env_all_modules_def, GSYM type_env_def]
QED

Theorem deploy_ctor_defined_map_agreement:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func layouts addr art env.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\
    check_contract T layouts addr [(NONE,tops)] = SOME art /\
    env.toplevel_vtypes = art.cta_toplevel_vtypes ==>
    place_map_tables_agree_on_defined cenv env
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_static_tables >> strip_tac >>
  drule_all checked_single_module_defined_map_agreement >> simp[]
QED

Theorem deploy_frame_supported_no_flags:
  !tops fid.
    supported_program tops ==> lookup_flag fid tops = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `!ts. EVERY (supported_declaration_body tops) ts ==>
         lookup_flag fid ts = NONE` suffices_by
    (disch_then irule >> fs[supported_program_def]) >>
  Induct >- simp[lookup_flag_def] >>
  Cases_on `h` >>
  simp[supported_declaration_body_def, lookup_flag_def]
QED

Theorem deploy_frame_supported_no_flag_types:
  !tops nsid n.
    supported_program tops ==>
    FLOOKUP (type_env tops) nsid <> SOME (FlagArgs n)
Proof
  rpt gen_tac >> strip_tac >>
  `!ts. EVERY (supported_declaration_body tops) ts ==>
        FLOOKUP (type_env_for_module NONE ts) nsid <> SOME (FlagArgs n)`
    suffices_by (disch_then (qspec_then `tops` mp_tac) >>
                 fs[type_env_def, supported_program_def]) >>
  Induct >- simp[type_env_for_module_def] >>
  Cases_on `h` >>
  simp[supported_declaration_body_def, type_env_for_module_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem deploy_frame_flag_compatibility:
  !tops am tx cenv.
    supported_program tops ==>
    (!src fid ts ls mid i.
       get_module_code (deploy_evaluation_context tops am tx) src = SOME ts /\
       lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i ==>
       cenv.ce_flag_member_id (nsid_to_string (src,fid)) mid = i) /\
    (!nsid m.
       FLOOKUP (get_tenv (deploy_evaluation_context tops am tx)) nsid =
         SOME (FlagArgs m) ==>
       cenv.ce_flag_n_members (nsid_to_string nsid) = m)
Proof
  rpt gen_tac >> strip_tac >>
  simp[deploy_evaluation_context_def, initial_evaluation_context_def,
       get_module_code_def, get_tenv_def, type_env_all_modules_def,
       GSYM type_env_def] >>
  conj_tac
  >- metis_tac[deploy_frame_supported_no_flags, optionTheory.NOT_SOME_NONE] >>
  metis_tac[deploy_frame_supported_no_flag_types]
QED

Theorem deploy_frame_checked_struct_metadata:
  !tops layouts addr art.
    check_contract T layouts addr [(NONE,tops)] = SOME art ==>
    sfields_tenv_consistent (make_struct_fields_map tops) (type_env tops) /\
    (!name fields.
       FLOOKUP (make_struct_fields_map tops) name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (type_env tops) fty = SOME tv ==>
         sz = type_memory_size tv) fields)
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    (drule check_contract_namespaces_ok >>
     simp[contract_namespaces_ok_def, contract_keys_def]) >>
  conj_tac >- simp[make_struct_fields_map_consistent] >>
  rpt gen_tac >> strip_tac >>
  `struct_args_unique tops` by metis_tac[distinct_type_keys_struct_args_unique] >>
  qpat_x_assum `FLOOKUP _ name = _` mp_tac >>
  simp[make_struct_fields_map_def] >> strip_tac >>
  drule built_struct_fields_origin >> simp[] >> strip_tac >>
  drule_all build_struct_fields_map_lookup >>
  disch_then (qspecl_then [`type_env tops`, `FEMPTY`] mp_tac) >>
  strip_tac >> gvs[GSYM type_env_def] >>
  `MEM ((NONE:num option),tops) [(NONE,tops)]` by simp[] >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all check_contract_struct_fields_distinct >> simp[]) >>
  simp[built_struct_fields_names, build_struct_fields_one_def,
       EVERY_MAP, EVERY_MEM, FORALL_PROD, field_mem_bytes_def,
       MEM_MAP, EXISTS_PROD] >> rpt strip_tac >> gvs[]
QED

Theorem deploy_ctor_struct_compatibility:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func am tx art.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\
    check_contract T am.layouts tx.target [(NONE,tops)] = SOME art ==>
    sfields_tenv_consistent cenv.ce_struct_fields
      (get_tenv (deploy_evaluation_context tops am tx)) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv (deploy_evaluation_context tops am tx)) fty = SOME tv ==>
         sz = type_memory_size tv) fields)
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_static_tables >> strip_tac >>
  drule deploy_frame_checked_struct_metadata >> strip_tac >>
  simp[deploy_evaluation_context_def, initial_evaluation_context_def,
       get_tenv_def, type_env_all_modules_def, GSYM type_env_def] >>
  metis_tac[]
QED

Theorem deploy_frame_bare_global_hashmap_exclusion:
  !tops am tx art env st cenv.
    supported_program tops /\
    check_contract T am.layouts tx.target [(NONE,tops)] = SOME art /\
    env_consistent env (deploy_evaluation_context tops am tx) st /\
    cenv.ce_hashmap_info = build_hashmap_info tops ==>
    !nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
      cenv.ce_hashmap_info nsid = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (drule check_contract_namespaces_ok >>
     simp[contract_namespaces_ok_def, contract_keys_def]) >>
  PairCases >> rpt gen_tac >> strip_tac >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >>
  gvs[deploy_evaluation_context_def, initial_evaluation_context_def,
      get_module_code_def] >>
  `?vis ty slot. MEM (VariableDecl vis Immutable nsid1 ty slot) tops` by
    (irule supported_bare_global_immutable >> fs[supported_program_def]) >>
  drule_all build_hashmap_info_variable >> simp[]
QED

Theorem deploy_frame_static_bare_globals:
  !tops vis mut fname args ret stmts locks cx env es.
    supported_program tops /\
    (!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops) /\
    get_module_code cx NONE = SOME tops /\
    get_tenv cx = type_env tops /\
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    env_consistent env cx es /\
    imm_len tops < dimword(:256) ==>
    !src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
      src = NONE /\
      ?off. FLOOKUP (build_compile_env tops vis mut fname args ret stmts locks)
               .ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
        !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
          off + type_memory_size tv < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >>
  `src = NONE /\ ts = tops` by metis_tac[] >> gvs[] >>
  `?dvis dty dslot. MEM (VariableDecl dvis Immutable id dty dslot) tops` by
    metis_tac[supported_bare_global_immutable, supported_program_def] >>
  drule immutable_build_compile_env_declared >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexists `off` >> fs[build_compile_env_module_vars] >> rpt strip_tac >>
  mp_tac (Q.SPEC `tops` immutable_build_compile_env_layout) >>
  simp[immutableRelationTheory.immutable_section_layout_def,
       build_compile_env_module_vars] >>
  disch_then drule >> strip_tac >>
  rename1 `tops = pre ++ [VariableDecl decl_vis Immutable id decl_ty decl_slot] ++ post` >>
  `bare_globals_complete env.bare_globals cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `MEM (VariableDecl decl_vis Immutable id decl_ty decl_slot) tops` by
    metis_tac[MEM_APPEND, MEM] >>
  `decl_ty = ty` by
    (fs[bare_globals_complete_def] >> metis_tac[optionTheory.SOME_11]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
   type_memory_size tv` by
    (`type_memory_bytes (build_compile_env tops vis mut fname args ret stmts locks) ty =
      type_memory_size tv` by
       (irule build_compile_env_type_memory_bytes >> simp[] >> metis_tac[]) >>
     fs[GSYM type_mem_bytes_type_memory_bytes, build_compile_env_ce_struct_fields]) >>
  `off + type_memory_size tv <= imm_len tops` by
    (qpat_x_assum `decl_ty = ty` SUBST_ALL_TAC >>
     qpat_x_assum `tops = _` SUBST_ALL_TAC >>
     simp[imm_len_def, compute_immutables_len_append, compute_immutables_len_def]) >>
  decide_tac
QED

Theorem deploy_ctor_module_locations:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) ==>
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY)
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule deploy_frame_register_static_fields >> strip_tac >>
  PairCases_on `cf` >>
  gvs[set_constructor_package_target_def, package_constructor_def,
      update_cenv_nonreentrant_def] >>
  simp[build_compile_env_module_vars]
QED

Theorem deploy_ctor_bare_global_bounds:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func am tx art env es.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\
    supported_program tops /\
    check_contract T am.layouts tx.target [(NONE,tops)] = SOME art /\
    env_consistent env (deploy_evaluation_context tops am tx) es /\
    imm_len tops < dimword(:256) ==>
    !src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
      src = cenv.ce_module /\
      ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
        !tv. evaluate_type (get_tenv (deploy_evaluation_context tops am tx)) ty = SOME tv ==>
          off + type_memory_size tv < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_module_locations >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    (drule check_contract_namespaces_ok >>
     simp[contract_namespaces_ok_def, contract_keys_def]) >>
  `get_tenv (deploy_evaluation_context tops am tx) = type_env tops` by
    simp[deploy_evaluation_context_def, initial_evaluation_context_def,
         get_tenv_def, type_env_all_modules_def, GSYM type_env_def] >>
  mp_tac (Q.SPEC `tops` deploy_frame_static_bare_globals) >>
  simp[build_compile_env_module_vars] >>
  disch_then (qspecl_then [`deploy_evaluation_context tops am tx`, `env`, `es`] mp_tac) >>
  (impl_tac >-
    (simp[deploy_evaluation_context_def, initial_evaluation_context_def,
          get_module_code_def] >> metis_tac[])) >> simp[]
QED

Theorem deploy_frame_collect_locals_names[local]:
  !body id.
    MEM id (MAP FST (collect_locals body)) <=>
    MEM id (MAP FST (supported_stmts_bindings T body)) \/
    MEM id (MAP FST (supported_stmts_bindings F body))
Proof
  recInduct collect_locals_ind >>
  simp[collect_locals_def, supportedStmtTraverseTheory.supported_stmt_bindings_def] >> metis_tac[]
QED

Theorem deploy_frame_formal_type_lookup:
  !tops vis args body id ty.
    supported_function_body tops vis args body /\ MEM (id,ty) args ==>
    ALOOKUP (REVERSE (args ++ collect_locals body)) id = SOME ty
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `supported_function_body tops vis args stmts` >>
  `MEM id (MAP FST args)` by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST args) /\
   ~MEM id (MAP FST (supported_stmts_bindings T stmts)) /\
   ~MEM id (MAP FST (supported_stmts_bindings F stmts))` by
    (fs[supported_function_body_def, supportedNamesTheory.supported_function_bindings_def,
        ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `ALOOKUP (REVERSE (collect_locals stmts)) id = NONE` by
    simp[alistTheory.ALOOKUP_NONE, MAP_REVERSE, deploy_frame_collect_locals_names] >>
  simp[REVERSE_APPEND, alistTheory.ALOOKUP_APPEND] >>
  irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> simp[MAP_REVERSE]
QED

Theorem deploy_frame_classified_constructor_lookup:
  !tops src name.
    case SND (SND (SND (classify_functions tops))) of
      NONE => lookup_function src name Deploy tops =
        SOME (Payable,F,[],[],NoneT,[])
    | SOME (mut,nr,rr,fname,args,dflts,ret,stmts) =>
        fname = name ==>
        lookup_function src name Deploy tops = SOME (mut,nr,args,dflts,ret,stmts)
Proof
  Induct >- simp[classify_functions_def, lookup_function_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`src`, `name`] mp_tac) >>
  simp[classify_functions_def] >>
  `?a b c d. FOLDR classify_function ([],[],NONE,NONE) tops = (a,b,c,d)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  simp[] >> strip_tac >> Cases_on `h` >>
  simp[classify_function_def, lookup_function_def]
  >~ [`VariableDecl vd`]
  >- (Cases_on `vd` >> simp[lookup_function_def])
  >~ [`HashMapDecl hd`]
  >- (Cases_on `hd` >> simp[lookup_function_def]) >>
  qmatch_goalsub_rename_tac `case vv of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vv` >> rw[]
QED

Theorem deploy_ctor_formal_var_types:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func mut args.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\ supported_program tops /\
    lookup_function NONE "__init__" Deploy tops =
      SOME (mut,nr,args,[],NoneT,stmts) ==>
    !id ty. MEM (id,ty) args ==> cenv.ce_var_type id = SOME ty
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_static_tables >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_ctor_code_def] >>
  `fname = "__init__"` by
    (drule_all lower_vyper_deploy_unit_ctor_named_init >> simp[ctor_named_init_def]) >>
  mp_tac (Q.SPECL [`tops`, `NONE:num option`, `"__init__"`]
    deploy_frame_classified_constructor_lookup) >> simp[] >> strip_tac >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
  drule_all supported_program_function >> strip_tac >>
  irule deploy_frame_formal_type_lookup >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any)
QED

Theorem deploy_ctor_allocation_bounds:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func mut args.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\
    lookup_function NONE "__init__" Deploy tops =
      SOME (mut,nr,args,[],NoneT,stmts) ==>
    EVERY (\a. type_memory_bytes cenv (SND a) < 2 ** 64) args /\
    alloc_limits_stmts cenv stmts /\
    ~supported_stmts_expr_exists
      (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) stmts
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_static_tables >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_ctor_code_def] >>
  `fname = "__init__"` by
    (drule_all lower_vyper_deploy_unit_ctor_named_init >> simp[ctor_named_init_def]) >>
  mp_tac (Q.SPECL [`tops`, `NONE:num option`, `"__init__"`]
    deploy_frame_classified_constructor_lookup) >> simp[] >> strip_tac >> gvs[] >>
  `fn_allocs_ok tops (mut,nr,rr,"__init__",args,[],NoneT,stmts)` by
    (irule lower_vyper_deploy_unit_allocs_ok >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `alloc_env_agree
     (build_compile_env tops Internal mut "__init__" args NoneT stmts F) cenv` by
    (drule deploy_ctor_alloc_env_agree >> strip_tac >> gvs[]) >>
  drule_all fn_allocs_ok_body >>
  simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem deploy_frame_formal_locals_alloc_ok:
  !cenv env args.
    EVERY (\a. type_memory_bytes cenv (SND a) < 2 ** 64) args /\
    (!n ty. FLOOKUP env.var_types n = SOME ty ==>
      ?id. MEM (id,ty) args /\ n = id) ==>
    locals_alloc_ok cenv env
Proof
  simp[locals_alloc_ok_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem deploy_frame_package_body_inv:
  !tops am tx rpolicy runtime_bc dunit
   (cf : function_mutability # bool # bool # string # (string # type) list #
         expr list # type # stmt list) cenv args rest art exts ints fb.
    supported_program tops /\
    check_contract T am.layouts tx.target [(NONE,tops)] = SOME art /\
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    classify_functions tops = (exts,ints,fb,SOME cf) /\
    set_constructor_package_target rpolicy.rpol_target
      (package_constructor tops F (assign_nkeys tops 0) cf) = (cenv,args,rest) ==>
    body_inv tops dunit.cu_context cenv (deploy_evaluation_context tops am tx)
Proof
  rpt gen_tac >> strip_tac >>
  `acyclic_struct_metadata (make_struct_fields_map tops)` by
    metis_tac[supported_checked_struct_metadata_acyclic] >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (drule check_contract_namespaces_ok >>
     simp[contract_namespaces_ok_def, contract_keys_def]) >>
  qpat_x_assum `set_constructor_package_target _ _ = _` mp_tac >>
  PairCases_on `cf` >>
  simp[set_constructor_package_target_def, package_constructor_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[body_inv_def, deploy_evaluation_context_def,
       initial_evaluation_context_def, get_module_code_def, get_tenv_def,
       type_env_all_modules_def, GSYM type_env_def,
       build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt conj_tac >>
  TRY (qexistsl [`rpolicy`, `dunit`] >> simp[] >> metis_tac[] >> NO_TAC) >>
  gvs[]
QED

Theorem deploy_ctor_body_inv:
  !tops am tx rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
    deploy_source_ok tops am tx /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) ==>
    body_inv tops dunit.cu_context cenv (deploy_evaluation_context tops am tx)
Proof
  rpt gen_tac >> simp[deploy_source_ok_def, deploy_typing_ok_def,
                      deploy_ctor_code_def] >> strip_tac >>
  `body_inv tops dunit.cu_context cenv0 (deploy_evaluation_context tops am tx)` by
    (irule deploy_frame_package_body_inv >> simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `body_inv tops dunit.cu_context
     (cenv0 with ce_imm_alloca :=
        (if imm_len tops > 0 then SOME imm else NONE))
     (deploy_evaluation_context tops am tx)` by
    (fs[body_inv_def] >> metis_tac[]) >>
  drule_all compile_register_constructor_args_body_inv >> strip_tac >>
  fs[body_inv_def] >> metis_tac[]
QED

Theorem deploy_frame_storage_var_types:
  !tops ctx cenv am tx.
    body_inv tops ctx cenv (deploy_evaluation_context tops am tx) ==>
    !src id ts tr typ id_str.
      get_module_code (deploy_evaluation_context tops am tx) src = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
      cenv.ce_hashmap_info (src,id) = NONE /\
      cenv.ce_module_var_type (src,id) = SOME typ
Proof
  rpt gen_tac >> strip_tac >>
  `!src ts. get_module_code (deploy_evaluation_context tops am tx) src = SOME ts ==>
            src = NONE` by
    simp[deploy_evaluation_context_def, initial_evaluation_context_def,
         get_module_code_def] >>
  metis_tac[bodySimStmtCasesTheory.body_inv_storage_var_types]
QED

(* body_stmts_sim's premises for the constructor body at its start, and the
   side conditions of constructor_frame_ret_ok and constructor_exit_run. *)
Theorem deploy_frame_checked_constructor_arg_types:
  !in_deploy layouts addr mods art ts fname mut nr args dflts ret body.
  check_contract in_deploy layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  vyperInterpreter$lookup_function NONE fname Deploy ts = SOME (mut,nr,args,dflts,ret,body) ==>
  !id ty. MEM (id,ty) args ==> well_formed_type (type_env_all_modules mods) ty
Proof
  rpt gen_tac >> strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
  gvs[check_contract_def, EVERY_MEM] >>
  drule ALOOKUP_MEM >> strip_tac >>
  first_x_assum drule >> simp[check_module_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!e. MEM e ts ==> check_toplevel_decl _ _ _ _` drule >>
  simp[check_toplevel_decl_def, params_ok_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  metis_tac[assignable_type_well_formed]
QED

Theorem deploy_frame_constructor_env_well_formed:
  !in_deploy layouts addr mods art ts fname mut nr args dflts ret body env cx st.
  check_contract in_deploy layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  vyperInterpreter$lookup_function NONE fname Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
  env.type_defs = type_env_all_modules mods /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==>
     ?id. MEM (id,ty) args /\ n = id) /\
  env_consistent env cx st ==>
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[deploy_frame_checked_constructor_arg_types] >>
  gvs[env_consistent_def, env_context_consistent_def] >>
  PairCases >> metis_tac[]
QED

Theorem deploy_frame_typed_allocated_stmts_exprs_ok:
  !env ret ss env' cenv.
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\
  type_stmts env ret ss = SOME env' /\
  ~supported_stmts_expr_exists (\e. ~alloc_limits_expr cenv e) ss /\
  alloc_limits_stmts cenv ss /\ ~cenv.ce_is_external ==>
  EVERY (stmt_exprs_ok cenv) ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_frame_typed_stmts_no_bad_widths >> strip_tac >>
  `~supported_stmts_expr_exists
     (\e. ~byte_widths_expr e \/ ~alloc_limits_expr cenv e) ss` by
    fs[deploy_frame_stmt_exists_disj] >>
  `(\e. ~byte_widths_expr e \/ ~alloc_limits_expr cenv e) =
   (\e. (~is_extcode e /\ (~byte_widths_expr e \/ ~alloc_limits_expr cenv e)) \/
        (is_extcode e /\ (~byte_widths_expr e \/ ~alloc_limits_expr cenv e)))` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  fs[deploy_frame_stmt_exists_disj] >>
  fs[stmts_exprs_ok_EVERY, DE_MORGAN_THM]
QED

Theorem deploy_ctor_typed_allocation_frame:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func mut args bindings env env'.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
     st_epilogue,st_final,func) /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,nr,args,[],NoneT,stmts) /\
  supported_stmts tops bindings stmts /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     well_formed_type env.type_defs ty) /\
  (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==>
     well_formed_vtype env.type_defs vt) /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==>
     ?id. MEM (id,ty) args /\ n = id) /\
  type_stmts env NoneT stmts = SOME env' ==>
  EVERY (stmt_exprs_ok cenv) stmts /\ locals_alloc_ok cenv env
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_allocation_bounds >> strip_tac >>
  drule deploy_ctor_static_tables >> strip_tac >>
  drule deploy_frame_supported_stmts_no_extcode >> strip_tac >>
  drule_all deploy_frame_remove_extcode_guard >> strip_tac >>
  conj_tac >- (irule deploy_frame_typed_allocated_stmts_exprs_ok >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule deploy_frame_formal_locals_alloc_ok >> goal_assum (drule_at Any) >> simp[]
QED

Theorem deploy_ctor_argument_locations[local]:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func mut args.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\ supported_program tops /\
    lookup_function NONE "__init__" Deploy tops =
      SOME (mut,nr,args,[],NoneT,stmts) ==>
    EVERY (\a. ?p sz. FLOOKUP cenv.ce_vars (FST a) = SOME (PtrVar (Var p) sz)) args /\
    (!n l. FLOOKUP cenv.ce_vars n = SOME l ==> MEM n (MAP FST args))
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_ctor_code_def] >>
  qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  simp[deploy_ctor_code_def] >> strip_tac >> PairCases_on `cf` >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >> simp[ctor_named_init_def] >>
  strip_tac >>
  drule_all deploy_ctor_target_reserved_entry >> strip_tac >>
  mp_tac (Q.SPECL [`tops`, `NONE:num option`, `"__init__"`]
    deploy_frame_classified_constructor_lookup) >> simp[] >> strip_tac >>
  rpt strip_tac >> drule_all deploy_ctor_target_entry_declared >> simp[]
QED

Theorem deploy_ctor_checked_locals_declared:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func mut args env_t.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\ supported_program tops /\
    lookup_function NONE "__init__" Deploy tops =
      SOME (mut,nr,args,[],NoneT,stmts) /\
    (!id ty. MEM (id,ty) args ==> FLOOKUP env_t.var_types id = SOME ty) ==>
    ce_locals_declared cenv env_t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_argument_locations >> strip_tac >>
  rw[ce_locals_declared_def] >>
  `MEM n (MAP FST args)` by metis_tac[] >>
  qpat_x_assum `MEM n (MAP FST args)` mp_tac >>
  pure_rewrite_tac[MEM_MAP, EXISTS_PROD] >> strip_tac >>
  gvs[] >> PairCases_on `y` >> gvs[] >>
  qpat_x_assum `!id ty. MEM (id,ty) args ==> _` drule >>
  simp[FLOOKUP_DEF] >> IF_CASES_TAC >> simp[]
QED

Theorem deploy_ctor_checked_pointer_domain:
  !tops rpolicy runtime_bc dunit stmts cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func mut args env_t.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,
       st_epilogue,st_final,func) /\ supported_program tops /\
    lookup_function NONE "__init__" Deploy tops =
      SOME (mut,nr,args,[],NoneT,stmts) /\
    (!n ty. FLOOKUP env_t.var_types n = SOME ty ==>
      ?id. MEM (id,ty) args /\ n = id) ==>
    !n. n IN FDOM env_t.var_types ==>
      ?p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_argument_locations >> strip_tac >>
  rpt strip_tac >>
  `?ty. FLOOKUP env_t.var_types n = SOME ty` by simp[FLOOKUP_DEF] >>
  qpat_x_assum `!n ty. FLOOKUP env_t.var_types n = SOME ty ==> _` drule >>
  strip_tac >> gvs[] >>
  qpat_x_assum `EVERY _ args` mp_tac >>
  simp[EVERY_MEM] >> disch_then drule >> simp[]
QED

Theorem deploy_ctor_body_frame:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    call_outcomes_ok am tx (MAP SND (call_trace es)) /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
    body_inv tops dunit.cu_context cenv (deploy_evaluation_context tops am tx) /\
    cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe (deploy_evaluation_context tops am tx) /\
            (deploy_evaluation_context tops am tx).nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_epilogue x) /\
    ?bindings env_t env'.
      supported_stmts tops bindings body /\
      expr_sim_inv cenv (deploy_evaluation_context tops am tx) env_t
        (es0 with outcomes := SOME vs.vs_outcomes) /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t NoneT body = SOME env' /\
      stmts_exprs_ok cenv body /\
      call_evaluation_safe (deploy_evaluation_context tops am tx) (int_calls_stmts body)
Proof
  rpt gen_tac >> strip_tac >>
  `body_inv tops dunit.cu_context cenv (deploy_evaluation_context tops am tx)` by
    metis_tac[deploy_ctor_body_inv] >>
  `cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE` by
    metis_tac[deploy_ctor_return_metadata] >>
  `LENGTH runtime_bc + imm_len tops < dimword(:256)` by
    metis_tac[deploy_ctor_immutable_size] >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >>
  simp[] >> conj_tac
  >- metis_tac[deploy_ctor_immutable_epilogue] >>
  drule_all deploy_frame_semantic_setup >> strip_tac >>
  `tx.function_name = "__init__"` by fs[deploy_state_rel_def] >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  `imm_len tops < dimword(:256)` by decide_tac >>
  `lookup_function NONE "__init__" Deploy tops = SOME (mut,nr,args,[],NoneT,body')` by
    metis_tac[] >>
  `(!id ty. FLOOKUP env_t.var_types id = SOME ty ==>
      well_formed_type env_t.type_defs ty) /\
   (!id vt. FLOOKUP env_t.toplevel_vtypes id = SOME vt ==>
      well_formed_vtype env_t.type_defs vt)` by
    (irule (INST_TYPE [alpha |-> ``:160 word``] deploy_frame_constructor_env_well_formed) >>
     conj_tac
     >- (goal_assum (drule_at Any) >> simp[] >>
         qexistsl [`tx.target`, `deploy_art`, `T`, `am.layouts`, `[(NONE,tops)]`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  drule_all deploy_ctor_typed_allocation_frame >> strip_tac >>
  qexistsl [`bindings`, `env_t`, `env'`] >> simp[] >>
  reverse conj_tac
  >- metis_tac[deploy_ctor_checked_locals_declared] >>
  `!n. n IN FDOM env_t.var_types ==>
    ?p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (drule deploy_ctor_checked_pointer_domain >> simp[] >>
     disch_then (qspec_then `env_t` mp_tac) >> simp[] >> metis_tac[]) >>
  drule deploy_ctor_formal_var_types >> simp[] >> strip_tac >>
  drule_all deploy_frame_flag_compatibility >> strip_tac >>
  drule_all deploy_ctor_struct_compatibility >> strip_tac >>
  drule_all deploy_ctor_defined_map_agreement >> strip_tac >>
  drule deploy_ctor_static_tables >> strip_tac >>
  drule deploy_frame_storage_var_types >> strip_tac >>
  simp[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  conj_tac >- metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (drule deploy_ctor_method_id >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (drule_at (Pat `env_consistent _ _ _`)
        deploy_frame_bare_global_hashmap_exclusion >> simp[] >>
      disch_then (qspec_then `cenv` mp_tac) >> simp[]) >>
  drule_at (Pat `env_consistent _ _ _`) deploy_ctor_bare_global_bounds >>
  simp[] >> disch_then drule >> simp[] >> metis_tac[]
QED
