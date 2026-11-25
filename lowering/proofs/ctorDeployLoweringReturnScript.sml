(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringReturn
Ancestors
  e2eDeployDefs e2eEntry
  spillWordBounds
  venomPipelineDriverProps
  deploySymSrcData deployRuntimeSuffix
  e2eProducers
  immutableCodeLayout
  deployEntryLayout
  codegenAsmStaticWf
  asmWf
  asmSymSem
  asmDataEnv
  asmFinalizerPrefixStatic
  fnPlanPlaceRevertPostamble finite_map
  valueEncodingDefs ctorDeployLoweringDefs ctorDeployDefs immSectionDead o1PassContract ctorReturnFrame
  accountsRelProps vfmProg
  vyperInterpreter supportedDecls symbolResolve ctorDeployInitcodeAsm
  codegenEncodingWf ctorDeployShape o1PipelineCorrect asmToBytecodeProofs list rich_list venomPipelineData unitLabelMap venomFnScheduleRunner
  venomPipelineRunner venomPipelineDriver vyperCompiler compileVyper asmIR
  ctorDeployLoweringReturnPending ctorDeployDefsReach
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeContractSoundness
  vyperImmutableMetadataFrame
  entryStateRel structFieldsProps vyperTypeDeploymentSoundness moduleLowering compileEnv loweringStateRelDefs

Theorem deploy_ctor_finish_normal[local]:
  ~nr /\
  (res = INL () \/ res = INR (ReturnException NoneV)) ==>
  deploy_ctor_finish tops tx cx nr mut am_c res st =
    INL (finalize_pending_deletions
      (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st
         with sources updated_by CONS (tx.target, [(NONE,tops)])), st.requests)
Proof
  strip_tac >>
  simp[deploy_ctor_finish_def, unlock_if_nr_def, vyperStateTheory.return_def,
       finalize_pending_deletions_def, abstract_machine_from_state_def,
       vfmExecutionTheory.process_deletions_def]
QED

Theorem deploy_ctor_start_nr[local]:
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==> ~nr
Proof
  simp[e2eDeployDefsTheory.deploy_state_rel_def,
    e2eDeployDefsTheory.constructor_args_encode_def, deploy_ctor_start_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem deploy_send_call_value_observations[local]:
  send_call_value mut cx s = (INL (),s') ==>
  send_call_value mut cx
    (s with <|scopes := sc; outcomes := oc; gas_obs := go|>) =
    (INL (),s' with <|scopes := sc; outcomes := oc; gas_obs := go|>)
Proof
  simp[send_call_value_def, transfer_value_def, COND_RATOR,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem deploy_send_call_value_scopes[local]:
  send_call_value mut cx s = (INL (),s') ==> s'.scopes = s.scopes
Proof
  simp[send_call_value_def, transfer_value_def, COND_RATOR,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem deploy_send_call_value_immutables[local]:
  send_call_value mut cx s = (INL (),s') ==> s'.immutables = s.immutables
Proof
  simp[send_call_value_def, transfer_value_def, COND_RATOR,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem deploy_ctor_start_immutables[local]:
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
  es0.immutables = am_c.immutables
Proof
  strip_tac >>
  `~nr` by (drule_all deploy_ctor_start_nr >> simp[]) >>
  gvs[deploy_ctor_start_def, lock_if_nr_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  drule deploy_send_call_value_immutables >> simp[initial_state_def]
QED

Theorem deploy_module_constants_immutables_present[local]:
  !mods am am'.
  evaluate_module_constants cx am addr mods = SOME am' /\
  IS_SOME (ALOOKUP am.immutables addr) ==>
  IS_SOME (ALOOKUP am'.immutables addr)
Proof
  rewrite_tac[evaluate_module_constants_def] >>
  Induct >- simp[evaluate_module_constants_trace_def] >>
  PairCases >> rpt gen_tac >>
  simp[evaluate_module_constants_trace_def] >> pairarg_tac >>
  Cases_on `result` >> gvs[] >>
  rename1 `constants_env_trace _ _ _ _ _ _ = (SOME cenv, observations)` >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `merge_constants addr h0 cenv am` mp_tac) >>
  simp[merge_constants_def] >> metis_tac[]
QED

Theorem deploy_all_constants_immutables_present[local]:
  evaluate_all_constants cx am addr mods = SOME am' /\
  IS_SOME (ALOOKUP am.immutables addr) ==>
  IS_SOME (ALOOKUP am'.immutables addr)
Proof
  simp[evaluate_all_constants_def] >>
  metis_tac[deploy_module_constants_immutables_present]
QED

Theorem deploy_ctor_initial_immutables_present[local]:
  !tops am tx deploy_bc es mut nr body am_c es0.
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) ==>
  ?imms. ALOOKUP es0.immutables tx.target = SOME imms
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_start_immutables >> strip_tac >>
  gvs[deploy_ctor_start_def] >>
  drule deploy_all_constants_immutables_present >> simp[] >>
  Cases_on `ALOOKUP am_c.immutables tx.target` >> simp[]
QED

Theorem deploy_ctor_final_immutables_present[local]:
  !tops am tx deploy_bc es mut nr body am_c es0 gs outcomes res st.
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  eval_stmts (deploy_evaluation_context tops am tx) body
    (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>) = (res,st) ==>
  ?imms. ALOOKUP st.immutables tx.target = SOME imms
Proof
  rpt gen_tac >> strip_tac >> drule_all deploy_ctor_initial_immutables_present >> strip_tac >>
  drule (cj 2 eval_metadata_frame_mutual) >>
  simp[immutable_metadata_frame_def] >> strip_tac >>
  qpat_x_assum `!addr. IS_SOME _ <=> _`
    (qspec_then `tx.target` mp_tac) >> simp[] >>
  Cases_on `ALOOKUP st.immutables tx.target` >> simp[]
QED

Theorem deploy_ctor_initial_immutable_lookup[local]:
  !tops am tx deploy_bc es mut nr stmts am_c es0 vis name ty slot.
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  ?imms tv v. ALOOKUP es0.immutables tx.target = SOME imms /\
    FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
    evaluate_type (type_env tops) ty = SOME tv
Proof
  rpt gen_tac >> strip_tac >>
  `es0.immutables = am_c.immutables` by
    (drule_all deploy_ctor_start_immutables >> simp[]) >>
  gvs[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_constants_ready,
      deploy_ctor_start_def] >>
  `contract_namespaces_ok F [(NONE,tops)] /\
   runtime_art.cta_bare_globals =
     (build_contract_type_artifact F [(NONE,tops)]).cta_bare_globals` by
    (qpat_x_assum `check_contract F _ _ _ = _` mp_tac >>
     simp[check_contract_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[live_artifact_def]) >>
  `FLOOKUP runtime_art.cta_bare_globals (NONE,name) = SOME ty` by
    (simp[] >> irule build_contract_type_artifact_bare_globals_complete >>
     simp[] >> qexistsl [`slot`,`Immutable`,`vis`] >> simp[]) >>
  drule_at (Pat `evaluate_all_constants _ _ _ _ = _`)
    (deploy_constants_setup_bare_globals_ready |> Q.INST
      [`am` |-> `am with exports updated_by CONS (tx.target,[])`] |>
      SRULE []) >>
  disch_then (qspecl_then [`[(tx.target,[(NONE,tops)])]`,
      `am.layouts`,`runtime_art`] mp_tac) >>
  simp[vyperContextTheory.get_tenv_def,
       e2eDeployDefsTheory.deploy_evaluation_context_def,
       initial_evaluation_context_def] >>
  strip_tac >>
  gvs[] >>
  qpat_x_assum `!src id ty'. _ ==> IS_SOME _`
    (qspecl_then [`NONE`,`name`,`ty`] mp_tac) >>
  simp[] >>
  Cases_on `ALOOKUP am_c.immutables tx.target` >>
  simp[vyperStateTheory.get_source_immutables_def] >>
  strip_tac >>
  qpat_x_assum `IS_SOME _` mp_tac >>
  Cases_on `FLOOKUP (case ALOOKUP x NONE of NONE => FEMPTY | SOME imm => imm) name` >> simp[] >>
  rename1 `FLOOKUP _ name = SOME pair` >>
  PairCases_on `pair` >>
  qexistsl [`pair0`,`pair1`] >> simp[] >>
  qpat_x_assum `!src id ty' tv v. _`
    (qspecl_then [`NONE`,`name`,`ty`,`pair0`,`pair1`] mp_tac) >>
  gvs[vyperStateTheory.get_source_immutables_def,
      vyperContextTheory.type_env_all_modules_def,
      vyperContextTheory.type_env_def]
QED

Theorem deploy_ctor_final_immutable_lookup[local]:
  !tops am tx deploy_bc es mut nr stmts am_c es0 gs outcomes res st vis name ty slot.
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  eval_stmts (deploy_evaluation_context tops am tx) stmts
    (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>) = (res,st) /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  ?imms tv v. ALOOKUP st.immutables tx.target = SOME imms /\
    FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
    evaluate_type (type_env tops) ty = SOME tv
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_initial_immutable_lookup >> strip_tac >>
  drule (cj 2 eval_metadata_frame_mutual) >> strip_tac >>
  `get_immutables (deploy_evaluation_context tops am tx) NONE
     (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>) =
   (INL (get_source_immutables NONE imms),
     es0 with <|gas_obs := gs; outcomes := SOME outcomes|>)` by
    simp[vyperStateTheory.get_immutables_def,
      vyperStateTheory.get_address_immutables_def,
      vyperStateTheory.lift_option_type_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, e2eDeployDefsTheory.deploy_evaluation_context_def,
      initial_evaluation_context_def] >>
  drule_all immutable_metadata_frame_lookup >> strip_tac >>
  gvs[vyperStateTheory.get_immutables_def,
      vyperStateTheory.get_address_immutables_def,
      vyperStateTheory.lift_option_type_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      e2eDeployDefsTheory.deploy_evaluation_context_def,
      initial_evaluation_context_def, AllCaseEqs()] >>
  Cases_on `ALOOKUP s''.immutables tx.target` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  metis_tac[]
QED

Theorem deploy_initial_state_scopes[local]:
  (initial_state am sc).scopes = sc /\
  (initial_state am sc with scopes := sc') = initial_state am sc' /\
  (initial_state am sc with <|scopes := sc'; outcomes := oc; requests := rq; gas_obs := go|>) =
    (initial_state am sc' with <|outcomes := oc; requests := rq; gas_obs := go|>)
Proof
  simp[initial_state_def]
QED

Theorem deploy_constructor_prefix_typing[local]:
  !tops am tx deploy_bc es mut nr body am_c es0 gs outcomes.
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  context_well_typed (deploy_evaluation_context tops am tx) ==>
  ?env_body env_after.
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env_body (deploy_evaluation_context tops am tx)
      (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>) /\
    env_body.type_defs = type_env_all_modules [(NONE,tops)] /\
    state_well_typed (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>) /\
    accounts_well_typed (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>).accounts /\
    context_well_typed (deploy_evaluation_context tops am tx) /\
    functions_well_typed (deploy_evaluation_context tops am tx) /\
    call_evaluation_safe (deploy_evaluation_context tops am tx) (int_calls_stmts body)
Proof
  rpt gen_tac >> strip_tac >>
  `~nr` by (drule_all deploy_ctor_start_nr >> simp[]) >>
  gvs[deploy_ctor_start_def, lock_if_nr_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  `es0.scopes = [env]` by
    (drule deploy_send_call_value_scopes >> simp[deploy_initial_state_scopes]) >>
  drule deploy_send_call_value_observations >>
  disch_then (qspecl_then [`[FEMPTY]`,`SOME outcomes`,`gs`] mp_tac) >>
  simp[deploy_initial_state_scopes] >> strip_tac >>
  gvs[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_constants_ready] >>
  `((es0 with <|scopes := [FEMPTY]; outcomes := SOME outcomes; gas_obs := gs|>)
      with scopes := [env]) =
    (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>)` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule_all (checked_constructor_prefix_typing |> Q.INST
    [`mods` |-> `[(NONE,tops)]`, `ts` |-> `tops`, `nr` |-> `F`, `exps` |-> `[]`,
     `cx` |-> `deploy_evaluation_context tops am tx`] |>
    SRULE [GSYM e2eDeployDefsTheory.deploy_evaluation_context_def,
           vyperStateTheory.return_def]) >>
  simp[]
QED

Theorem deploy_context_well_typed[local]:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es ==>
  context_well_typed (deploy_evaluation_context tops am tx)
Proof
  simp[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_constants_ready,
    call_tx_well_typed_def, vyperTypeInvariantsTheory.context_well_typed_def,
    e2eDeployDefsTheory.deploy_evaluation_context_def,
    initial_evaluation_context_def] >> metis_tac[]
QED

Theorem deploy_ctor_final_state_well_typed[local]:
  !tops am tx deploy_bc es mut nr stmts am_c es0 gs outcomes res st.
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  eval_stmts (deploy_evaluation_context tops am tx) stmts
    (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>) = (res,st) /\
  (res = INL () \/ res = INR (ReturnException NoneV)) ==>
  state_well_typed st
Proof
  rpt gen_tac >> strip_tac >>
  `context_well_typed (deploy_evaluation_context tops am tx)` by
    (drule_all deploy_context_well_typed >> simp[]) >>
  drule_all deploy_constructor_prefix_typing >>
  disch_then (qspecl_then [`gs`,`outcomes`] strip_assume_tac) >>
  drule_all vyperTypeStmtSoundnessTheory.eval_stmts_preserves_state_and_accounts_well_typed >>
  simp[]
QED

Theorem deploy_register_constructor_args_fields[local]:
  !args cenv off dsz st cenv' st'.
    compile_register_constructor_args cenv args off dsz st = (cenv',st') ==>
    cenv'.ce_module = cenv.ce_module /\
    cenv'.ce_module_vars = cenv.ce_module_vars
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

Theorem deploy_ctor_environment_fields[local]:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  cenv.ce_module = NONE /\ cenv.ce_is_ctor /\
  cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY)
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> rpt strip_tac >>
  drule deploy_register_constructor_args_fields >> strip_tac >>
  drule entryLocalsTheory.compile_register_constructor_args_fields >> strip_tac >>
  PairCases_on `cf` >>
  gvs[set_constructor_package_target_def, package_constructor_def,
      update_cenv_nonreentrant_def,
      immutableLocationPropsTheory.build_compile_env_module_vars]
QED

Theorem deploy_immutable_locations_unchanged[local]:
  !tops off vars name.
  ~MEM (NONE,name) (FLAT (MAP (vyperTypeContract$toplevel_vtype_keys_toplevel (NONE:num option)) tops)) ==>
  FLOOKUP (add_immutable_locations sft tops off vars) (NONE,name) =
    FLOOKUP vars (NONE,name)
Proof
  Induct >- simp[add_immutable_locations_def] >>
  rpt gen_tac >>
  simp[immutableLocationPropsTheory.immutable_locations_cons] >>
  Cases_on `h` >>
  simp[vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  CASE_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem deploy_immutable_locations_offset[local]:
  !pre post off vars vis name ty slot.
  ALL_DISTINCT (FLAT (MAP (vyperTypeContract$toplevel_vtype_keys_toplevel (NONE:num option))
    (pre ++ VariableDecl vis Immutable name ty slot :: post))) ==>
  FLOOKUP (add_immutable_locations sft
    (pre ++ VariableDecl vis Immutable name ty slot :: post) off vars) (NONE,name) =
    SOME (ImmutableLoc (off + compute_immutables_len sft pre))
Proof
  Induct >-
    (simp[vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def,
          immutableLocationPropsTheory.immutable_locations_cons,
          compute_immutables_len_def] >> rpt strip_tac >>
     simp[deploy_immutable_locations_unchanged, finite_mapTheory.FLOOKUP_UPDATE]) >>
  rpt gen_tac >>
  simp[Once immutableLocationPropsTheory.immutable_len_cons] >>
  pure_rewrite_tac[APPEND, immutableLocationPropsTheory.immutable_locations_cons] >>
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (vyperTypeContract$toplevel_vtype_keys_toplevel (NONE:num option))
    (pre ++ VariableDecl vis Immutable name ty slot :: post)))` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  first_x_assum drule >> disch_then (rewrite_tac o single) >>
  AP_TERM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem deploy_source_variable_names_distinct[local]:
  deploy_source_ok tops am tx ==>
  ALL_DISTINCT (FLAT (MAP (vyperTypeContract$toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  simp[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_constants_ready] >>
  rpt strip_tac >>
  qpat_x_assum `check_contract T _ _ _ = _` mp_tac >>
  simp[vyperTypeContractTheory.check_contract_def,
       vyperTypeContractTheory.contract_namespaces_ok_def,
       vyperTypeContractTheory.contract_keys_def, AllCaseEqs()] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_immutable_offsets[local]:
  !tops am tx rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
  deploy_source_ok tops am tx /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  cenv.ce_module = NONE /\ cenv.ce_is_ctor /\
  (!pre vis name ty slot post.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
    FLOOKUP cenv.ce_module_vars (NONE,name) =
      SOME (ImmutableLoc (compute_immutables_len
        (get_struct_fields (make_struct_fields_map tops)) pre)))
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_environment_fields >> strip_tac >>
  drule deploy_source_variable_names_distinct >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  drule (deploy_immutable_locations_offset |> Q.SPEC `pre` |> Q.SPEC `post` |> SRULE []) >>
  disch_then (qspecl_then
    [`get_struct_fields (make_struct_fields_map
        (pre ++ VariableDecl vis Immutable name ty slot :: post))`, `0`] mp_tac) >>
  simp[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then (rewrite_tac o single)
QED

Theorem deploy_padded_prefix_bytes[local]:
  off + n <= cap ==>
  mem_bytes_at off n (TAKE cap (mem ++ REPLICATE cap 0w)) = mem_bytes_at off n mem
Proof
  rw[valueEncodingDefsTheory.mem_bytes_at_def, listTheory.LIST_EQ_REWRITE,
     listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE,
     listTheory.EL_APPEND_EQN, listTheory.EL_DROP,
     rich_listTheory.EL_REPLICATE] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem deploy_padded_prefix_value[local]:
  off + type_memory_size tv <= cap /\ val_in_memory tv v off mem /\ val_wf tv v ==>
  val_in_memory tv v off (TAKE cap (mem ++ REPLICATE cap 0w))
Proof
  strip_tac >>
  `mem_bytes_at off (type_memory_size tv) mem =
   mem_bytes_at off (type_memory_size tv) (TAKE cap (mem ++ REPLICATE cap 0w))` by
    simp[deploy_padded_prefix_bytes] >>
  drule_all valueMemoryTransportTheory.val_in_memory_transport >> simp[]
QED

Theorem deploy_padded_immutable_section[local]:
  immutables_rel cenv addr NONE T st before /\
  ALOOKUP st.immutables addr = SOME imms /\
  (!pre vis name ty slot post.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
    FLOOKUP cenv.ce_module_vars (NONE,name) =
      SOME (ImmutableLoc (compute_immutables_len
        (get_struct_fields (make_struct_fields_map tops)) pre)) /\
    ?tv v. FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
      val_wf tv v /\ type_memory_size tv =
        type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty) ==>
  immutables_section_rel tops imms
    (TAKE (imm_len tops) (before.vs_memory ++ REPLICATE (imm_len tops) 0w))
Proof
  strip_tac >> simp[immutableSectionRelTheory.immutables_section_rel_def, imm_len_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!pre vis name ty slot post. _`
    (qspecl_then [`pre`,`vis`,`name`,`ty`,`slot`,`post`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >> strip_tac >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >>
  simp[immutables_rel_def] >> disch_then drule_all >> strip_tac >>
  `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
     type_memory_size tv <=
   compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops` by
    fs[compute_immutables_len_append, compute_immutables_len_def] >>
  gvs[] >> conj_tac
  >- (irule deploy_padded_prefix_value >> simp[]) >>
  simp[deploy_padded_prefix_bytes]
QED

Theorem deploy_state_immutable_val_wf[local]:
  state_well_typed st /\ ALOOKUP st.immutables addr = SOME imms /\
  FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
  val_wf tv v
Proof
  strip_tac >>
  `imms_well_typed imms` by
    (gvs[vyperTypeInvariantsTheory.state_well_typed_def, EVERY_MEM] >>
     drule alistTheory.ALOOKUP_MEM >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  gvs[vyperTypeInvariantsTheory.imms_well_typed_def,
      vyperStateTheory.get_source_immutables_def] >>
  Cases_on `ALOOKUP imms NONE` >> gvs[] >>
  `value_has_type tv v` by metis_tac[] >>
  metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]
QED

Theorem deploy_source_type_names_distinct[local]:
  deploy_source_ok tops am tx ==>
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))
Proof
  simp[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_constants_ready] >>
  rpt strip_tac >>
  qpat_x_assum `check_contract T _ _ _ = _` mp_tac >>
  simp[check_contract_def, contract_namespaces_ok_def, contract_keys_def,
       AllCaseEqs()] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_immutable_section[local]:
  !tops am tx deploy_bc es mut nr body source_body am_c es0 gs outcomes res st
   rpolicy runtime_bc dunit cenv nkey ut imm exit_lbl sa sb sj st_exit
   st_epilogue st_final func before.
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,source_body,am_c,es0) /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  eval_stmts (deploy_evaluation_context tops am tx) source_body
    (es0 with <|gas_obs := gs; outcomes := SOME outcomes|>) = (res,st) /\
  (res = INL () \/ res = INR (ReturnException NoneV)) /\
  immutables_rel cenv tx.target NONE T (st with scopes := []) before ==>
  ?imms. ALOOKUP st.immutables tx.target = SOME imms /\
    immutables_section_rel tops imms
      (TAKE (imm_len tops) (before.vs_memory ++ REPLICATE (imm_len tops) 0w))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all deploy_ctor_final_immutables_present >> strip_tac >>
  drule_all deploy_ctor_immutable_offsets >> strip_tac >>
  `state_well_typed st` by
    metis_tac[deploy_ctor_final_state_well_typed] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  drule deploy_source_type_names_distinct >> strip_tac >>
  qexists `imms` >> simp[] >>
  irule deploy_padded_immutable_section >>
  qexistsl [`tx.target`,`cenv`,`st with scopes := []`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by
    (simp[MEM_APPEND] >> metis_tac[]) >>
  drule_all deploy_ctor_final_immutable_lookup >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule deploy_state_immutable_val_wf >> metis_tac[]) >>
  drule_at (Pat `evaluate_type _ _ = _`) evaluated_type_mem_bytes >> simp[]
QED

Theorem deploy_snapshot_observations[local]:
  state_rel H func cenv (deploy_evaluation_context tops am tx)
    (st with scopes := []) before ==>
  (!a. a <> tx.target ==>
    lookup_account a before.vs_accounts = lookup_account a st.accounts) /\
  (lookup_account tx.target before.vs_accounts) with code := [] =
    (lookup_account tx.target st.accounts) with
      <|code := []; storage := (lookup_account tx.target before.vs_accounts).storage|> /\
  storage_agree
    (storage_dead H F
      (lookup_account tx.target st.accounts).storage)
    (lookup_account tx.target st.accounts).storage
    (lookup_account tx.target before.vs_accounts).storage /\
  transient_agree H (deploy_evaluation_context tops am tx).txn.target st.tStorage before.vs_transient /\
  logs_correspond (compiled_event_info tops) (type_env tops)
    tx.target st.logs before.vs_logs /\
  LIST_REL (request_agree H (deploy_evaluation_context tops am tx).txn.target)
    st.requests before.vs_requests
Proof
  strip_tac >>
  drule accountsRelPropsTheory.state_rel_accounts >>
  simp[accounts_agree_def, e2eDeployDefsTheory.deploy_evaluation_context_def,
       initial_evaluation_context_def] >> strip_tac >>
  `log_entry_equiv cenv (deploy_evaluation_context tops am tx).txn.target = $=` by
    simp[FUN_EQ_THM, log_entry_equiv_def] >>
  `st.logs = before.vs_logs` by
    (qpat_x_assum `state_rel _ _ _ _ _ _` mp_tac >>
     simp[state_rel_def, logs_rel_def, LIST_REL_eq] >> metis_tac[]) >>
  `LIST_REL (request_agree H (deploy_evaluation_context tops am tx).txn.target)
     st.requests before.vs_requests` by
    (qpat_x_assum `state_rel _ _ _ _ _ _` mp_tac >>
     simp[state_rel_def] >> metis_tac[]) >>
  `log_entry_corresponds (compiled_event_info tops) (type_env tops) tx.target = $=` by
    simp[FUN_EQ_THM, e2eDefsTheory.log_entry_corresponds_concrete_event] >>
  simp[vfmStateTheory.lookup_account_def, e2eDefsTheory.logs_correspond_def,
       e2eDefsTheory.log_entry_corresponds_concrete_event, LIST_REL_eq] >>
  fs[e2eDeployDefsTheory.deploy_evaluation_context_def, initial_evaluation_context_def] >>
  qpat_x_assum `_ with storage := _ = _` (mp_tac o GSYM) >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem deploy_snapshot_immutables[local]:
  state_rel H func cenv (deploy_evaluation_context tops am tx)
    (st with scopes := []) before /\
  cenv.ce_module = NONE /\ cenv.ce_is_ctor ==>
  immutables_rel cenv tx.target NONE T (st with scopes := []) before
Proof
  strip_tac >>
  gvs[state_rel_def, e2eDeployDefsTheory.deploy_evaluation_context_def,
       initial_evaluation_context_def]
QED

Theorem deploy_lowering_runtime_suffix[local]:
  run_deploy_lowering has_constructor rpolicy bytes immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  ?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem deploy_unit_runtime_suffix[local]:
  lower_vyper_deploy_unit tops rpolicy bytes = SOME unit ==>
  ?pre. unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]
Proof
  simp[lower_vyper_deploy_unit_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule deploy_lowering_runtime_suffix >> simp[]
QED

Theorem deploy_phase_assembly_suffix[local]:
  deploy_phases policy tops (deploy_bc,bytes)
    (rpolicy,dunit,dout,prog,cplan) ==>
  ?pre. prog = pre ++ [AsmDataHeader "runtime_begin";
                       AsmDataItem bytes; AsmDataHeader "code_end"]
Proof
  simp[deploy_phases_def] >> strip_tac >>
  drule deploy_unit_runtime_suffix >> strip_tac >>
  `?pre. dout.po_unit.cu_data_segment = pre ++
    [<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>]` by
    (gvs[o1PipelineCorrectTheory.o1_pipeline_def] >>
     metis_tac[deploy_pipeline_runtime_suffix]) >>
  gvs[data_segment_asm_def, data_section_asm_def,
      FLAT_APPEND, MAP_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Triviality deploy_final_label_bound:
  asm_encoding_wf prog /\
  FLOOKUP (SND (compute_label_offsets prog)) label = SOME n ==> n < 65536
Proof
  Cases_on `compute_label_offsets prog` >>
  rw[asm_encoding_wf_def, symbol_size_def] >>
  `LENGTH (encode_num_bytes n) <= 2` by
    (qpat_assum `!lbl off. FLOOKUP _ lbl = SOME off ==> _`
       (qspecl_then [`label`, `n`] mp_tac) >> simp[]) >>
  qspecl_then [`2`, `n`] mp_tac encode_num_bytes_length_bound >>
  simp[EVAL ``256 ** 2 : num``]
QED

(* The runtime data segment moves with the finalized assembly's data suffix. *)
Triviality deploy_relocated_data_offset:
  asm_static_wf prog /\ MEM (AsmDataHeader label) prog ==>
  FLOOKUP (lo_reloc prog prog') label =
    FLOOKUP (SND (compute_label_offsets prog')) label
Proof
  strip_tac >>
  `~MEM (AsmLabel label) prog` by metis_tac[asm_static_wf_def] >>
  simp[lo_reloc_def, FLOOKUP_FUNION, FLOOKUP_DRESTRICT]
QED

Theorem deploy_relocated_data_layout:
  deploy_phases policy tops (deploy_bc,bytes)
    (rpolicy,dunit,dout,prog,cplan) /\ deploy_source_ok tops am tx /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' ==>
  FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog')) /\
  LENGTH (assemble prog') < 65536 /\
  ?off. FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
        DROP off (assemble prog') = bytes /\
        off <= LENGTH (assemble prog') /\ off < dimword(:256)
Proof
  strip_tac >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy bytes = SOME dunit /\
   o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog` by fs[deploy_phases_def] >>
  `unit_shape_ok dout.po_unit` by
    metis_tac[run_venom_pipeline_output_shape] >>
  `codegen_ready dout.po_unit.cu_context` by
    metis_tac[o1PipelineCorrectTheory.o1_pipeline_def,
              run_venom_pipeline_success_boundary] >>
  `sym_unit_static_ok dout.po_unit` by
    (irule o1_pipeline_sym_unit_static_ok >>
     qexistsl_tac [`rpolicy`, `dunit`] >>
     simp[] >> conj_tac
     >- (strip_tac >> drule lower_vyper_deploy_unit_runtime_section >>
         strip_tac >> simp[EXISTS_MEM] >>
         qexists_tac `<|ds_label := "runtime_begin"; ds_items := [DataBytes bytes]|>` >>
         simp[])
     >> drule lower_vyper_deploy_unit_data_bytes >> simp[]) >>
  `asm_static_wf prog` by metis_tac[codegen_asm_static_wf] >>
  `asm_static_wf prog' /\ FILTER is_data_inst prog' = FILTER is_data_inst prog` by
    (qspecl_then [`fin`, `rpolicy`, `prog`, `prog'`, `[]`]
       mp_tac finalizer_prefix_static >> simp[]) >>
  drule deploy_phase_assembly_suffix >> strip_tac >>
  `FLOOKUP (lo_reloc prog prog') "runtime_begin" =
    FLOOKUP (SND (compute_label_offsets prog')) "runtime_begin"` by
    (irule deploy_relocated_data_offset >> simp[MEM_APPEND]) >>
  `FLOOKUP (lo_reloc prog prog') "code_end" =
    FLOOKUP (SND (compute_label_offsets prog')) "code_end"` by
    (irule deploy_relocated_data_offset >> simp[MEM_APPEND]) >>
  `?prefix. prog' = prefix ++
    [AsmDataHeader "runtime_begin"; AsmDataItem bytes; AsmDataHeader "code_end"]` by
    (qspec_then `prog'` mp_tac asm_data_split >>
     impl_tac >- fs[asm_static_wf_def] >>
     disch_then (qx_choose_then `n` strip_assume_tac) >>
     qexists_tac `TAKE n prog' ++ FILTER is_data_inst pre` >>
     `FILTER is_data_inst (TAKE n prog') = []` by
       simp[FILTER_EQ_NIL] >>
     `FILTER is_data_inst (DROP n prog') = DROP n prog'` by
       simp[FILTER_EQ_ID] >>
     `FILTER is_data_inst prog' = DROP n prog'` by
       (qspecl_then [`n`, `prog'`]
          (fn split =>
            qpat_assum `FILTER _ (TAKE _ _) = []` (fn head =>
              qpat_assum `FILTER _ (DROP _ _) = DROP _ _` (fn tail =>
                ACCEPT_TAC (SYM (SIMP_RULE (srw_ss ()) [FILTER_APPEND, head, tail]
                  (Q.AP_TERM `FILTER is_data_inst` split)))))) TAKE_DROP) >>
     `DROP n prog' = FILTER is_data_inst pre ++
       [AsmDataHeader "runtime_begin"; AsmDataItem bytes; AsmDataHeader "code_end"]` by
       (qpat_assum `FILTER is_data_inst prog' = DROP n prog'` (fn split =>
          qpat_assum `FILTER is_data_inst prog' = FILTER is_data_inst prog` (fn preserved =>
            qpat_assum `prog = _ ++ _` (fn shape =>
              ACCEPT_TAC (SIMP_RULE (srw_ss ()) [shape, FILTER_APPEND, is_data_inst_def]
                (TRANS (SYM split) preserved)))))) >>
     qpat_assum `DROP n prog' = _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[TAKE_DROP, APPEND_ASSOC]) >>
  qabbrev_tac `off = SUM (MAP asm_inst_size prefix)` >>
  `FLOOKUP (SND (compute_label_offsets prog')) "runtime_begin" = SOME off` by
    fs[Abbr `off`, deploy_runtime_suffix_offset] >>
  `asm_encoding_wf prog'` by fs[asm_static_wf_def] >>
  `FLOOKUP (SND (compute_label_offsets prog')) "code_end" =
    SOME (LENGTH (assemble prog'))` by
    (irule immutable_code_end_length >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `prefix ++ [AsmDataHeader "runtime_begin"; AsmDataItem bytes]` >>
     simp[GSYM APPEND_ASSOC]) >>
  `LENGTH (assemble prog') < 65536` by (drule_all deploy_final_label_bound >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexists_tac `off` >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_assum `prog' = prefix ++ _` (fn shape =>
        qpat_assum `asm_encoding_wf prog'` (fn enc =>
          mp_tac (REWRITE_RULE [shape] enc) >>
          simp_tac (srw_ss ()) [shape, Abbr `off`, deploy_runtime_suffix_slice]))) >>
  `off <= LENGTH (assemble prog')` by
    (drule deploy_encoding_total_length >> strip_tac >>
     qspec_then `prog'` strip_assume_tac compute_label_offsets_bound >>
     metis_tac[]) >>
  simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >> decide_tac
QED

Triviality deploy_runtime_snapshot_slice:
  deploy_state_rel tops (assemble prog') am tx es /\
  raw_variant vs.vs_initial_fmp vs
    (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
  FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
  off < dimword(:256) /\ off <= LENGTH (assemble prog') /\
  DROP off (assemble prog') = bytes /\
  snap.vs_code = vs.vs_code /\ snap.vs_labels = vs.vs_labels /\
  FLOOKUP snap.vs_labels "runtime_begin" = SOME codepos ==>
  TAKE (LENGTH bytes)
    (DROP (w2n codepos) snap.vs_code ++ REPLICATE (LENGTH bytes) 0w) = bytes
Proof
  strip_tac >>
  `snap.vs_code = (FST (HD es.contexts)).msgParams.code /\
   FLOOKUP snap.vs_labels "runtime_begin" = SOME (n2w off)` by
    (qpat_assum `raw_variant _ _ _` (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     disch_then (mp_tac o Q.AP_TERM `\s. (s.vs_code,s.vs_labels)`) >>
     simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def,
          entry_venom_state_frame_fields] >>
     strip_tac >>
     qpat_assum `FLOOKUP snap.vs_labels "runtime_begin" = SOME codepos` mp_tac >>
     qpat_assum `snap.vs_labels = _` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `n2w o_f _ = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     qpat_assum `FLOOKUP (lo_reloc _ _) "runtime_begin" = _`
       (fn th => simp_tac (srw_ss ()) [FLOOKUP_o_f, th])) >>
  `codepos = n2w off` by metis_tac[optionTheory.SOME_11] >>
  `w2n codepos = off` by simp[wordsTheory.w2n_n2w] >>
  `?args_bytes. snap.vs_code = assemble prog' ++ args_bytes` by
    (fs[deploy_state_rel_def] >> qexists_tac `args_bytes` >>
     qpat_assum `(FST (HD es.contexts)).msgParams.code = vs.vs_code` mp_tac >>
     qpat_assum `es.contexts = _` (fn th => simp[th]) >> gvs[]) >>
  qpat_assum `snap.vs_code = assemble prog' ++ args_bytes`
    (fn th => PURE_REWRITE_TAC [th]) >>
  qpat_assum `w2n codepos = off` (fn th => PURE_REWRITE_TAC [th]) >>
  `DROP off (assemble prog' ++ args_bytes) = bytes ++ args_bytes` by
    (qspecl_then [`off`, `assemble prog'`] mp_tac DROP_APPEND1 >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qspec_then `args_bytes` SUBST1_TAC) >> asm_rewrite_tac []) >>
  qpat_assum `DROP off (assemble prog' ++ args_bytes) = _`
    (fn th => PURE_REWRITE_TAC [th, GSYM APPEND_ASSOC, TAKE_LENGTH_APPEND]) >> REFL_TAC
QED

Theorem deploy_ctor_start_static[local]:
  !tops am tx mut nr body am_c es0.
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) ==>
  am_c.sources = am.sources /\ am_c.layouts = am.layouts
Proof
  rpt gen_tac >> simp[deploy_ctor_start_def] >> rpt strip_tac >>
  drule vyperTypeDeploymentMachineTheory.evaluate_all_constants_preserves_machine_static_components >>
  simp[]
QED

Theorem deploy_result_context_agree[local]:
  am_c.sources = am.sources /\ am_c.layouts = am.layouts ==>
  accounts_agree H
    (initial_evaluation_context ((tx.target,[(NONE,tops)])::am_c.sources) am_c.layouts tx NONE).txn.target =
    accounts_agree H (deploy_evaluation_context tops am tx).txn.target /\
  transient_agree H
    (initial_evaluation_context ((tx.target,[(NONE,tops)])::am_c.sources) am_c.layouts tx NONE).txn.target =
    transient_agree H (deploy_evaluation_context tops am tx).txn.target /\
  request_agree H
    (initial_evaluation_context ((tx.target,[(NONE,tops)])::am_c.sources) am_c.layouts tx NONE).txn.target =
    request_agree H (deploy_evaluation_context tops am tx).txn.target
Proof
  strip_tac >> irule accountsRelPropsTheory.agree_cx_cong >>
  simp[initial_evaluation_context_def, e2eDeployDefsTheory.deploy_evaluation_context_def]
QED

(* A constructor that finishes normally (falls off its end or returns)
   halts returning the runtime code and the immutables section, with the
   source's accounts, transient storage and logs. *)
Theorem deploy_ctor_return:
  !policy tops runtime_bc rpolicy dunit dout prog prog' cplan off am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut source_body am_c es0 gs res st final H.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
    off < dimword(:256) /\ off <= LENGTH (assemble prog') /\
    DROP off (assemble prog') = runtime_bc /\
    raw_variant vs.vs_initial_fmp vs
      (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, source_body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) source_body
      (es0 with <| gas_obs := gs; outcomes := SOME vs.vs_outcomes |>) =
      (res, st) /\
    (res = INL () \/ res = INR (ReturnException NoneV)) /\
    constructor_return_q H func cenv (deploy_evaluation_context tops am tx) (LENGTH runtime_bc)
      (imm_len tops) nr nkey NoneV (st with scopes := []) (Halt final) /\
    final.vs_code = vs.vs_code /\ final.vs_labels = vs.vs_labels ==>
    deploy_venom_result_rel H tops runtime_bc tx
      (deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx) nr mut am_c res st) (Halt final)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~nr` by (drule_all deploy_ctor_start_nr >> simp[]) >>
  `deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx) nr mut am_c res st =
   INL (finalize_pending_deletions
     (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st
       with sources updated_by CONS (tx.target,[(NONE,tops)])),st.requests)` by
    metis_tac[deploy_ctor_finish_normal] >>
  qpat_x_assum `constructor_return_q _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[constructor_return_q_def] >> strip_tac >>
  `TAKE (LENGTH runtime_bc)
      (DROP (w2n codepos) before.vs_code ++ REPLICATE (LENGTH runtime_bc) 0w) = runtime_bc` by
    (irule deploy_runtime_snapshot_slice >> metis_tac[]) >>
  drule_all deploy_ctor_immutable_offsets >> strip_tac >>
  drule_all deploy_snapshot_immutables >> strip_tac >>
  `?imms. ALOOKUP st.immutables tx.target = SOME imms /\
    immutables_section_rel tops imms
      (TAKE (imm_len tops) (before.vs_memory ++ REPLICATE (imm_len tops) 0w))` by
    metis_tac[deploy_ctor_immutable_section] >>
  drule deploy_snapshot_observations >> strip_tac >>
  drule accountsRelPropsTheory.state_rel_accounts >> strip_tac >>
  `before.vs_pending_deletions = st.pending_deletions` by
    fs[] >>
  drule deploy_ctor_start_static >> strip_tac >>
  drule_all deploy_result_context_agree >>
  disch_then (qspecl_then [`tx`,`tops`,`H`] strip_assume_tac) >>
  qpat_x_assum `deploy_phases _ _ _ _` kall_tac >>
  qpat_x_assum `deploy_source_ok _ _ _` kall_tac >>
  qpat_x_assum `deploy_state_rel _ _ _ _ _` kall_tac >>
  qpat_x_assum `raw_variant _ _ _` kall_tac >>
  qpat_x_assum `deploy_ctor_code _ _ _ _ _` kall_tac >>
  qpat_x_assum `deploy_ctor_start _ _ _ _` kall_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` kall_tac >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `state_rel _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!pre vis name ty slot post. _` kall_tac >>
  simp[deploy_venom_result_rel_def, finalize_pending_deletions_def,
       abstract_machine_from_state_def,
       e2eDefsTheory.account_immutables_def] >>
  gvs[initial_evaluation_context_def,
      e2eDeployDefsTheory.deploy_evaluation_context_def] >>
  `accounts_agree H tx.target
    (process_deletions st.pending_deletions st.accounts)
    (process_deletions st.pending_deletions before.vs_accounts)` by
    (irule (SRULE [e2eDeployDefsTheory.deploy_evaluation_context_def,
      initial_evaluation_context_def]
      (Q.SPEC `deploy_evaluation_context tops am tx`
        accountsRelPropsTheory.accounts_agree_process_deletions)) >> fs[]) >>
  Cases_on `MEM tx.target st.pending_deletions`
  >- (`!a. process_deletions st.pending_deletions
        (update_account tx.target a before.vs_accounts) =
        process_deletions st.pending_deletions before.vs_accounts` by
        (gen_tac >> irule accountsRelPropsTheory.process_deletions_update_mem >>
         fs[]) >> fs[]) >>
  `(lookup_account tx.target before.vs_accounts).code =
   (lookup_account tx.target st.accounts).code` by
    (qpat_x_assum `accounts_agree H tx.target st.accounts before.vs_accounts` mp_tac >>
     simp[accounts_agree_def, vfmStateTheory.lookup_account_def,
          vfmStateTheory.account_state_component_equality]) >>
  `!A a. update_account a (lookup_account a A) A = A` by
    rw[FUN_EQ_THM, vfmStateTheory.update_account_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  `lookup_account tx.target before.vs_accounts with
     code := (lookup_account tx.target st.accounts).code =
   lookup_account tx.target before.vs_accounts` by
    simp[vfmStateTheory.account_state_component_equality] >>
  fs[vfmProgTheory.lookup_account_process_deletions_other]
QED
