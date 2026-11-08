(*
 * S3 helper: loweringRuntimeCorrect's external_body_source_ok at any gas
 * observations, as the counted body judgment's gas_admissible asks of the
 * called body.  (S1's restated twin, at es0 with gas_obs := gs, may
 * replace it when the branches merge.)
 *)
Theory loweringMemBodySourceGas
Ancestors
  stmtSimProps stmtSimDefs gasContext supportedDecls
  list pair finite_map
  e2eDefs supportedProgram loweringRuntimeCorrect
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperTypeStmtSoundness vyperTypeEvalSoundness vyperTypeExprSoundness
  vyperTypeContractFunction vyperTypeContractSoundness
  vyperTypeContractContext vyperTypeContract vyperTypeExternalDefaults
  vyperTypeInitialState vyperTypeBindArguments vyperTypeInvariants
  vyperInterpreter vyperState vyperContext

val _ = Parse.hide "body";

(* The checked typing of the selected external body (PR #1081's
   external_selected_body_typing). *)
Theorem external_body_typing_gas_mem[local]:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, F, args, [], ret, fbody) ==>
  ?art env_t env'.
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    checked_contract_runtime_ready art [(NONE,tops)] am tx /\
    env_t.current_src = NONE /\
    env_t.type_defs = get_tenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    env_t.fn_sigs = art.cta_fn_sigs /\
    env_t.bare_globals = art.cta_bare_globals /\
    env_t.bare_global_assignable = art.cta_bare_global_assignable /\
    env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_t.flag_members = art.cta_flag_members /\
    type_stmts env_t ret fbody = SOME env' /\
    (!id ty. MEM (id,ty) args ==>
      FLOOKUP env_t.var_types id = SOME ty /\
      IS_SOME (FLOOKUP env_t.var_assignable id)) /\
    (!n ty. FLOOKUP env_t.var_types n = SOME ty ==> MEM (n,ty) args) /\
    (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
      ?ty. MEM (n,ty) args) /\
    stmts_no_control_escape fbody /\
    call_evaluation_safe
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (int_calls_stmts fbody)
Proof
  strip_tac >>
  `?raw. MEM (FunctionDecl External mut F raw tx.function_name args [] ret
                fbody) tops` by
    (irule entryStateRelTheory.lookup_function_external_decl >> simp[] >>
     qexists `tops` >>
     gvs[supported_program_def, supported_declaration_headers_def]) >>
  gvs[source_typing_ok_def, source_deployment_rel_def] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `External <> Deploy` by simp[] >>
  `ALOOKUP [(NONE,tops)] NONE = SOME tops` by simp[] >>
  drule checked_function_body_typing_package >>
  simp[] >> disch_then drule >> simp[] >>
  strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
     External mut F args [] ret fbody` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl [`tx.function_name`, `raw`] >> simp[]) >>
  conj_tac >- gvs[check_function_body_def] >>
  drule checked_explicit_external_body_call_evaluation_safe >>
  simp[] >> disch_then drule >> simp[]
QED

(* Moving the call value changes only the accounts. *)
Theorem send_call_value_frame_gas_mem[local]:
  send_call_value mut cx st = (res,st') ==>
  st' with accounts := st.accounts = st
Proof
  rw[send_call_value_def, transfer_value_def, bind_def, ignore_bind_def,
     get_accounts_def, check_def, assert_def, update_accounts_def,
     return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

(* The body's start state is well typed (PR #1081's
   external_body_prefix_state). *)
Theorem external_body_prefix_state_gas_mem[local]:
  machine_well_typed am /\
  bind_arguments tenv args vals = SOME env /\
  send_call_value mut cx
    (initial_state am [env] with <|outcomes := SOME os; requests := []|>) =
    (INL (),es0) ==>
  es0.scopes = [env] /\ es0.immutables = am.immutables /\
  state_well_typed es0 /\ accounts_well_typed es0.accounts
Proof
  strip_tac >>
  `scope_well_typed env` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `accounts_well_typed es0.accounts` by
    (irule send_call_value_accounts_well_typed_c53 >>
     goal_assum (drule_at Any) >>
     simp[initial_state_accounts_well_typed_simple]) >>
  drule send_call_value_frame_gas_mem >>
  simp[evaluation_state_component_equality, initial_state_def] >>
  strip_tac >> gvs[state_well_typed_def, machine_well_typed_def]
QED

(* The typing environment is consistent with the body's start state (PR
   #1081's external_selected_env_consistent). *)
Theorem external_env_consistent_gas_mem[local]:
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  checked_contract_runtime_ready art [(NONE,tops)] am tx /\
  env_t.current_src = NONE /\
  env_t.type_defs = get_tenv
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  env_t.fn_sigs = art.cta_fn_sigs /\
  env_t.bare_globals = art.cta_bare_globals /\
  env_t.bare_global_assignable = art.cta_bare_global_assignable /\
  env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env_t.flag_members = art.cta_flag_members /\
  (!id ty. MEM (id,ty) args ==>
    FLOOKUP env_t.var_types id = SOME ty /\
    IS_SOME (FLOOKUP env_t.var_assignable id)) /\
  (!n ty. FLOOKUP env_t.var_types n = SOME ty ==> MEM (n,ty) args) /\
  (!n b. FLOOKUP env_t.var_assignable n = SOME b ==>
    ?ty. MEM (n,ty) args) /\
  bind_arguments (type_env tops) args vals = SOME env /\
  es0.scopes = [env] /\ es0.immutables = am.immutables ==>
  env_consistent env_t
    (initial_evaluation_context am.sources am.layouts tx NONE) es0
Proof
  strip_tac >> gvs[checked_contract_runtime_ready_def] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art [(NONE,tops)] NONE` >>
      rpt (conj_tac >-
        simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >> simp[])
  >- (`es0 with scopes := [env] = es0` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (SUBST1_TAC o GSYM) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env tops`, `vals`] >>
      simp[get_tenv_def, initial_evaluation_context_def,
           type_env_all_modules_def, type_env_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def] >> rw[] >>
      qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
      simp[immutables_ready_def] >> strip_tac >>
      first_x_assum drule_all >> simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`id_str`, `tv`, `v`] mp_tac) >> simp[])
QED

(* The source context is well typed (PR #1081's
   external_source_context_typed). *)
Theorem external_context_typed_gas_mem[local]:
  source_typing_ok tops am tx ==>
  context_well_typed
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  functions_well_typed
    (initial_evaluation_context am.sources am.layouts tx NONE)
Proof
  rw[source_typing_ok_def]
  >- gvs[call_tx_well_typed_def, context_well_typed_def,
         initial_evaluation_context_def] >>
  irule check_contract_functions_well_typed_initial >>
  gvs[checked_contract_runtime_ready_def] >> goal_assum (drule_at Any) >>
  simp[]
QED

(* external_body_source_ok at any gas observations: the body's result is
   one a statement fragment admits.  The proof is PR #1081's fixed-run
   external_body_source_ok, at es0 with gas_obs := gs: the typing
   invariants don't mention gas_obs. *)
Theorem external_body_source_ok_gas_mem:
  !tops am tx ret vs mut args fbody env es0.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    gas_admissible
      (eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
         fbody)
      (stmt_res_ok NoLoop) es0
Proof
  rpt strip_tac >>
  drule_all external_body_typing_gas_mem >> strip_tac >>
  `machine_well_typed am` by gvs[source_typing_ok_def] >>
  drule_all external_body_prefix_state_gas_mem >> strip_tac >>
  drule_all external_env_consistent_gas_mem >> strip_tac >>
  drule external_context_typed_gas_mem >> strip_tac >>
  rw[gas_admissible_def] >>
  `no_type_error_eval
     (eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
        fbody (es0 with gas_obs := gs))` by
    (irule eval_stmts_no_type_error >> simp[] >> metis_tac[]) >>
  gvs[no_type_error_eval_def] >>
  Cases_on `res` >> simp[stmt_res_ok_def] >>
  drule_all stmts_no_control_escape_eval_stmts_no_loop_control >>
  strip_tac >> rename1 `INR y` >> Cases_on `y` >> gvs[stmt_res_ok_def] >>
  rename1 `Error e` >> Cases_on `e` >>
  gvs[stmt_res_ok_def, no_type_error_result_def]
QED
