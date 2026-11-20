(* Assemble dispatched calls once the selected entry reaches the body. *)
Theory dispatchedCallAssembly
Ancestors
  dispatchedArgsBind dispatchedEntryValueRevert fallbackEntryEndpoint
  loweringRuntimeCorrect gasShadowRunLowering loweringShapeProps
  gasShadowUnit sourceUnitExecution dispatchedSelectedEndpoint
  defaultDispatchFacts externalReturnPackage runtimeFallbackPackageEnvironment
  externalEntryValueRevert vyperLoweringCorrect

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >> conj_asm2_tac
  >- (simp[source_unit_execution_correct_def,
           source_unit_execution_correct_at_def] >>
      qpat_x_assum `?marks. _` (qx_choose_then `marks` assume_tac) >>
      qexistsl_tac [`marks`, `shadow_unit.cu_context`] >> simp[]) >>
  drule_all dispatched_vyper_call_bind >>
  disch_then (qx_choose_then `env` assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>)`
    ["res es0"] >>
  reverse (namedCases_on `res` ["u", "e"])
  >- (qexists_tac `[]` >>
      `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
        (Cases_on `classify_functions tops` >> PairCases_on `r` >>
         drule supported_program_no_external_defaults >> simp[] >> strip_tac >>
         drule_at (Pat `classify_functions _ = _`) runtime_gas_shadow_unit_exists >>
         disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
         simp[gas_shadow_unit_def]) >>
      drule_all external_entry_value_revert_dispatched_with_nr >> simp[]) >>
  Cases_on `u` >>
  qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]
QED
*)
Theorem dispatched_call_correct_from_value_success:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    (!env es0. bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
         tops ret am tx unit vs) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  cheat
QED

Theorem dispatched_call_correct_from_selected_endpoint:
  !tops rpolicy unit shadow_unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    (!env es0. tx.function_name <> "__default__" /\
       bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  rpt gen_tac >> strip_tac >>
  irule dispatched_call_correct_from_value_success >>
  asm_rewrite_tac [] >> conj_tac
  >- (qexists_tac `rpolicy` >> asm_rewrite_tac []) >>
  qexistsl_tac [`args`, `fbody`, `mut`, `F`] >>
  asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
  `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)` by
    (Cases_on `tx.function_name = "__default__"`
     >- (drule_all dispatched_entry_endpoint_default >> simp[]) >>
     qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]) >>
  drule_all runtime_body_joint_from_start_with_shadow >> simp[]
QED

Triviality fallback_runtime_body_start:
  runtime_fallback_body_start tops rpolicy
    (lbl,cenv,[],4,pay,nr,nkey,ut,iv,fbody,rt) st ==>
  runtime_entry_body_start tops rpolicy
    ("fn___default__",cenv,[],4,pay,nr,nkey,ut,iv,fbody,rt) st
Proof
  simp[runtimeBodyStartDefsTheory.runtime_entry_body_start_def,
       runtimeBodyStartDefsTheory.runtime_fallback_body_start_def]
QED

(* The source body uses the same package environment as the actual fallback. *)
val fallback_source_package_tac =
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,T,args,[],ret,fbody)` by fs[] >>
  `args = []` by metis_tac[default_fallback_no_args] >>
  drule_all default_fallback_classified >>
  strip_tac >>
  qabbrev_tac `rr = lookup_raw_return_or_F (NONE:num option) "__default__" External tops` >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[entryStateRelTheory.source_typing_ok_external_names_distinct] >>
  drule_all default_fallback_lookup_decl >> strip_tac >>
  `subst_consts_stmts (module_consts_env tops []) fbody = fbody` by
    (drule_all checked_supported_external_subst >>
     simp[constSubstTheory.subst_consts_fn_def]) >>
  `set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot)
      (SOME (mut,T,rr,"__default__",[],([]:expr list),ret,fbody))) =
      SOME (cenv,mut = Payable,T,global_nonreentrant_slot,T,mut = View,fbody,rt)` by
    (qpat_assum `runtime_fallback_body_start _ _ _ _`
      (mp_tac o REWRITE_RULE [runtimeBodyStartDefsTheory.runtime_fallback_body_start_def]) >>
     rpt strip_tac >> gvs[]) >>
  drule fallback_empty_source_external_package >> strip_tac >>
  `compile_register_positional_args cenv [] 4 sa = (cenv,sa)` by
    simp[moduleLoweringTheory.compile_register_positional_args_def, compileEnvTheory.comp_return_def] >>
  drule_then assume_tac fallback_runtime_body_start;

val registered_lock_body_tac =
  drule_all nonreentrantEntryPathTheory.guarded_body_code_from_registration >>
  simp[] >>
  disch_then (qx_choosel_then [`sl`,`se`] strip_assume_tac) >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[contextTheory.global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  mp_tac (Q.INST
    [`ctx` |-> `unit.cu_context`,
     `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
     `nkey` |-> `global_nonreentrant_slot`,
     `ss` |-> `vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0|>`]
    (SPEC_ALL externalEntryJointTheory.selected_entry_after_lock)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`s_lock`,`G_lock`,`tn_lock`]
    (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  `s_lock.vs_gas_readings = vs.vs_gas_readings /\
    s_lock.vs_code = vs.vs_code /\ s_lock.vs_labels = vs.vs_labels` by simp[] >>
  `mut <> View ==> ~tx.is_static` by
    (qpat_assum `mut <> View ==>
      ~(initial_evaluation_context am.sources am.layouts tx NONE).txn.is_static`
      (ACCEPT_TAC o SIMP_RULE (srw_ss())
        [vyperInterpreterTheory.initial_evaluation_context_def])) >>
  `!st0 H. valid_horizon
      (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
      es_lock.storage_trace ==>
      ((!fuel. ptr_safe_run
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 fuel unit.cu_context func [] G_lock tn_lock s_lock) ==>
        !fuel. ptr_safe_blocks
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 fuel unit.cu_context func [] FEMPTY entry_taint
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0 |>)) /\
      ghost_inv_at
        (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
        0 NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE)
        es_lock G_lock tn_lock s_lock /\
      stmt_state_rel H unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es_lock s_lock /\
      !explicit.
        gas_origin_ptr_path
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
           0,explicit,unit.cu_context,func,[])
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0 |>,FEMPTY,entry_taint)
           [] (OK s_lock,G_lock,tn_lock)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!st0 H. valid_horizon _ _ _ es_lock.storage_trace ==> _`
       (qspecl_then [`st0`,`H`] mp_tac) >>
     simp[GSYM bodyPtrDefsTheory.ghost_inv_cx_dead]);

fun registered_lock_result_tac placement =
  drule_all externalEntryJointTheory.selected_nonreentrant_lock_metadata >>
  strip_tac >>
  namedCases_on `lock_if_nr
    (initial_evaluation_context am.sources am.layouts tx NONE)
    T (is_view_mut mut) es0` ["status es_lock"] >>
  rename1 `lock_if_nr _ _ _ _ = (status,es_lock)` >>
  namedCases_on `status` ["u","exc"]
  >- (Cases_on `u` >> registered_lock_body_tac >>
      mp_tac (Q.SPECL
        ([`tops`,`rpolicy`,`unit`,`am`,`tx`,`ret`,`vs`,`mut`,
          `args`,`fbody`,`env`,`es0`,`es_lock`] @ placement @
         [`cenv`,`sa`,`sl`,`se`,`st'`,`func`,`s_lock`,
          `G_lock`,`tn_lock`])
        (INST_TYPE [alpha |-> ``:expr``] runtime_selected_lock_readings)) >>
      impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
      disch_then (qx_choosel_then [`shadow_unit`,`marks`] strip_assume_tac) >>
      qexistsl_tac [`shadow_unit`,`marks`] >> simp[]) >>
  mp_tac (Q.INST
    [`ctx` |-> `unit.cu_context`,
     `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
     `ss` |-> `vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0|>`,
     `es_abort` |-> `es_lock`,
     `fbody` |-> `subst_consts_stmts (module_consts_env tops []) fbody`,
     `rt` |-> `if ret = NoneT then NONE else SOME ret`]
    (SPEC_ALL externalEntryJointTheory.external_entry_abort_from_registration)) >>
  impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
  disch_then (qx_choosel_then [`a`,`s`,`G`,`tn`]
    (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  drule_all runtime_lock_abort_result_with >>
  disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
  qexistsl_tac [`shadow_unit`,`[]`] >> simp[];

Theorem dispatched_nonreentrant_result[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  (ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
    SOME (tx.function_name,tx.args) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) ==>
  ?shadow_unit marks.
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_unit_execution_correct_with shadow_unit.cu_context marks
      tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  strip_tac >>
  drule default_dispatch_raw_cases >>
  disch_then (DISJ_CASES_THEN2
    (MAP_EVERY ASSUME_TAC o CONJUNCTS)
    (qx_choosel_then [`tys`,`tvs`] strip_assume_tac))
  >- (drule_all fallback_entry_registration_joint >>
      disch_then (qx_choosel_then
        [`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`,`rt`] strip_assume_tac) >>
      fallback_source_package_tac >>
      qpat_x_assum `rt = if ret = NoneT then NONE else SOME ret` SUBST_ALL_TAC >>
      registered_lock_result_tac [`STRCAT "fn_" "__default__"`,
        `"fn___default__"`,`cenv`,`[]`,`4`,`mut = Payable`,
        `if ret = NoneT then NONE else SOME ret`,`sa`]) >>
  SUBGOAL_THEN (Term `?ts. FIND (\(name,ts). abi_method_id (type_env tops) name ts =
      cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
      SOME (tx.function_name,ts)`) ASSUME_TAC
  >- (qexists_tac `tys` >> first_assum ACCEPT_TAC) >>
  drule_all dispatched_selected_registration_joint >>
  disch_then (qx_choosel_then
    [`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,
     `rt`,`st`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`] strip_assume_tac) >>
  `nkey = global_nonreentrant_slot /\ ut' = T /\ iv = (mut = View) /\
    rt = (if ret = NoneT then NONE else SOME ret)` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> simp[]) >>
  gvs[] >>
  `runtime_entry_body_start tops rpolicy
    (lbl,cenv0,pos_args,min_cds,is_payable,T,global_nonreentrant_slot,
     T,mut = View,subst_consts_stmts (module_consts_env tops []) fbody,
     if ret = NoneT then NONE else SOME ret) st` by
    (pure_rewrite_tac[runtimeBodyStartDefsTheory.runtime_entry_body_start_def] >>
     disj1_tac >> first_assum ACCEPT_TAC) >>
  registered_lock_result_tac [`lbl`,`lbl`,`cenv0`,`pos_args`,`min_cds`,
    `is_payable`,`if ret = NoneT then NONE else SOME ret`,`st`]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dispatched_vyper_call_bind >>
  disch_then (qx_choose_then `env` assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>)`
    ["res es0"] >>
  reverse (namedCases_on `res` ["u", "e"])
  >- (qexists_tac `[]` >>
      `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
        (Cases_on `classify_functions tops` >> PairCases_on `r` >>
         drule supported_program_no_external_defaults >> simp[] >> strip_tac >>
         drule_at (Pat `classify_functions _ = _`) runtime_gas_shadow_unit_exists >>
         disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
         simp[gas_shadow_unit_def]) >>
      conj_tac >- (drule_all external_entry_value_revert_dispatched_with_nr >> simp[]) >>
      `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
      drule_all external_entry_reject_readings_nr >> simp[]) >>
  Cases_on `u` >>
  qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]
QED
*)
Triviality dispatched_call_readings_from_value_success:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    (!env es0. bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
         tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))) ==>
    ?marks.
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  cheat
QED

Triviality dispatched_call_readings_from_selected_endpoint:
  !tops rpolicy unit shadow_unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    (!env es0. tx.function_name <> "__default__" /\
       bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)) ==>
    ?marks.
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  irule dispatched_call_readings_from_value_success >>
  asm_rewrite_tac [] >> conj_tac
  >- (qexists_tac `rpolicy` >> asm_rewrite_tac []) >>
  qexistsl_tac [`args`, `fbody`, `mut`, `F`] >>
  asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
  `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)` by
    (Cases_on `tx.function_name = "__default__"`
     >- (drule_all dispatched_entry_endpoint_default >> simp[]) >>
     qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]) >>
  drule_all runtime_body_joint_from_start_with_readings >> simp[]
QED

Theorem dispatched_call_correct_with_readings:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) ==>
    ?marks.
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `nr`
  >- (irule dispatched_call_readings_from_value_success >> asm_rewrite_tac[] >>
      conj_tac >- (qexists_tac `rpolicy` >> asm_rewrite_tac[]) >>
      qexistsl_tac [`args`,`fbody`,`mut`,`T`] >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      drule_all dispatched_nonreentrant_result >>
      disch_then (qx_choosel_then [`actual_shadow`,`marks`] strip_assume_tac) >>
      qexists_tac `marks` >> gvs[]) >>
  drule_at (Pat `runtime_gas_shadow_unit _ _ = _`)
    dispatched_call_readings_from_selected_endpoint >>
  disch_then (drule_at (Pat `vyperInterpreter$lookup_function _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`unit`,`am`,`vs`] mp_tac) >>
  simp[dispatched_entry_endpoint_selected]
QED

Theorem dispatched_call_correct:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  metis_tac[dispatched_call_correct_with_readings,
            source_unit_execution_correct_def,
            source_unit_execution_correct_at_def]
QED
