(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalEntryValueRevert
Ancestors
  externalEntryChecks entryChecksProps moduleLoweringProps
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

(* The source fails to move the call value only for a nonpayable function
   called with value: value_transfer_ok rules out a failed transfer. *)
Theorem send_call_value_fails[local]:
  !mut srcs layouts tx am env orc e es.
    value_transfer_ok tx am.accounts /\
    send_call_value mut (initial_evaluation_context srcs layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INR e, es) ==>
    mut <> Payable /\ tx.value <> 0
Proof
  rpt gen_tac >>
  simp[send_call_value_def, transfer_value_def, value_transfer_ok_def,
       initial_evaluation_context_def, initial_state_def] >>
  rw[] >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.assert_def,
      vyperStateTheory.check_def, get_accounts_def, update_accounts_def,
      AllCaseEqs()]
QED

(* When the source cannot move the call value (a nonpayable function
   called with value), the run from __entry reaches the selected
   function's entry checks (external_entry_reaches_checks), which abort
   as external_call_result_rel asks (entryChecksProps's
   entry_checks_nonpayable_value). *)
Theorem external_entry_value_revert:
  !tops rpolicy unit am tx ret vs mut args fbody env e st.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >>
  `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
  drule_all send_call_value_fails >> strip_tac >>
  drule_all external_entry_reaches_checks >> strip_tac >>
  rename1 `compile_entry_checks _ _ sc = ((), sc')` >>
  `call_tx_well_typed tx` by fs[source_typing_ok_def] >>
  `s0.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_x_assum `vars_pc_only _ _` mp_tac >> simp[vars_pc_only_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `call_ctx_rel tx s0.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx` by
    fs[initial_venom_state_rel_def, venom_env_rel_def] >>
  `?c. package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, rr, tx.function_name, args, ([] : expr list), ret, fbody) =
       (lbl, c, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt)` by
    (qmatch_asmsub_abbrev_tac `set_external_package_target _ pkg = _` >>
     PairCases_on `pkg` >>
     gvs[set_external_package_target_def, markerTheory.Abbrev_def]) >>
  qspecl_then [`tops`, `am`, `tx`, `SOME vs.vs_outcomes`, `ret`, `F`,
               `assign_nkeys tops 0`, `mut`, `rr`, `args`, `[] : expr list`, `fbody`,
               `lbl`, `c`, `pos_args`, `min_cds`, `is_payable`,
               `(F, nkey, ut', iv, fbody, rt)`, `sc`, `sc'`,
               `unit.cu_context`, `s0`, `vs.vs_tx_ctx`, `vs.vs_block_ctx`]
    mp_tac (Q.INST [`gobs` |-> `gas_explicit [] vs.vs_gas_readings`]
             entry_checks_nonpayable_value) >>
  impl_tac >- simp[] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  simp[source_unit_execution_correct_def, source_unit_execution_correct_at_def] >>
  qexists_tac `[]` >> disj2_tac >>
  first_x_assum (qspecl_then [`fuel`, `Abort Revert_abort t`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `fuel'` >> gvs[]
QED

