(* Assemble a linked external call at the value check. *)
Theory dispatchedCallAssemblyMods
Ancestors
  dispatchedValuePrefix dispatchedSelectionMods dispatchedRejectCodeMods
  dispatchedRejectCertificateMods e2eModsDefs entryRejectCode sourceUnitExecutionMods
  sourceValueRejection linkedRuntimeValueRejection
  vyperContext vyperInterpreter vyperState

Theorem dispatched_call_correct_with_readings_mods:
  !execution_ok. execution_ok = (\marks.
    source_unit_execution_correct_with_mods shadow_ctx marks
      mods exps ret am tx unit vs /\
    ((?tail.
        call_storage_ok am tx vs.vs_outcomes
          (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
     !tail.
       FST (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
       INR (Error (RuntimeError "msg.gas: no gas reading")))) ==>
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    ~EXISTS (external_has_defaults o SND) (FST (classify_functions_unit mods exps)) /\
    gas_shadow_context unit.cu_context shadow_ctx /\
    source_typing_ok_mods mods exps am tx /\
    source_deployment_rel_mods mods exps am tx /\
    calldata_dispatch_mods mods exps vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name,tx.args) /\
    initial_venom_state_rel_mods mods am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    ALOOKUP mods (ALOOKUP exps tx.function_name) = SOME tops /\
    vyperInterpreter$lookup_function (ALOOKUP exps tx.function_name) tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    (!env es0.
       bind_arguments (type_env_all_modules mods) args tx.args = SOME env /\
       send_call_value mut
         (initial_evaluation_context am.sources am.layouts tx (ALOOKUP exps tx.function_name))
         (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
         (INL (),es0) ==>
       ?marks. execution_ok marks) ==>
    ?marks. execution_ok marks
Proof
  CONV_TAC Unwind.UNWIND_FORALL_CONV >> BETA_TAC >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `classify_functions_unit mods exps` >> PairCases_on `r` >>
  qpat_x_assum `~EXISTS _ (FST _)` (assume_tac o REWRITE_RULE [pairTheory.FST]) >>
  drule_all (SIMP_RULE pure_ss [LET_THM] linked_dispatched_binding_route) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `env` assume_tac) assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx (ALOOKUP exps tx.function_name))
    (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>)`
    ["res es0"] >>
  namedCases_on `res` ["u", "e"]
  >- (Cases_on `u` >>
      qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]) >>
  `value_transfer_ok
    (initial_evaluation_context am.sources am.layouts tx
      (ALOOKUP exps tx.function_name)).txn
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>).accounts` by
    gvs[initial_venom_state_rel_mods_def,
        initial_evaluation_context_def, initial_state_def] >>
  drule_at (Pos last) send_call_value_reject_condition >>
  simp[initial_evaluation_context_def] >> strip_tac >>
  drule_at (Pat `bind_arguments _ _ _ = SOME _`)
    vyperCallTheory.bind_arguments_length >> strip_tac >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH ([]:expr list)` by simp[] >>
  `!os gobs. call_external_trace (SOME os) gobs am tx =
     (INR (Error (RuntimeError "not Payable")),am,[],[])` by
    (gen_tac >> drule_all linked_external_value_reject_trace >>
     disch_then (qspec_then `SOME os` ACCEPT_TAC)) >>
  qexists_tac `[]` >> conj_tac
  >- (drule_all (SIMP_RULE pure_ss [LET_THM] linked_routed_reject_code) >>
      strip_tac >>
      qpat_assum `!os gobs. call_external_trace _ _ _ _ = _`
        (qspec_then `vs.vs_outcomes` assume_tac) >>
      irule linked_installed_reject_certificate >>
      fs[] >> qexistsl_tac [`checked`,`de`,`ds`,`fl`,`mc`,`opened`,`selectors`] >> simp[]) >>
  strip_tac >> qx_gen_tac `tail` >>
  qpat_x_assum `!os gobs. call_external_trace _ _ _ _ = _`
    (qspecl_then [`vs.vs_outcomes`, `gas_explicit [] vs.vs_gas_readings ++ tail`] assume_tac) >>
  drule_then strip_assume_tac call_external_trace_result >> simp[]
QED
