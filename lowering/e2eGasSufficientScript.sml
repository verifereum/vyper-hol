(* Sufficient gas for the identity finalizer: the cases from which the
 * sufficient-gas companions of vyper_call_correct_guarded and e2e_deploy_correctness
 * are joined.  The companions themselves are stated separately.
 *
 * vyper_call_correct_guarded holds for any gas, so it lets the frame run out of gas.
 * Here: some amount of gas is enough.  With at least that much more gas,
 * our frame runs out of gas only once it has run a RETURNDATACOPY.  That
 * exemption is needed: when a call fails, the compiled code copies the
 * callee's revert data and reverts with it, and a callee holding all but
 * 1/64 of our gas can return more data than the rest pays to copy, or
 * leave us too little for the REVERT after the copy.
 *
 * Contents:
 *   vyper_call_gas_sufficient_identity -- the call case, identity finalizer
 *   e2e_deploy_gas_sufficient_identity -- the deployment case
 *
 * Only gas starvation is ruled out: a StackOverflow outcome, which
 * frame_resource_starved also allows, does not depend on gas.
 *
 * The call case joins uniform runtime-unit fuel, the dispatch rejection
 * or selected-call certificate, the O1 bound, and codegen gas sufficiency.
 *
 * The RETURNDATACOPY escape applies to deployment as well. A code deposit
 * larger than max_code_size also causes OutOfGas at any gas.
 *
 * The call theorem, S1b and S6b rely on the lowering's bounded ABI decoder
 * checking each range before it loads from it, as it does today.
 *)
Theory e2eGasSufficient
Ancestors
  e2eDefs e2eProducers e2eEntry e2eOptEntry unitTransformDefs ctorDeployNoCreate
  stackPlanGen[qualified,ignore_grammar] loweringCreateSource
  contextRawReachable venomLayout ctorCallFreeExpr
  ptrDiscipline lowerDloadDefs e2eComposition sourceUnitExitSafe
  sourceUnitExecution exprSimHypsDefs
  o1PipelineCorrect o1PipelineCompose o1PassContract contextCodegenRel
  o1StaticPipelineCorrect runtimeLabelReadiness
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeProps loweringShapeSource passSimulationDefs contextCodegenRel
  codegenCorrectness immutableCodeLayout frameOutcome frameGas
  venomRunBounded unitMemInv o1OpcodeAbsence
  loweringRuntimeNoCreate venomPipelineDriverProps fragFuelUnit
  e2eCorrectness loweringCalldataCorrect dispatchedValueSelection callPremiseDispatch entryStateRel
  callRawVariant callDynamicMemory[qualified,ignore_grammar] vyperTypeContract
  asmOptimizer callTrace
  e2eDeployCorrectness e2eDeployAtMarks e2eDeployDefs e2eDeployRawFmp ctorDeployDefs ctorDeployBodyJoint
  ctorDeployFrame ctorDeployShape ctorDeployDefsReach ctorDeployInitcode
  ctorDeployEntry ctorDeployDead ctorDeployRunBounded ctorDeployImmBudget
  ctorDeployMemoryFrontier deployUnitExecution deployUnitExitSafe deployUnitProducers o1SafeUpto
  ctorDeployLoweringSource deployDynamicMemory
  vfmExecution vfmExecutionProp vfmContext list rich_list pair

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

(* ===== Entry facts preserved by add_frame_gas ===== *)

(* Only gas fields change, so the account maps and the return data the
   two bounds range over are the same. *)
Theorem add_frame_gas_bounded:
  !B g es.
    (balance_bounded B (add_frame_gas g es) <=> balance_bounded B es) /\
    (returndata_bounded (add_frame_gas g es) <=> returndata_bounded es)
Proof
  rpt gen_tac >> Cases_on `es.contexts`
  >- simp[add_frame_gas_def]
  >> PairCases_on `h` >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  simp[vfmTotalBalanceTheory.balance_bounded_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmReturndataBoundTheory.returndata_bounded_def,
       add_frame_gas_fields, MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP]
QED

Theorem entry_venom_state_add_frame_gas:
  !prog cp g es.
    entry_venom_state prog cp (add_frame_gas g es) =
    entry_venom_state prog cp es with
      <| vs_outcomes := MAP SND (call_trace (add_frame_gas g es));
         vs_gas_readings := gas_readings (add_frame_gas g es) |>
Proof
  rpt gen_tac >> Cases_on `es.contexts`
  >- simp[add_frame_gas_def, entry_venom_state_def] >>
  PairCases_on `h` >> simp[add_frame_gas_def, entry_venom_state_def]
QED

Theorem initial_ctx_rel_add_frame_gas[local]:
  !cp prog ctx vs es g.
    initial_ctx_rel cp prog ctx vs es ==>
    initial_ctx_rel cp prog ctx
      (vs with
        <| vs_outcomes := MAP SND (call_trace (add_frame_gas g es));
           vs_gas_readings := gas_readings (add_frame_gas g es) |>)
      (add_frame_gas g es)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_state (add_frame_gas g es)` by
    (irule add_frame_gas_wf_state >> fs[initial_ctx_rel_def]) >>
  fs[initial_ctx_rel_def] >>
  drule add_frame_gas_contexts >>
  disch_then (qspec_then `g` assume_tac) >>
  `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
    simp[add_frame_gas_def] >>
  qexistsl_tac [
    `ctxt with msgParams updated_by (\p. p with gasLimit updated_by $+ g)`,
    `rb`,
    `MAP (\x. (FST x with <| gasUsed updated_by $+ g;
                msgParams updated_by (\p. p with gasLimit updated_by $+ g) |>,
              SND x)) rest`] >>
  gvs[initial_state_rel_def, initial_codegen_state_rel_def,
     stack_params_rel_def, msg_ctx_rel_def, blockhash_rel_def,
     add_frame_gas_fields]
QED

(* The source boundary and code layout ignore the two traced streams.
   The codegen boundary keeps the streams of the raised state itself. *)
Theorem call_gas_entry_rel[local]:
  !tops prog am tx es u cp policy g.
    call_state_rel tops (assemble prog) am tx es /\
    codegen_assembly policy u = SOME prog /\ unit_shape_ok u ==>
    initial_venom_state_rel tops am tx
      (entry_venom_state prog cp (add_frame_gas g es)) /\
    initial_ctx_rel cp prog u.cu_context
      (entry_venom_state prog cp (add_frame_gas g es)) (add_frame_gas g es) /\
    code_layout_valid (entry_venom_state prog cp (add_frame_gas g es))
Proof
  rpt strip_tac >> rename1 `entry_venom_state prog cplan (add_frame_gas g es)`
  >- (drule entry_venom_state_initial_venom_state_rel >>
      disch_then (qspec_then `cplan` mp_tac) >>
      simp[entry_venom_state_add_frame_gas, initial_venom_state_rel_def,
           venom_env_rel_def])
  >- (drule_all entry_venom_state_initial_ctx_rel >>
      disch_then (qspec_then `cplan` assume_tac) >>
      drule initial_ctx_rel_add_frame_gas >>
      disch_then (qspec_then `g` mp_tac) >>
      simp[entry_venom_state_add_frame_gas]) >>
  drule_all generated_entry_code_layout_shape >>
  disch_then (qspec_then `cplan` mp_tac) >>
  simp[entry_venom_state_add_frame_gas, code_layout_valid_def]
QED

(* The creation frame's relation at the new gas: only gas fields change. *)
Theorem deploy_state_rel_add_frame_gas:
  !tops bc am tx g es.
    deploy_state_rel tops bc am tx es ==>
    deploy_state_rel tops bc am tx (add_frame_gas g es)
Proof
  rw[deploy_state_rel_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  qexistsl_tac [`ctxt with msgParams updated_by (\p. p with gasLimit updated_by $+ g)`,
                `rb`, `args_bytes`] >>
  `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
    (simp[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]) >>
  fs[add_frame_gas_wf_state, add_frame_gas_fields, add_frame_gas_bounded]
QED

(* ===== The gas theorems' exemptions ===== *)

(* The correctness exemptions, plus a source run that stops on an oversized
   CREATE initcode: the EVM answers that CREATE with OutOfGas at every gas
   limit (EIP-3860), so no gas is enough. *)
Definition gas_source_exempt_def:
  gas_source_exempt tops tx
    (src : (value + exception) # abstract_machine # call_request list) <=>
    source_exempt tops src \/
    FST src = INR (Error (RuntimeError "create initcode too large")) \/
    (tx.is_static /\
     ((?m. m <> "msg.gas: no gas reading" /\
           FST src = INR (Error (RuntimeError m))) \/
      FST src = INR (AssertException "UNREACHABLE")))
End

Definition deploy_gas_source_exempt_def:
  deploy_gas_source_exempt tops
    (src : (abstract_machine # call_request list) + exception) <=>
    deploy_source_exempt tops src \/
    src = INR (Error (RuntimeError "create initcode too large"))
End

(* GATE_ADMISSION: held, creation body case; create size at the call entry *)
Theorem call_entry_reachable_create_size_ok:
  !own fin tops rpolicy unit out prog prog' cplan am tx es vs.
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (own <=> fin = asm_opt_finalizer) /\
    supported_program tops /\ source_typing_ok tops am tx /\
    EXISTS (top_body_has expr_create_root) tops /\
    (?es0 g. call_state_rel tops (assemble prog') am tx es0 /\
             es = add_frame_gas g es0) /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cplan /\
    vs = (if own then opt_entry_state_own prog prog' cplan es
          else opt_entry_state prog prog' cplan es) /\
    (!f vals. calldata_dispatch tops tx.calldata = SOME (f,vals) ==>
      (!obs. call_storage_ok am (tx with <|function_name := f; args := vals|>)
        (MAP SND (call_trace es)) obs) /\
      (!obs. ~gas_source_exempt tops (tx with <|function_name := f; args := vals|>)
        (call_external (SOME (MAP SND (call_trace es))) obs am
          (tx with <|function_name := f; args := vals|>))) /\
      LENGTH (call_trace es) < 2 ** 64) ==>
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      out.po_unit.cu_context vs
Proof
  cheat
QED

(* GATE_ADMISSION: held, creation body case; create size at the deploy entry *)
Theorem deploy_entry_reachable_create_size_ok:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs.
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_dalloca_form_occurs expr_create_root tops /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs = opt_deploy_entry_state_own prog prog' cplan tops es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    (!obs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) obs) /\
    (!obs. ~deploy_gas_source_exempt tops
      (load_contract (SOME (MAP SND (call_trace es))) obs am tx [(NONE,tops)] [])) ==>
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      dout.po_unit.cu_context vs
Proof
  cheat
QED

Theorem opt_entry_state_identity_add_frame_gas:
  !tops am tx prog cp es g.
    call_state_rel tops (assemble prog) am tx es ==>
    opt_entry_state prog prog cp (add_frame_gas g es) =
    entry_venom_state prog cp (add_frame_gas g es)
Proof
  rpt strip_tac >>
  `(FST (HD (add_frame_gas g es).contexts)).msgParams.code =
     (FST (HD es.contexts)).msgParams.code` by
    (Cases_on `es.contexts` >- simp[add_frame_gas_def] >>
     PairCases_on `h` >> drule add_frame_gas_contexts >>
     disch_then (qspec_then `g` mp_tac) >> simp[]) >>
  qspecl_then [`tops`, `am`, `tx`, `prog`, `cp'`, `es`]
    mp_tac opt_entry_state_identity >>
  simp[] >>
  simp[opt_entry_state_def, entry_venom_state_add_frame_gas,
       venomStateTheory.venom_state_component_equality] >>
  metis_tac[opt_entry_state_identity, opt_entry_state_def,
            venomStateTheory.venom_state_component_equality]
QED

(* CREATE and CREATE2 are absent from the lowered unit, so the size
   invariant holds for every entry state. *)
Theorem deploy_entry_create_size_ok:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  ~deploy_dalloca_form_occurs expr_create_root tops ==>
  mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
    dout.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
   o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout` by
    fs[deploy_phases_def] >>
  match_mp_tac mem_inv_create_size_ok_no_create >>
  conj_tac
  >- (qpat_x_assum `o1PipelineCorrect$o1_pipeline _ _ = _` mp_tac >>
      simp[o1PipelineCorrectTheory.o1_pipeline_def] >>
      disch_then (assume_tac o MATCH_MP run_venom_pipeline_success_unit_wf) >>
      fs[venomCompilerWfTheory.unit_wf_def]) >>
  qspecl_then [`tops`, `am`, `tx`, `rpolicy`, `runtime_bc`, `dunit`] mp_tac
    lower_vyper_deploy_unit_no_create >>
  impl_tac >- simp[] >> disch_tac >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qspecl_then [`rpolicy`, `dunit`, `dout`, `CREATE`] mp_tac
        o1_pipeline_opcode_absence >>
      impl_tac >- (fs[] >> metis_tac[]) >> disch_then drule_all >> simp[]) >>
  qspecl_then [`rpolicy`, `dunit`, `dout`, `CREATE2`] mp_tac
    o1_pipeline_opcode_absence >>
  impl_tac >- (fs[] >> metis_tac[]) >> disch_then drule_all >> simp[]
QED

Theorem call_static_abort_gas_source_exempt:
  !H tops ret tx src u.
    tx.is_static /\
    FST src <> INR (Error (RuntimeError "msg.gas: no gas reading")) /\
    external_call_result_rel H tops ret tx src (Abort ExHalt_abort u) ==>
    gas_source_exempt tops tx src
Proof
  rpt gen_tac >> PairCases_on `src` >>
  Cases_on `src0` >> simp[external_call_result_rel_def] >>
  rename1 `INR ex` >> Cases_on `ex` >>
  simp[external_call_result_rel_def, gas_source_exempt_def] >>
  rename1 `Error e` >> Cases_on `e` >>
  simp[external_call_result_rel_def, gas_source_exempt_def]
QED

Theorem call_gas_static_no_abort:
  !tops ret am tx unit vs marks.
    tx.is_static /\ o1_source_unit_ok unit /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~gas_source_exempt tops tx
      (call_external (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings) am tx) /\
    FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings) am tx) <>
      INR (Error (RuntimeError "msg.gas: no gas reading")) ==>
    ~(!fuel. terminates (run_context fuel unit.cu_context vs) ==>
       ?u. run_context fuel unit.cu_context vs = Abort ExHalt_abort u)
Proof
  rpt strip_tac >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_at_def,
                                      source_unit_execution_correct_with_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> simp[])
  >- (qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      drule vyperInterpreterTheory.call_external_trace_result >> strip_tac >>
      gvs[gas_source_exempt_def]) >>
  qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `[]` assume_tac) >> fs[] >>
  drule vyperInterpreterTheory.call_external_trace_result >> strip_tac >>
  drule_all e2eCorrectnessTheory.selected_run >> strip_tac >>
  `terminates (run_context fuel unit.cu_context vs)` by
    (Cases_on `run_context fuel unit.cu_context vs` >>
     gvs[terminates_def, fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!n. terminates _ ==> _` drule >> strip_tac >>
  `external_call_result_rel (storage_trace_horizon obs) tops ret tx
     (res, am', rqs) (Abort ExHalt_abort u)` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qspecl_then [`storage_trace_horizon obs`, `tops`, `ret`, `tx`,
               `(res, am', rqs)`, `u`] mp_tac
    call_static_abort_gas_source_exempt >> gvs[]
QED

(* ===== The call cases ===== *)

(* With no creation forms, lowering and O1 both preserve opcode absence. *)
Theorem o1_runtime_unit_create_size_ok:
  !tops rpolicy unit out vs am tx.
    source_typing_ok tops am tx /\
    ~EXISTS (top_body_has expr_create_root) tops /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out
    ==>
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s) out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[source_typing_ok_def] >>
  `!vis mut nr rr name args dflts ret body.
    MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops ==>
      ~supported_stmts_expr_exists expr_create_root body /\
      ~EXISTS (supported_expr_exists expr_create_root) dflts` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `~EXISTS (top_body_has expr_create_root) tops` mp_tac >>
     simp[EXISTS_MEM, EVERY_MEM] >>
     disch_then (qspec_then `FunctionDecl vis mut nr rr name args dflts ret body` mp_tac) >>
     simp[top_body_has_def, EVERY_MEM, combinTheory.o_DEF]) >>
  `runtime_bodies_avoid_create tops` by
    (drule_all (INST_TYPE [alpha |-> ``:160 word``]
       check_contract_runtime_bodies_avoid_create) >> simp[]) >>
  match_mp_tac mem_inv_create_size_ok_no_create >>
  conj_tac
  >- (qpat_x_assum `o1PipelineCorrect$o1_pipeline _ _ = _` mp_tac >>
      simp[o1PipelineCorrectTheory.o1_pipeline_def] >>
      disch_then (assume_tac o MATCH_MP run_venom_pipeline_success_unit_wf) >>
      fs[venomCompilerWfTheory.unit_wf_def]) >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac
    lower_vyper_runtime_unit_no_create >>
  impl_tac >- fs[] >> disch_tac >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qspecl_then [`rpolicy`, `unit`, `out`, `CREATE`] mp_tac
        o1_pipeline_opcode_absence >>
      impl_tac >- (fs[] >> metis_tac[]) >> disch_then drule_all >> simp[]) >>
  qspecl_then [`rpolicy`, `unit`, `out`, `CREATE2`] mp_tac
    o1_pipeline_opcode_absence >>
  impl_tac >- (fs[] >> metis_tac[]) >> disch_then drule_all >> simp[]
QED

(* A uniform bound on every terminating run of the runtime unit, before
   choosing the entry state or decoding the calldata. *)
Theorem call_gas_uniform_fuel:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops ==>
  ?fuel. !n s. terminates (run_context n unit.cu_context s) ==>
               terminates (run_context fuel unit.cu_context s)
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac
    lower_vyper_runtime_unit_fns_stable >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_context_terminates_uniform >> simp[]
QED

Triviality initial_venom_state_rel_dispatch:
  initial_venom_state_rel tops am
    (tx with <| function_name := f; args := vals |>) vs <=>
  initial_venom_state_rel tops am tx vs
Proof
  simp[initial_venom_state_rel_def, venom_env_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def,
       loweringStateRelDefsTheory.tx_env_ok_def, value_transfer_ok_def,
       accounts_after_transfer_def]
QED

(* Dispatch rejection provides the raw facts directly. On a selected call
   they come from the execution certificate at its own gas marks. *)
Theorem call_gas_raw_variant_facts:
  !tops rpolicy unit am tx vs vi fuel fmp.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp <= w2n fmp /\
    (!f vals. calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
       LENGTH vs.vs_outcomes < 2 ** 64 /\ LENGTH tx.calldata < 2 ** 64) /\
    o1_source_unit_ok unit /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context +
        32 * ctx_dload_count unit.cu_context <= w2n fmp /\ w2n fmp < 2 ** 254) /\
    code_layout_valid vs /\ raw_variant fmp vi vs /\
    (!n s. terminates (run_context n unit.cu_context s) ==>
           terminates (run_context fuel unit.cu_context s)) /\
    (!f vals. calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
       (!obs. call_storage_ok am
          (tx with <| function_name := f; args := vals |>) vs.vs_outcomes obs) /\
       (!obs. ~gas_source_exempt tops
          (tx with <| function_name := f; args := vals |>)
          (call_external (SOME vs.vs_outcomes) obs am
             (tx with <| function_name := f; args := vals |>)))) ==>
    raw_unit_memory_ok unit.cu_context vi /\
    ptr_discipline 0 unit.cu_context vi /\
    mem_inv dload_offset_ok unit.cu_context vi /\
    mem_inv dload_headroom_ok unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                              s.vs_code = vi.vs_code /\
                              s.vs_data_section = vi.vs_data_section)
      unit.cu_context vi /\
    terminates (run_context fuel unit.cu_context vi) /\
    (tx.is_static ==>
     ~(!n. terminates (run_context n unit.cu_context vi) ==>
          ?u. run_context n unit.cu_context vi = Abort ExHalt_abort u))
Proof
  rpt gen_tac >> strip_tac >>
  `vs.vs_call_ctx.cc_calldata = tx.calldata` by
    fs[initial_venom_state_rel_def, venom_env_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def] >>
  Cases_on `calldata_dispatch tops tx.calldata`
  >- (qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `vi`, `fmp`]
        mp_tac raw_variant_revert_facts_fmp >>
      simp[] >> strip_tac >>
      rename1 `run_context n unit.cu_context vi = Abort Revert_abort _` >>
      `terminates (run_context n unit.cu_context vi)` by
        simp[terminates_def] >>
      simp[] >> conj_tac >- metis_tac[] >>
      strip_tac >> qexists_tac `n` >> simp[]) >>
  rename1 `_ = SOME fv` >> PairCases_on `fv` >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule_all_then strip_assume_tac calldata_dispatch_has_source_entry >>
  `LENGTH vs.vs_outcomes < 2 ** 64 /\ LENGTH tx.calldata < 2 ** 64` by
    metis_tac[] >>
  qpat_x_assum `!f vals. SOME (fv0, fv1) = SOME (f, vals) ==>
     (!obs. call_storage_ok _ _ _ _) /\ _`
    (qspecl_then [`fv0`, `fv1`] mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac `td = tx with <| function_name := fv0; args := fv1 |>` >>
  `initial_venom_state_rel tops am tx vi` by
    metis_tac[raw_variant_initial_venom_state_rel] >>
  `vi.vs_outcomes = vs.vs_outcomes /\ vi.vs_call_ctx = vs.vs_call_ctx` by
    metis_tac[raw_variant_outcomes, raw_variant_call_ctx] >>
  `code_layout_valid vi /\ vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp` by
    (fs[raw_variant_def, gas_variant_def, code_layout_valid_def,
        venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `dispatched_vyper_call tops td vi.vs_call_ctx.cc_calldata ret` by
    (simp[Abbr`td`, dispatched_vyper_call_def] >> metis_tac[]) >>
  `source_typing_ok tops am td` by
    simp[Abbr`td`, call_premises_dispatch_invariant] >>
  `source_deployment_rel tops am td /\ td.is_static = tx.is_static` by
    fs[Abbr`td`, source_deployment_rel_def, layouts_agree_def] >>
  `initial_venom_state_rel tops am td vi` by
    simp[Abbr`td`, initial_venom_state_rel_dispatch] >>
  `outcomes_accounts_typed (SOME vi.vs_outcomes)` by fs[] >>
  `ctx_has_dalloca unit.cu_context ==>
    unit_alloca_budget unit.cu_context <= w2n vi.vs_initial_fmp /\
    w2n vi.vs_initial_fmp < 2 ** 254` by
    (strip_tac >> fs[] >> decide_tac) >>
  `ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vi unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s` by
    (strip_tac >>
     qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `fmp`, `vi`]
       mp_tac callDynamicMemoryTheory.call_raw_variant_headroom >> gvs[]) >>
  drule_all lower_vyper_runtime_unit_correct_dispatched_readings_available >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qabbrev_tac `obs = gas_explicit marks vi.vs_gas_readings` >>
  `call_storage_ok am td vi.vs_outcomes obs /\
   ~gas_source_exempt tops td (call_external (SOME vi.vs_outcomes) obs am td)` by
    metis_tac[] >>
  `FST (call_external (SOME vi.vs_outcomes) obs am td) <>
     INR (Error (RuntimeError "msg.gas: no gas reading"))` by
    (qpat_x_assum `(?tail. _) ==> _` mp_tac >>
     impl_tac >- (qexists_tac `[]` >> fs[Abbr`obs`]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[Abbr`obs`]) >>
  `~source_exempt tops (call_external (SOME vi.vs_outcomes) obs am td)` by
    fs[gas_source_exempt_def] >>
  `?n. terminates (run_context n unit.cu_context vi)` by
    (qpat_assum `source_unit_execution_correct_at _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_at_def,
                                         source_unit_execution_correct_with_def])
     >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >>
         fs[Abbr`obs`])
     >- (qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
           (qspec_then `[]` assume_tac) >> fs[] >>
         drule vyperInterpreterTheory.call_external_trace_result >>
         strip_tac >> gvs[Abbr`obs`]) >>
     drule_all e2eCorrectnessTheory.selected_run >> strip_tac >>
     rename1 `run_context n unit.cu_context vi = _` >>
     qexists_tac `n` >>
     Cases_on `run_context n unit.cu_context vi` >>
     gvs[terminates_def, fragExecTheory.exit_result_def]) >>
  `terminates (run_context fuel unit.cu_context vi)` by metis_tac[] >>
  qunabbrev_tac `obs` >>
  qspecl_then [`marks`, `tops`, `ret`, `am`, `td`, `unit`, `vi`, `rpolicy`]
    mp_tac source_unit_exit_safe_runs >>
  impl_tac >- simp[] >> strip_tac >>
  `w2n vi.vs_initial_fmp <= w2n vi.vs_fmp` by simp[] >>
  `ctx_has_dalloca unit.cu_context ==>
    32 * ctx_dload_count unit.cu_context + unit_alloca_budget unit.cu_context <= w2n fmp` by
    (disch_tac >>
     qpat_assum `ctx_has_dalloca unit.cu_context ==> _ <= w2n fmp /\ w2n fmp < 2 ** 254`
       (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] o
        CONJUNCT1 o UNDISCH)) >>
  `raw_unit_memory_ok unit.cu_context vi /\ ptr_discipline 0 unit.cu_context vi` by
    (mp_tac (Q.INST [`rp` |-> `rpolicy`, `vs` |-> `vi`, `tx` |-> `td`,
          `D` |-> `cx_dead (H : (bool # bytes32 # type_value) list # num list)
            (initial_evaluation_context am.sources am.layouts td NONE)`]
        e2eCorrectnessTheory.selected_raw_memory) >>
     impl_tac >- simp[] >>
     simp[]) >>
  `mem_inv dload_offset_ok unit.cu_context vi` by
    (irule lower_vyper_runtime_unit_dload_offset_ok >> metis_tac[]) >>
  `mem_inv dload_headroom_ok unit.cu_context vi` by
    (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
  `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                           s.vs_code = vi.vs_code /\
                           s.vs_data_section = vi.vs_data_section)
     unit.cu_context vi` by
    (irule lower_vyper_runtime_unit_dload_in_section >> metis_tac[]) >>
  simp[] >> strip_tac >>
  qspecl_then [`tops`, `ret`, `am`, `td`, `unit`, `vi`, `marks`] mp_tac
    call_gas_static_no_abort >>
  simp[]
QED

Theorem call_state_rel_add_frame_gas_raises:
  call_state_rel tops runtime_bc am tx es ==>
  !g. frame_raises (add_frame_gas g es) OutOfGas <=>
      ?op. frame_inst_raises (add_frame_gas g es) OutOfGas op
Proof
  strip_tac >> gen_tac >> irule frame_raises_inst_raises >>
  qpat_x_assum `call_state_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [call_state_rel_def, evm_state_ok_def]) >>
  simp[add_frame_gas_wf_state] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` strip_assume_tac) >>
  simp[]
QED

(* The selected-call guards range over the trace at the raised gas
   and over the source call the calldata dispatches to.  ~gas_source_exempt is S3's ~source_exempt (on
   the exempt inputs, malformed data to a dynamic abi_decode, the compiled
   code may read at any offset, so no gas is enough) plus no oversized
   CREATE initcode.  It is stated for every list of GAS
   observations, since the source run S4 relates the compiled run to may
   read other GAS values than the EVM run does. *)
Theorem vyper_call_gas_sufficient_identity:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es
    ==>
    ?g. !g'.
      g <= g' /\
      (!f vals.
         calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
           (!gs. call_storage_ok am
              (tx with <| function_name := f; args := vals |>)
              (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
           (!obs. ~gas_source_exempt tops
              (tx with <| function_name := f; args := vals |>)
              (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                 obs am (tx with <| function_name := f; args := vals |>))) /\
           LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64)
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (frame_raises (add_frame_gas g' es) OutOfGas ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_checked_source_shape >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def, frame_fresh_def,
                                           frame_tx_rel_def, world_rel_def] >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  drule_all call_gas_uniform_fuel >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`0`, `rpolicy`, `unit`, `out`, `cplan`, `fuel`] mp_tac
    run_venom_pipeline_run_bounded_static_abort >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `out.po_unit`, `cplan`, `prog`, `fuel'`, `M`]
    mp_tac codegen_gas_sufficient >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  drule call_state_rel_add_frame_gas_raises >>
  disch_then (qspec_then `g'` (fn th => PURE_REWRITE_TAC [th])) >>
  (* Carry only the entry facts that survive the gas top-up. *)
  drule_all call_gas_entry_rel >>
  disch_then (qspecl_then [`cplan`, `g'`] strip_assume_tac) >>
  `outcomes_accounts_typed
      (SOME (MAP SND (call_trace (add_frame_gas g' es))))` by
    (`wf_state (add_frame_gas g' es) /\
      balance_bounded (2 ** 256 - 1) (add_frame_gas g' es) /\
      returndata_bounded (add_frame_gas g' es)` by
       (fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
           evm_state_ok_def, add_frame_gas_bounded] >>
        irule add_frame_gas_wf_state >> simp[]) >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, listTheory.EVERY_MEM]) >>
  `wf_state es` by fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def,
                      world_rel_def, evm_state_ok_def] >>
  qspecl_then [`prog`, `cplan`, `add_frame_gas g' es`] assume_tac
    entry_venom_state_o1_initial_state_ok >>
  qabbrev_tac `vs = entry_venom_state prog cplan (add_frame_gas g' es)` >>
  `vs.vs_outcomes = MAP SND (call_trace (add_frame_gas g' es)) /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[Abbr`vs`, entry_venom_state_def] >>
  `o1_initial_state_ok vs /\ code_layout_valid vs` by fs[Abbr`vs`] >>
  `vs.vs_fmp = vs.vs_initial_fmp` by
    simp[Abbr`vs`, entry_venom_state_def] >>
  `K SOME <> asm_opt_finalizer` by
    (strip_tac >>
     qpat_x_assum `K SOME = asm_opt_finalizer`
       (fn th => mp_tac (Q.AP_THM
         (Q.AP_THM th `rpolicy with rpol_final_assembly := FAP_Optimize`)
         `[AsmOp "STOP"; AsmOp "STOP"]`)) >>
     EVAL_TAC) >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      out.po_unit.cu_context vs` by
    (Cases_on `EXISTS (top_body_has expr_create_root) tops`
     >- (qspecl_then [`F`, `K SOME`, `tops`, `rpolicy`, `unit`, `out`,
                      `prog`, `prog`, `cplan`, `am`, `tx`,
                      `add_frame_gas g' es`, `vs`]
           mp_tac call_entry_reachable_create_size_ok >>
         impl_tac >- (simp[accepted_finalizers_def, Abbr `vs`] >>
                      metis_tac[opt_entry_state_identity_add_frame_gas]) >>
         simp[]) >>
     metis_tac[o1_runtime_unit_create_size_ok]) >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[lower_vyper_runtime_unit_no_runtime_begin] >>
  (* Each variant has its own storage horizon.  The gas bound needs only
     termination and memory bounds, so one all-dead mask serves them all. *)
  qabbrev_tac `D = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D` by simp[Abbr`D`, dead_wf_def] >>
  `!f vals. calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
      (!obs. call_storage_ok am
         (tx with <| function_name := f; args := vals |>) vs.vs_outcomes obs) /\
      (!obs. ~gas_source_exempt tops
         (tx with <| function_name := f; args := vals |>)
         (call_external (SOME vs.vs_outcomes) obs am
            (tx with <| function_name := f; args := vals |>)))` by
    simp[] >>
  `outcomes_accounts_typed (SOME vs.vs_outcomes)` by simp[] >>
  `!f vals. calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
     LENGTH vs.vs_outcomes < 2 ** 64 /\ LENGTH tx.calldata < 2 ** 64` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `!f vals. calldata_dispatch tops tx.calldata = SOME (f,vals) ==>
          _ /\ _ /\ LENGTH (call_trace (add_frame_gas _ _)) < _`
           (qspecl_then [`f`,`vals`] (fn branch =>
              qpat_assum `calldata_dispatch tops tx.calldata = SOME (f,vals)`
                (assume_tac o cj 3 o MATCH_MP branch))) >>
         fs[]) >>
     drule callDynamicMemoryTheory.call_state_rel_calldata_bound >> simp[]) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[stackPlanGenTheory.generate_context_plan_def] >>
     drule stackPlanGenTheory.generate_context_plan_with_headroom >> simp[]) >>
  `w2n vs.vs_initial_fmp < 2 ** 254` by
    (fs[wordsTheory.w2n_n2w, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  drule callDynamicMemoryTheory.call_source_raw_fmp >>
  disch_then (qspec_then `vs.vs_initial_fmp` strip_assume_tac) >>
  `!vi. raw_variant fmp vi vs ==>
        raw_unit_memory_ok unit.cu_context vi /\
        ptr_discipline 0 unit.cu_context vi /\
        taint_within D unit.cu_context vi /\
        mem_inv dload_offset_ok unit.cu_context vi /\
        mem_inv dload_headroom_ok unit.cu_context vi /\
        terminates (run_context fuel unit.cu_context vi) /\
        (tx.is_static ==>
         ~(!n. terminates (run_context n unit.cu_context vi) ==>
               ?u. run_context n unit.cu_context vi = Abort ExHalt_abort u))` by
    (gen_tac >> strip_tac >>
     qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `vi`, `fuel`, `fmp`]
       mp_tac call_gas_raw_variant_facts >>
     impl_tac >- (simp[] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[Abbr`D`, taint_within_def]) >>
  `venom_run_bounded fuel' M out.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
       (qspecl_then [`D`, `vs`, `fmp`] mp_tac) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  (* S4's input state, for the codegen obligations *)
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  `o1_lowered_inv out.po_unit.cu_context vs` by
    (Cases_on `tx.is_static`
     >- (qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`,
                      `fmp`] mp_tac
           run_venom_pipeline_correct_static_abort >>
         impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
         qpat_assum `!vi. raw_variant _ vi vs ==> _`
           (qspec_then `vs_in` mp_tac) >>
         impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
         qpat_x_assum `_ ==> ctx_sim _ _ _ _ _ /\ _` drule_all >>
         metis_tac[]) >>
     `o1_run_state_ok vs` by
       (qpat_x_assum `initial_venom_state_rel tops am tx vs` mp_tac >>
        simp[initial_venom_state_rel_def, venom_env_rel_def,
             loweringStateRelDefsTheory.call_ctx_rel_def, o1_run_state_ok_def]) >>
     qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`,
                  `fmp`] mp_tac run_venom_pipeline_correct >>
     impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
     qpat_x_assum `_ ==> ctx_sim _ _ _ _ _ /\ _` mp_tac >>
     impl_tac >- metis_tac[] >> simp[]) >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qpat_x_assum `prog = _` kall_tac >>
  qpat_x_assum `!g' Inv vs es. _` irule >> simp[] >>
  qexistsl_tac [`Inv`, `vs`] >> simp[]
QED


(* ===== The deployment cases ===== *)

(* The source result and memory facts at a raw constructor entry. *)
Theorem deploy_gas_raw_variant_facts:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs vi fmp.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs = opt_deploy_entry_state_own prog prog' cplan tops es /\
    vs.vs_alloca_next = imm_len tops /\ code_layout_valid vs /\
    LENGTH (call_trace es) < 2 ** 64 /\
    w2n vs.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    raw_variant fmp vi vs /\
    (!gs. deploy_storage_ok tops am tx vs.vs_outcomes gs) /\
    (!obs. ~deploy_source_exempt tops
       (load_contract (SOME vs.vs_outcomes) obs am tx [(NONE,tops)] []))
    ==>
      ?(H : (bool # bytes32 # type_value) list # num list) obs efuel.
        raw_unit_memory_ok dunit.cu_context vi /\
        ptr_discipline (imm_len tops) dunit.cu_context vi /\
        taint_within (deploy_dead H tops runtime_bc am tx) dunit.cu_context vi /\
        mem_inv dload_offset_ok dunit.cu_context vi /\
        mem_inv dload_headroom_ok dunit.cu_context vi /\
        mem_inv (\c f inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\
                             s.vs_data_section = vi.vs_data_section)
          dunit.cu_context vi /\
        deploy_venom_result_rel H tops runtime_bc tx
          (load_contract (SOME vs.vs_outcomes) obs am tx [(NONE,tops)] [])
          (run_context efuel dunit.cu_context vi)
Proof
  rpt gen_tac >> strip_tac >>
  `vi.vs_outcomes = vs.vs_outcomes` by metis_tac[raw_variant_outcomes] >>
  `code_layout_valid vi /\ vi.vs_alloca_next = imm_len tops /\
    vi.vs_initial_fmp = fmp /\ vi.vs_fmp = fmp` by
    (fs[raw_variant_def, gas_variant_def, code_layout_valid_def,
        venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `deploy_typing_ok tops am tx` by fs[deploy_source_ok_def] >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  `lowering_context_ok dunit.cu_context` by metis_tac[deploy_unit_context_ok] >>
  qspecl_then [`fin`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
               `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `fmp`]
    mp_tac deploy_unit_execution_correct_selected_raw_fmp >>
  impl_tac >- gvs[] >> strip_tac >>
  `?marks. deploy_unit_execution_correct_at marks tops runtime_bc am tx dunit vi`
    by
    (simp[deploy_unit_execution_correct_at_with] >>
     qpat_x_assum `!vs. raw_variant _ vs _ ==> _` (qspec_then `vi` mp_tac) >>
     impl_tac >- metis_tac[] >> metis_tac[]) >>
  qspecl_then [`marks`, `tops`, `runtime_bc`, `am`, `tx`, `dunit`, `vi`, `[]`]
    mp_tac deploy_unit_exit_safe_runs >>
  REWRITE_TAC [APPEND_NIL] >>
  qabbrev_tac `obs = gas_explicit marks vi.vs_gas_readings` >>
  `deploy_storage_ok tops am tx vi.vs_outcomes obs` by
    (qpat_assum `vi.vs_outcomes = vs.vs_outcomes`
       (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `!gs. deploy_storage_ok tops am tx _ gs`
       (qspec_then `obs` ACCEPT_TAC)) >>
  `~deploy_source_exempt tops
      (load_contract (SOME vi.vs_outcomes) obs am tx [(NONE,tops)] [])` by
    metis_tac[] >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  strip_tac >>
  rename1 `deploy_venom_result_rel _ _ _ _ _ (run_context vf _ vi)` >>
  `?(H : (bool # bytes32 # type_value) list # num list).
      (!fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
         (imm_len tops) fuel dunit.cu_context func [] FEMPTY entry_taint
         (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) /\
      deploy_venom_result_rel H tops runtime_bc tx
        (load_contract (SOME vi.vs_outcomes) obs am tx [(NONE,tops)] [])
        (run_context vf dunit.cu_context vi)` by
    (qexists_tac `storage_trace_horizon
       (deploy_storage_trace (SOME vi.vs_outcomes) obs am tx tops)` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n vi.vs_initial_fmp <= w2n vi.vs_fmp` by simp[] >>
  `raw_unit_memory_ok dunit.cu_context vi /\
   ptr_discipline (imm_len tops) dunit.cu_context vi /\
   taint_within (deploy_dead
     (H : (bool # bytes32 # type_value) list # num list) tops runtime_bc am tx)
     dunit.cu_context vi /\
   mem_inv dload_offset_ok dunit.cu_context vi /\
   mem_inv dload_headroom_ok dunit.cu_context vi` by
    (Cases_on `ctx_has_dalloca dunit.cu_context`
     >- (mp_tac (Q.INST [`vs` |-> `vi`,
                            `D` |-> `deploy_dead
                              (H : (bool # bytes32 # type_value) list # num list)
                              tops runtime_bc (am:abstract_machine) tx`,
                            `deploy_bc` |-> `assemble prog`]
           deploy_selected_memory_from_checked) >>
         impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
         disch_then ACCEPT_TAC) >>
     metis_tac[deploy_selected_memory]) >>
  `dunit.cu_context.ctx_entry = SOME "__deploy"` by
    (drule lower_vyper_deploy_unit_entry >> simp[]) >>
  `mem_inv (\c f inst s. inst_dload_in_section inst s /\
                        s.vs_code = vi.vs_code /\
                        s.vs_data_section = vi.vs_data_section)
     dunit.cu_context vi` by
    (simp[mem_inv_raw_reachable] >> rpt strip_tac >>
     drule raw_reachable_code_data >> strip_tac >>
     simp[] >> irule lowered_unit_dload_in_section >>
     metis_tac[]) >>
  qpat_assum `vi.vs_outcomes = vs.vs_outcomes`
    (fn th => qpat_x_assum `deploy_venom_result_rel H _ _ _ _ _`
       (assume_tac o REWRITE_RULE [th])) >>
  qexistsl_tac [`H`, `obs`, `vf`] >> rpt conj_tac >>
  FIRST_ASSUM ACCEPT_TAC
QED

(* e2e_deploy_correctness's hypotheses.  The constructor run's finite
   storage guard depends on the run's GAS observations, so it is stated at
   the new gas for every list of them, as is the exemption premise, the
   deploy counterpart of the call's.  S6b takes the all-dead set: each gas
   variant of the entry state has its own observed horizon, and no common
   finite one exists.  S4 takes its input state before the dead set, which
   is then the dead set at that state's own horizon, so the source's
   result relation carries over to the compiled unit. *)
Theorem e2e_deploy_gas_sufficient_identity:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' /\
      LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64 /\
      (!gs. deploy_storage_ok tops am tx
              (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
      (!obs. ~deploy_gas_source_exempt tops
         (load_contract (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            obs am tx [(NONE, tops)] []))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops \/
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases >> strip_tac >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  (* S1b-d, S6b and S7g-d, at bounds that hold for every creation frame *)
  (* S1b-d: one fuel for every run that ends; each variant's run ends on its
     exit arm (below) *)
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  `lowering_context_ok dunit.cu_context` by metis_tac[deploy_unit_context_ok] >>
  qspecl_then [`tops`, `rpolicy`, `runtime_bc`, `dunit`, `am`, `tx`]
    mp_tac deploy_unit_fns_fuel_stable >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_context_uniform_fuel >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `cplan`, `fuel`]
    mp_tac run_venom_pipeline_run_bounded_raw >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`, `dunit`,
               `dout`, `prog`, `cplan`, `fuel'`, `M`] mp_tac
    (INST_TYPE [alpha |-> ``:256``] deploy_frame_gas_sufficient) >>
  impl_tac >- fs[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  (* the creation frame at the new gas *)
  `deploy_state_rel tops deploy_bc am tx (add_frame_gas g' es)` by
    (irule deploy_state_rel_add_frame_gas >> fs[]) >>
  `wf_state es` by fs[deploy_state_rel_def] >>
  qpat_x_assum `deploy_state_rel _ _ _ _ es` kall_tac >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  qabbrev_tac `vs = deploy_entry_state prog cplan tops (add_frame_gas g' es)` >>
  `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_outcomes = MAP SND (call_trace (add_frame_gas g' es))` by
    simp[Abbr`vs`, deploy_entry_state_def, entry_venom_state_def] >>
  `deploy_bc = assemble prog` by fs[deploy_phases_def] >>
  `K SOME IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  `K SOME <> asm_opt_finalizer` by
    (strip_tac >>
     qpat_x_assum `K SOME = asm_opt_finalizer`
       (fn th => mp_tac (Q.AP_THM
         (Q.AP_THM th `rpolicy with rpol_final_assembly := FAP_Optimize`)
         `[AsmOp "STOP"; AsmOp "STOP"]`)) >>
     EVAL_TAC) >>
  `deploy_state_rel tops (assemble prog) am tx (add_frame_gas g' es)` by fs[] >>
  `opt_deploy_entry_state prog prog cplan tops (add_frame_gas g' es) = vs` by
    (simp[Abbr `vs`] >> irule opt_deploy_entry_state_identity >> metis_tac[]) >>
  `tx with code := vs.vs_code = tx` by
    (qspecl_then [`tops`, `am`, `tx`, `prog`, `cplan`, `add_frame_gas g' es`]
       mp_tac deploy_txp_identity >> simp[]) >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      dout.po_unit.cu_context vs` by
    (Cases_on `deploy_dalloca_form_occurs expr_create_root tops`
     >- (qspecl_then [`K SOME`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
                      `dunit`, `dout`, `prog`, `prog`, `cplan`, `am`, `tx`,
                      `add_frame_gas g' es`, `vs`]
           mp_tac deploy_entry_reachable_create_size_ok >>
         fs[Abbr `vs`, opt_deploy_entry_state_own_identity]) >>
     drule_all deploy_entry_create_size_ok >> simp[]) >>
  qabbrev_tac `Du = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf Du` by simp[Abbr`Du`, dead_wf_def] >>
  `vs = opt_deploy_entry_state_own prog prog cplan tops (add_frame_gas g' es)` by
    metis_tac[opt_deploy_entry_state_own_identity] >>
  `vs.vs_alloca_next = imm_len tops` by
    simp[Abbr `vs`, deploy_entry_state_def, opt_deploy_entry_state_own_def,
         opt_entry_state_own_def, entry_venom_state_def] >>
  qspecl_then [`policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`, `dout`,
               `prog`, `prog`, `cplan`, `add_frame_gas g' es`] mp_tac
    deploy_raw_fmp_exists >>
  impl_tac >- fs[] >> disch_then (qx_choose_then `fmp` strip_assume_tac) >>
  `w2n vs.vs_initial_fmp <= w2n fmp` by
    (qpat_assum `vs = opt_deploy_entry_state_own _ _ _ _ _` SUBST1_TAC >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `cplan.cp_initial_fmp MOD dimword (:256) <= w2n fmp` by
    (qpat_assum `w2n vs.vs_initial_fmp <= w2n fmp` mp_tac >>
     qpat_assum `vs.vs_initial_fmp = _`
       (fn th => PURE_REWRITE_TAC [th, wordsTheory.w2n_n2w]) >>
     simp[]) >>
  `!vi. raw_variant fmp vi vs ==>
      ?(H : (bool # bytes32 # type_value) list # num list) obs efuel.
        raw_unit_memory_ok dunit.cu_context vi /\
        ptr_discipline (imm_len tops) dunit.cu_context vi /\
        taint_within (deploy_dead H tops runtime_bc am tx) dunit.cu_context vi /\
        mem_inv dload_offset_ok dunit.cu_context vi /\
        mem_inv dload_headroom_ok dunit.cu_context vi /\
        mem_inv (\c f inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\
                             s.vs_data_section = vi.vs_data_section)
          dunit.cu_context vi /\
        deploy_venom_result_rel H tops runtime_bc tx
          (load_contract (SOME vs.vs_outcomes) obs am tx [(NONE,tops)] [])
          (run_context efuel dunit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     qspecl_then [`K SOME`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
                  `dunit`, `dout`, `prog`, `prog`, `cplan`, `am`, `tx`,
                  `add_frame_gas g' es`, `vs`, `vi`, `fmp`]
       mp_tac deploy_gas_raw_variant_facts >>
     impl_tac >-
       fs[deploy_gas_source_exempt_def, o1_run_state_ok_def,
          wordsTheory.w2n_n2w] >>
     metis_tac[]) >>
  `venom_run_bounded fuel' M dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
       (qspecl_then [`Du`, `vs`, `fmp`] mp_tac) >>
     impl_tac >- (simp[] >> gen_tac >> strip_tac >>
       qpat_assum `!vi. raw_variant _ vi vs ==> _`
         (qspec_then `vs_in` mp_tac) >>
       impl_tac >- metis_tac[] >> strip_tac >>
       `terminates (run_context fuel dunit.cu_context vs_in)` by
         (qpat_x_assum `!s f. terminates _ ==> _` irule >>
          metis_tac[deploy_venom_result_rel_terminates]) >>
       simp[Abbr `Du`, taint_within_def]) >> simp[]) >>
  (* S4's input state, picked before its dead set *)
  `!eom. max_live_eom dout.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`,
               `fmp`] mp_tac run_venom_pipeline_correct_all_dead >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `!vi. raw_variant _ vi vs ==> _`
    (qspec_then `vs_in` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`H`, `gobs`, `efuel`] strip_assume_tac) >>
  qabbrev_tac `D = deploy_dead H tops runtime_bc am tx` >>
  `dead_wf D` by simp[Abbr`D`, deploy_dead_wf] >>
  `ctx_sim D dunit.cu_context dout.po_unit.cu_context vs_in vs /\
   o1_lowered_inv dout.po_unit.cu_context vs` by metis_tac[] >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `!obs. ~deploy_source_exempt tops
     (load_contract (SOME vs.vs_outcomes) obs am tx [(NONE, tops)] [])`
    by fs[deploy_gas_source_exempt_def] >>
  (* what the compiled constructor returns *)
  `terminates (run_context efuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?vfuel. dead_result_rel D (run_context efuel dunit.cu_context vs_in)
             (run_context vfuel dout.po_unit.cu_context vs)` by
    metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
      (load_contract (SOME vs.vs_outcomes) gobs am tx [(NONE, tops)] [])` by fs[] >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `am`, `tx`,
               `SOME vs.vs_outcomes`, `gobs`,
               `load_contract (SOME vs.vs_outcomes) gobs am tx [(NONE, tops)] []`,
               `run_context efuel dunit.cu_context vs_in`,
               `run_context vfuel dout.po_unit.cu_context vs`] mp_tac
    deploy_venom_result_rel_dead >>
  impl_tac >- fs[Abbr`D`, deploy_state_rel_def] >> strip_tac >>
  qpat_x_assum `!g' am tx es Inv. _`
    (qspecl_then [`g'`, `am`, `tx`, `es`, `raw_reachable vs`] mp_tac) >>
  impl_tac
  >- (fs[Abbr `vs`] >>
      qexistsl_tac [`H`,
        `load_contract (SOME (deploy_entry_state prog cplan tops (add_frame_gas g' es)).vs_outcomes)
           gobs am tx [(NONE, tops)] []`, `vfuel`] >>
      metis_tac[]) >>
  simp[]
QED

Theorem call_gas_static_lowered_inv:
  !H tops ret am tx fuel unit out vs_in vs marks tail.
    tx.is_static /\
    (!rest.
      FST (call_external (SOME vs_in.vs_outcomes)
        (gas_explicit marks vs_in.vs_gas_readings ++ rest) am tx) <>
      INR (Error (RuntimeError "msg.gas: no gas reading"))) /\
    ~gas_source_exempt tops tx
      (call_external (SOME vs_in.vs_outcomes)
        (gas_explicit marks vs_in.vs_gas_readings ++ tail) am tx) /\
    external_call_result_rel H tops ret tx
      (call_external (SOME vs_in.vs_outcomes)
        (gas_explicit marks vs_in.vs_gas_readings ++ tail) am tx)
      (run_context fuel unit.cu_context vs_in) /\
    terminates (run_context fuel unit.cu_context vs_in) /\
    (o1_lowered_inv out.po_unit.cu_context vs \/
     (!n. terminates (run_context n unit.cu_context vs_in) ==>
       ?u. run_context n unit.cu_context vs_in = Abort ExHalt_abort u)) ==>
    o1_lowered_inv out.po_unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!n. terminates _ ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!rest. FST _ <> _` (qspec_then `tail` assume_tac) >>
  gvs[] >> metis_tac[call_static_abort_gas_source_exempt]
QED
