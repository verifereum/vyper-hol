(* End-to-End Vyper-to-EVM Correctness (PLAN §2.1/§8.1).
 * TOP-LEVEL: vyper_call_correct (single-call correctness over fixed storage
 * regions), vyper_call_correct_guarded (per-filling storage guard),
 * e2e_vyper_to_evm (admission-free generic §8.1 composition),
 * e2e_venom_pipeline, compile_vyper_runtime_bytecode (preserved proved APIs).
 * e2e_deploy_correctness (the §5.11 admission) is in e2eDeployCorrectness.
 * Boundary/oracle/entry definitions live below this composition owner.
 * Deployment and gen_fn_simulation are OFF the call's logical dependency path;
 * definition-owner imports are not uses of their admitted correctness facts.
 * TASK056: no active legacy constant/alias. Original retired proof text is
 * retained in inactive SOURCECOMMENT archives; mapping: lowering/e2eLegacy.md.
 * This composes planned stages; it does NOT prove the outstanding stage proofs.
 *)
Theory e2eCorrectness
Ancestors
  ptrDiscipline unitMemInv lowerDloadDefs moduleLoweringProps
  e2eDefs e2eComposition unitTransformDefs e2eDeployDefs
  e2eProducers e2eEntry e2eOptEntry o1PipelineCorrect o1PassContract contextCodegenRel
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringCalldataCorrect callPremiseDispatch dispatchedValueSelection entryStateRel
  loweringShapeProps loweringShapeSource vfmExecution
  passSimulationDefs
  codegenCorrectness immutableCodeLayout asmOptimizer codegenEncodingWf
  spillWordBounds
  sourceUnitExecution gasSummary supportedProgram callTrace frameOutcome
  stateEquiv stateEquivProps
  venomExecSemantics
  vyperABI
  vyperInterpreter
  compileEnv loweringStateRelDefs compileVyper
  venomInst
  vyperStorageFootprint fragGasPathMem fragExecMem fragGasOrigin fragGasMode
  fragExec memSafeRun venomExecProofs unitShapeDefs
  staticAbortDefs codegenStaticAbort o1PipelineMemoryLoweredAbort runtimeLabelEntry
  runtimeSymSrcUnit codegenAsmOpt codegenAsmOptRevert codegenEntryRel asmFrameRel
  o1CodeEndOffset o1PipelineCompose o1StaticPipelineCorrect
  staticShadowDefs staticShadowRun staticShadowO1State runtimeLabelReadiness
  codegenSymRel codegenRel frameRel asmOptNonemptyFinalizer
  stepWriteFootprint contextRawReachable contextPlanLayoutProps
  o1SymStaticData o1SymStaticPipeline venomPipelineDriverProps
  venomCompilerWf venomWf o1LabelFlowCompose
  contextStaticAbortRel
  list callRawVariant ctorDeployRunBounded rawReachableFmp ctxLookupAgreeHelpers
  callCodeTrace callCodeStorage guardSourceAlignment vyperCallFiniteStorageSupport


(* =====================================================================
   Call-Level Correctness (Main Theorem)
   ===================================================================== *)

(* TASK056 RETIRED SOURCE ARCHIVE: original pre-5.5 boundary text below.
   No active local run_call or legacy owner remains. Replacement: e2eDefs plus
   Verifereum frame/trace API. Provenance only, NOT an equivalence claim.

(* ===== run_call: EVM execution of a single call frame ===== *)

(* Execute the current call frame until it completes.
   Keeps stepping while: execution hasn't aborted (ISL r) AND the
   context stack is at least as deep as when we started (our frame
   hasn't been popped yet).

   Returns SOME es' when the frame completes:
   - Normal case (depth > 1): our frame was popped by handle_exception,
     result incorporated into the caller's context. es' has the
     caller's context on top with returndata set, success flag pushed
     on stack, accounts updated or rolled back.
   - Outermost frame (depth = 1): handle_exception reraises, result
     is (INR exc_opt, es').
   - vfm_abort: hard abort, returns (INR exc_opt, es') with our
     frame still on the stack.
   Returns NONE only for non-termination (impossible with finite gas). *)
Definition run_call_def:
  run_call es =
    let depth = LENGTH es.contexts in
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ depth)
           (step o SND)
           (INL (), es)
End

(* ===== Pre-call state correspondence ===== *)

(* The EVM is starting a fresh call to compiled Vyper bytecode, and
   the runtime state corresponds to the Vyper abstract machine / tx.
   Covers: fresh call frame setup, account/storage correspondence,
   call parameters, block/chain context, type environment, and
   source deployment. *)
Definition call_state_rel_def:
  call_state_rel (program : toplevel list) bytecode am tx tenv
                 (ctxt : context) (rb : rollback_state)
                 (txp : transaction_parameters) ⇔
    (* Fresh call frame: bytecode loaded, pc=0, empty stack *)
    ctxt.msgParams.code = bytecode ∧
    ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode ∧
    ctxt.pc = 0 ∧
    ctxt.stack = [] ∧
    ctxt.logs = [] ∧
    ctxt.returnData = [] ∧
    buffer_to_list ctxt.memory = [] ∧
    (* Accounts and transient storage match *)
    rb.accounts = am.accounts ∧
    rb.tStorage = am.tStorage ∧
    (* Call parameters match *)
    ctxt.msgParams.caller = tx.sender ∧
    ctxt.msgParams.callee = tx.target ∧
    ctxt.msgParams.value = tx.value ∧
    (* Block and chain context match *)
    txp.origin = tx.origin ∧
    txp.gasPrice = tx.gas_price ∧
    txp.baseFeePerGas = tx.base_fee ∧
    txp.blockNumber = tx.block_number ∧
    txp.blockTimeStamp = tx.time_stamp ∧
    txp.blockCoinBase = tx.coinbase ∧
    txp.blockGasLimit = tx.gas_limit ∧
    txp.chainId = tx.chain_id ∧
    txp.blobHashes = tx.blob_hashes ∧
    txp.baseFeePerBlobGas = tx.blob_base_fee ∧
    (* Type environment is derived from program *)
    tenv = type_env program ∧
    (* Source is deployed at target address *)
    (∃mods. ALOOKUP am.sources tx.target = SOME mods)
End

(* ===== Valid call ===== *)

(* The calldata encodes a valid call to an exported function of
   the Vyper program. Binds ret (return type) which is needed
   by the postcondition for ABI encoding of the return value. *)
Definition valid_vyper_call_def:
  valid_vyper_call am tx tenv calldata ret ⇔
    ∃mut nr args dflts body.
      lookup_exported_function
        (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
        tx.function_name = SOME (mut, nr, args, dflts, ret, body) ∧
      calldata_encodes tenv tx.function_name (MAP SND args) tx.args
        calldata
End

Definition compiled_event_info_def:
  compiled_event_info program =
    build_event_info (type_env program) program
      ((K NONE) : string -> (num # type list # bool list) option)
End

(* ===== Post-call result correspondence ===== *)

(* Relates the result of call_external to the EVM state after
   run_call completes. Takes both the starting state es and final
   state es_f, making preserved/changed fields explicit.

   Handles both outermost (r = INR exc_opt) and inner
   (r = INL (), frame popped) calls.

   Key uniformities across both cases:
   - Returndata: always in (FST (HD es_f.contexts)).returnData
     (callee's context for outermost; caller's after set_return_data
     for inner — handle_exception copies it before popping)
   - Accounts on success: es_f.rollback.accounts = am'.accounts
     (update_accounts modifies rollback; pop doesn't change it
     on success)
   - Accounts on revert: outermost leaves dirty accounts (caller
     handles rollback via r = INR (SOME Reverted)); inner has
     pop_and_incorporate_context restore pre-call rollback
   - Logs: callee's new EVM logs appended to the caller's pre-call
     logs. For outermost, pre-call logs are [] (callee's context
     started empty). For inner, they come from HD (TL es.contexts).
   - txParams: unchanged *)

(* Helper: the caller's logs before the call.
   Outermost (no caller): [].
   Inner: logs from the caller's context in the original state. *)
Definition caller_pre_logs_def:
  caller_pre_logs [] = ([] : event list) ∧
  caller_pre_logs (((ctxt : context), rb) :: _) = ctxt.logs
End

Definition call_result_matches_def:
  call_result_matches tenv event_info am tx ret r es es_f ⇔
    ∃ctxt_hd rb_hd accts tstor accs tdel md.
    (* es_f is es with contexts, rollback, msdomain updated.
       txParams preserved. Deeper contexts preserved. *)
    es_f = es with <|
      contexts := (ctxt_hd, rb_hd) :: TL (TL es.contexts);
      rollback := es.rollback with <|
        accounts := accts; tStorage := tstor;
        accesses := accs; toDelete := tdel
      |>;
      msdomain := md
    |> ∧
    case call_external_simple am tx of
      (INL v, am') =>
        (* EVM indicates success *)
        (r = INR NONE ∨
         (r = INL () ∧
          ¬NULL ctxt_hd.stack ∧ HD ctxt_hd.stack = 1w)) ∧
        (* Returndata encodes the return value *)
        return_data_encodes tenv ret v es_f ∧
        (* Accounts and transient storage committed *)
        accts = am'.accounts ∧ tstor = am'.tStorage ∧
        (* Callee's new logs correspond to Vyper's logs *)
        (∃evm_logs.
           ctxt_hd.logs =
             caller_pre_logs (TL es.contexts) ++ evm_logs ∧
           logs_correspond event_info tenv tx.target
             am'.logs evm_logs)
    | (INR (AssertException _), _) =>
        (* Outermost: r signals revert, caller handles rollback.
           Inner: frame popped, caller sees 0w on stack,
           accounts rolled back by pop_and_incorporate_context. *)
        r = INR (SOME Reverted) ∨
        (r = INL () ∧
         ¬NULL ctxt_hd.stack ∧ HD ctxt_hd.stack = 0w ∧
         accts = am.accounts ∧ tstor = am.tStorage)
    | (INR (Error _), _) => T
    | (INR BreakException, _) => F
    | (INR ContinueException, _) => F
    | (INR (ReturnException _), _) => F
End

*)

(* ===== Generic three-stage composition (PLAN §8.1) ===== *)

(* The stages are explicit premises, not appeals to admitted S1-S7.
   Source exemption is handled before the conditional stages are opened.
   Totality supplies an actual EVM run even when neither stage applies.
   The middle stage matches runs up to the source result's dead bytes
   (external_call_dead), which the source relation ignores. *)
(* The reconstructed raw oracle need not satisfy initial_ctx_rel: that
   relation ties the output entry state to the actual EVM readings. *)
Theorem e2e_vyper_to_evm_states:
  !gobs tops ret am tx ctx ctx' vs_in vs_out es.
    external_return_type tops tx.function_name = ret /\
    vs_in.vs_outcomes = MAP SND (call_trace es) /\
    (?fuel. external_call_result_rel
              (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gobs))
              tops ret tx
              (call_external (SOME vs_in.vs_outcomes) gobs am tx)
              (run_context fuel ctx vs_in)) /\
    (~source_exempt tops (call_external (SOME vs_in.vs_outcomes) gobs am tx) ==>
       ctx_sim (external_call_dead
                  (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gobs)) tx
                  (call_external (SOME vs_in.vs_outcomes) gobs am tx))
         ctx ctx' vs_in vs_out /\
       !fuel. ?r es'.
         run_call es = SOME (r, es') /\
         (frame_resource_starved es r es' \/
          venom_frame_rel es r es' (run_context fuel ctx' vs_out)))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/
             call_result_rel_at gobs tops am tx es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `source_exempt tops (call_external (SOME vs_in.vs_outcomes) gobs am tx)`
  >- (disj2_tac >> irule source_exempt_call_result_rel >> gvs[]) >>
  gvs[] >>
  drule_all external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  `terminates (run_context fuel' ctx' vs_out)` by
    metis_tac[dead_result_rel_terminates] >>
  qpat_x_assum `!fuel. frame_resource_starved es r es' \/ _`
    (qspec_then `fuel'` strip_assume_tac) >>
  gvs[] >>
  drule_all external_call_result_rel_dead_transport >> strip_tac >>
  metis_tac[external_call_result_rel_frame]
QED

Theorem e2e_vyper_to_evm:
  !gobs tops ret am tx ctx ctx' vs es.
    external_return_type tops tx.function_name = ret /\
    vs.vs_outcomes = MAP SND (call_trace es) /\
    (?fuel. external_call_result_rel
              (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gobs))
              tops ret tx
              (call_external (SOME vs.vs_outcomes) gobs am tx)
              (run_context fuel ctx vs)) /\
    (~source_exempt tops (call_external (SOME vs.vs_outcomes) gobs am tx) ==>
       ctx_sim (external_call_dead
                  (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gobs)) tx
                  (call_external (SOME vs.vs_outcomes) gobs am tx))
         ctx ctx' vs vs /\
       !fuel. ?r es'.
         run_call es = SOME (r, es') /\
         (frame_resource_starved es r es' \/
          venom_frame_rel es r es' (run_context fuel ctx' vs)))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/
             call_result_rel_at gobs tops am tx es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `source_exempt tops (call_external (SOME vs.vs_outcomes) gobs am tx)`
  >- (disj2_tac >> irule source_exempt_call_result_rel >> gvs[]) >>
  gvs[] >>
  drule_all external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  `terminates (run_context fuel' ctx' vs)` by
    metis_tac[dead_result_rel_terminates] >>
  (* gvs identifies every stage-3 witness with the actual run by uniqueness. *)
  qpat_x_assum `!fuel. frame_resource_starved es r es' \/ _`
    (qspec_then `fuel'` strip_assume_tac)
  >- gvs[] >>
  gvs[] >>
  drule_all external_call_result_rel_dead_transport >> strip_tac >>
  metis_tac[external_call_result_rel_frame]
QED

(* TASK056 RETIRED PROOF ARCHIVE: old schemas/proofs preserved verbatim.
   Replacement mapping: lowering/e2eLegacy.md. No active legacy API below.
(* ===== Adapter Lemmas for vyper_call_correct ===== *)
(* TASK049: every theorem below remains a LEGACY claim. In particular the
   existing admitted bridge and codegen dependencies are not new certificates.
   Clean PLAN 5.5 composition will be provided by TASK054/056. *)

(* The checked-unit correspondence below combines the explicit compilation,
   source-deployment, transform, codegen, and finalizer interfaces.  These
   small adapters keep initial-state and valid-call conversions local to the
   call-level consumer. *)
Theorem call_state_rel_initial_evm_rel_legacy[local]:
  !program cp bytecode am tx tenv ctxt rb rest es vs.
    initial_codegen_state_rel cp vs /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel_legacy program bytecode am tx tenv ctxt rb es.txParams /\
    rb.accounts = vs.vs_accounts /\
    rb.tStorage = vs.vs_transient /\
    ctxt.returnData = vs.vs_returndata /\
    ctxt.logs = vs.vs_logs /\
    (!i. read_byte i vs.vs_memory = read_byte i (buffer_to_list ctxt.memory)) /\
    buffer_to_list ctxt.msgParams.data = vs.vs_call_ctx.cc_calldata
    ==>
    initial_evm_rel_legacy cp bytecode vs es
Proof
(* Original proof text:
Proof
  rw[call_state_rel_def, initial_evm_rel_def] >> metis_tac[]
QED
*)
  rw[call_state_rel_legacy_def, initial_evm_rel_legacy_def] >> metis_tac[]
QED

Theorem valid_vyper_call_valid_function_call_legacy[local]:
  !am tx tenv selectors calldata args ret mut nr dflts body.
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
      tx.function_name = SOME (mut, nr, args, dflts, ret, body) /\
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args calldata /\
    (?sel fn_lbl htz.
       MEM (sel, fn_lbl, htz) selectors /\
       selector_matches sel tx.function_name
         (vyper_to_abi_types tenv (MAP SND args)))
    ==>
    valid_function_call_legacy tenv am tx selectors calldata args ret
Proof
(* Original proof text:
Proof
  rw[valid_function_call_def] >> metis_tac[]
QED
*)
  rw[valid_function_call_legacy_def] >> metis_tac[]
QED

Theorem log_entry_equiv_log_entry_corresponds[local]:
  !cenv event_info tenv addr l ev.
    cenv.ce_type_env = tenv /\ cenv.ce_event_info = event_info ==>
    (log_entry_equiv cenv addr l ev <=>
     log_entry_corresponds event_info tenv addr l ev)
Proof
  simp[log_entry_equiv_def, log_entry_corresponds_def]
QED

Theorem external_logs_rel_logs_correspond[local]:
  !cenv event_info tenv addr am ss.
    cenv.ce_type_env = tenv /\ cenv.ce_event_info = event_info ==>
    (external_logs_rel cenv addr am ss <=>
     logs_correspond event_info tenv addr am.logs ss.vs_logs)
Proof
  rw[external_logs_rel_def, logs_correspond_def] >>
  `log_entry_equiv cenv addr =
   log_entry_corresponds cenv.ce_event_info cenv.ce_type_env addr`
    by simp[FUN_EQ_THM, log_entry_equiv_log_entry_corresponds] >>
  simp[]
QED

(* LEGACY source-unit obligation (replacement TASK051, removal TASK056).
   The source semantics of the exact packaged compilation unit is an explicit
   boundary obligation.  In particular, it is not reconstructed from the
   weaker observable equivalence used by generic transform correctness. *)
Definition source_unit_execution_correct_legacy_def:
  source_unit_execution_correct_legacy tenv cenv am tx ret
    (unit : compilation_unit) vs <=>
    ?fuel. external_call_result_rel_legacy tenv cenv
      (initial_evaluation_context am.sources am.layouts tx
        (find_function_module am tx.target tx.function_name))
      ret (call_external_simple am tx) (run_context fuel unit.cu_context vs)
End

(* TASK051: old alias theorem/proof retained with the explicit legacy result
   name; NOT an equivalence with the new oracle-mode boundary.
   Previous saved name: source_unit_execution_correct. Removal TASK056. *)
Theorem source_unit_execution_correct_legacy:
  source_unit_execution_correct_legacy tenv cenv am tx ret unit vs <=>
  ?fuel. external_call_result_rel_legacy tenv cenv
    (initial_evaluation_context am.sources am.layouts tx
      (find_function_module am tx.target tx.function_name))
    ret (call_external_simple am tx) (run_context fuel unit.cu_context vs)
Proof
  (* Original proof text:
Proof
  simp[source_unit_execution_correct_def]
QED
  *)
  simp[source_unit_execution_correct_legacy_def]
QED
Theorem run_context_zero_error[local]:
  !ctx vs. ?e. run_context 0 ctx vs = Error e
Proof
  rpt gen_tac >> Cases_on `ctx.ctx_entry`
  >- simp[run_context_def]
  >> rename1 `ctx.ctx_entry = SOME entry` >>
     Cases_on `lookup_function entry ctx.ctx_functions`
  >- simp[run_context_def]
  >> rename1 `lookup_function entry ctx.ctx_functions = SOME fn` >>
     Cases_on `fn_entry_label fn`
  >- simp[run_context_def, run_function_def]
  >> simp[run_context_def, run_function_def, Once run_blocks_def]
QED

(* TASK049 original proof text retained verbatim:
Proof
  rpt strip_tac >>
  gvs[source_unit_execution_correct_def,
      checked_unit_transform_correct_legacy_def,
      ctx_transform_correct_legacy_def, pass_correct_def] >>
  `!r1 r2. lift_result R_ok R_term R_term r1 r2 ==>
           observable_result_equiv r1 r2` by
    (rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
     fs[lift_result_def, observable_result_equiv_def,
        observable_equiv_def, revert_equiv_def] >>
     metis_tac[]) >>
  Cases_on `terminates (run_context fuel unit.cu_context vs)`
  >- (`?fuel'. terminates
          (run_context fuel' out.po_unit.cu_context vs)` by metis_tac[] >>
      qexistsl [`fuel`, `fuel'`] >>
      metis_tac[])
  >> Cases_on `run_context fuel unit.cu_context vs` >>
     gvs[terminates_def] >>
     qspecl_then [`out.po_unit.cu_context`, `vs`] strip_assume_tac
       run_context_zero_error >>
     qexistsl [`fuel`, `0`] >>
     gvs[observable_result_equiv_def]
QED
*)
Theorem source_unit_execution_through_pipeline[local]:
  !tenv cenv am tx ret unit vs pipeline rpolicy out R_ok R_term.
    source_unit_execution_correct_legacy tenv cenv am tx ret unit vs /\
    pipeline rpolicy unit = SOME out /\
    checked_unit_transform_correct_legacy pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2)
    ==>
    ?fuel fuel'.
      external_call_result_rel_legacy tenv cenv
        (initial_evaluation_context am.sources am.layouts tx
          (find_function_module am tx.target tx.function_name))
        ret (call_external_simple am tx) (run_context fuel unit.cu_context vs) /\
      observable_result_equiv
        (run_context fuel unit.cu_context vs)
        (run_context fuel' out.po_unit.cu_context vs)
Proof
  rpt strip_tac >>
  (* Original first rewrite: gvs[source_unit_execution_correct_def, *)
  gvs[source_unit_execution_correct_legacy_def,
      checked_unit_transform_correct_legacy_def,
      ctx_transform_correct_legacy_def, pass_correct_def] >>
  `!r1 r2. lift_result R_ok R_term R_term r1 r2 ==>
           observable_result_equiv r1 r2` by
    (rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
     fs[lift_result_def, observable_result_equiv_def,
        observable_equiv_def, revert_equiv_def] >>
     metis_tac[]) >>
  Cases_on `terminates (run_context fuel unit.cu_context vs)`
  >- (`?fuel'. terminates
          (run_context fuel' out.po_unit.cu_context vs)` by metis_tac[] >>
      qexistsl [`fuel`, `fuel'`] >>
      metis_tac[])
  >> Cases_on `run_context fuel unit.cu_context vs` >>
     gvs[terminates_def] >>
     qspecl_then [`out.po_unit.cu_context`, `vs`] strip_assume_tac
       run_context_zero_error >>
     qexistsl [`fuel`, `0`] >>
     gvs[observable_result_equiv_def]
QED

(* TASK049 original theorem statement/proof retained verbatim:
Theorem e2e_vyper_to_evm:
  !tops pipeline finalizer policy rpolicy unit out prog deploy_bc runtime_bc
   cp name i r fn off Inv cenv am tx tenv ret ctxt rb rest es vs R_ok R_term.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    runtime_bc = assemble prog /\
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc) /\
    source_deployment_rel tops am tx cenv /\
    source_unit_execution_correct tenv cenv am tx ret unit vs /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    out.po_unit.cu_context.ctx_entry = SOME name /\
    lookup_function name out.po_unit.cu_context.ctx_functions = SOME fn /\
    i < LENGTH out.po_unit.cu_context.ctx_functions /\
    EL i out.po_unit.cu_context.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    contextCodegenRel$codegen_context_obligations
      Inv out.po_unit.cu_context cp /\
    contextCodegenRel$codegen_reachability_package
      Inv out.po_unit.cu_context vs /\
    initial_codegen_state_rel cp vs /\
    codegenCorrectness$initial_ctx_rel_legacy cp prog off
      out.po_unit.cu_context vs es /\
    asm_pc_to_offset prog off = 0 /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel tops runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call am tx tenv (buffer_to_list ctxt.msgParams.data) ret /\
    cenv.ce_type_env = tenv /\
    cenv.ce_event_info = compiled_event_info tops /\
    checked_unit_transform_correct_legacy pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    finalizer_correct rpolicy finalizer
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence tenv (compiled_event_info tops) ret am tx es
Proof
  rpt strip_tac >>
  drule_all source_unit_execution_through_pipeline >> strip_tac >>
  drule_all codegen_correct_legacy >> strip_tac >>
  qpat_x_assum `!fuel. ?gas_needed. _`
    (qspec_then `fuel'` strip_assume_tac) >>
  qexists `gas_needed` >> strip_tac >>
  first_x_assum (qspec_then `es` mp_tac) >>
  (impl_tac >- (gvs[call_state_rel_def])) >>
  strip_tac >>
  Cases_on `call_external_simple am tx` >>
  rename1 `call_external_simple am tx = (src_result, am')` >>
  Cases_on `src_result` >>
  Cases_on `run_context fuel unit.cu_context vs` >>
  Cases_on `run_context fuel' out.po_unit.cu_context vs` >>
  gvs[external_call_result_rel_def, observable_result_equiv_def,
      observable_equiv_def, revert_equiv_def,
      vyper_evm_correspondence_def] >>
  gvs[return_data_encodes_def, state_effects_match_def,
      final_state_rel_def, external_call_state_rel_def,
      initial_evaluation_context_def]
  >- (Cases_on `es'.contexts` >> gvs[] >> PairCases_on `h` >>
      gvs[] >> metis_tac[external_logs_rel_logs_correspond])
  >- (Cases_on `y` >> Cases_on `a` >>
      gvs[external_call_result_rel_def])
  >> Cases_on `y` >> gvs[external_call_result_rel_def]
QED

*)

(* Preserved legacy composition proof, STAGE-ADMITTED, not PLAN 5.5
   correctness. TASK054: renamed from e2e_vyper_to_evm; original proof text
   is unchanged. Removal owner TASK056. No old/new equivalence is claimed. *)
Theorem e2e_vyper_to_evm_legacy:
  !tops pipeline finalizer policy rpolicy unit out prog deploy_bc runtime_bc
   cp name i r fn off Inv cenv am tx tenv ret ctxt rb rest es vs R_ok R_term.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    runtime_bc = assemble prog /\
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc) /\
    source_deployment_rel_legacy tops am tx cenv /\
    source_unit_execution_correct_legacy tenv cenv am tx ret unit vs /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    out.po_unit.cu_context.ctx_entry = SOME name /\
    lookup_function name out.po_unit.cu_context.ctx_functions = SOME fn /\
    i < LENGTH out.po_unit.cu_context.ctx_functions /\
    EL i out.po_unit.cu_context.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    contextCodegenRel$codegen_context_obligations
      Inv out.po_unit.cu_context cp /\
    contextCodegenRel$codegen_reachability_package
      Inv out.po_unit.cu_context vs /\
    initial_codegen_state_rel cp vs /\
    codegenCorrectness$initial_ctx_rel_legacy cp prog off
      out.po_unit.cu_context vs es /\
    asm_pc_to_offset prog off = 0 /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel_legacy tops runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call_legacy am tx tenv (buffer_to_list ctxt.msgParams.data) ret /\
    cenv.ce_type_env = tenv /\
    cenv.ce_event_info = compiled_event_info tops /\
    checked_unit_transform_correct_legacy pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    finalizer_correct_legacy rpolicy finalizer
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence_legacy tenv (compiled_event_info tops) ret am tx es
Proof
  rpt strip_tac >>
  drule_all source_unit_execution_through_pipeline >> strip_tac >>
  drule_all codegen_correct_legacy >> strip_tac >>
  qpat_x_assum `!fuel. ?gas_needed. _`
    (qspec_then `fuel'` strip_assume_tac) >>
  qexists `gas_needed` >> strip_tac >>
  first_x_assum (qspec_then `es` mp_tac) >>
  (impl_tac >- (gvs[call_state_rel_legacy_def])) >>
  strip_tac >>
  Cases_on `call_external_simple am tx` >>
  rename1 `call_external_simple am tx = (src_result, am')` >>
  Cases_on `src_result` >>
  Cases_on `run_context fuel unit.cu_context vs` >>
  Cases_on `run_context fuel' out.po_unit.cu_context vs` >>
  (* TASK051 original rewrite: external_call_result_rel_def. The identical
     NONE-mode contract now has its explicit _legacy name. *)
  gvs[external_call_result_rel_legacy_def, observable_result_equiv_def,
      observable_equiv_def, revert_equiv_def,
      vyper_evm_correspondence_legacy_def] >>
  gvs[return_data_encodes_legacy_def, state_effects_match_legacy_def,
      final_state_rel_def, external_call_state_rel_def,
      initial_evaluation_context_def]
  >- (Cases_on `es'.contexts` >> gvs[] >> PairCases_on `h` >>
      gvs[] >> metis_tac[external_logs_rel_logs_correspond])
  >- (Cases_on `y` >> Cases_on `a` >>
      gvs[external_call_result_rel_legacy_def])
  >> Cases_on `y` >> gvs[external_call_result_rel_legacy_def]
QED

(* ===== Main Correctness Theorem ===== *)

(* LEGACY compiler correctness for a single external call.

   When EVM execution enters compiled Vyper bytecode (at any point
   in the call stack), the result corresponds to the Vyper source
   semantics (the NONE-mode pair projection call_external_simple am tx).

   Covers both outermost calls (rest = [], as in a transaction) and
   inner calls (rest ≠ [], as in a CALL from another contract).
   The pipeline and all Venom-internal details are hidden in the proof.

   Gas is existential: there exists a gas bound such that with enough
   gas, EVM execution produces the correct result. *)
(* TASK049's original statement and proof of the legacy wrapper
   (vyper_call_correct_legacy below), kept as text, not compiled:
Theorem vyper_call_correct_legacy:
  !tops pipeline finalizer policy rpolicy unit out prog deploy_bc runtime_bc
   cp name i r fn off Inv cenv am tx tenv ret ctxt rb rest es vs R_ok R_term.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    runtime_bc = assemble prog /\
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc) /\
    source_deployment_rel tops am tx cenv /\
    source_unit_execution_correct tenv cenv am tx ret unit vs /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    out.po_unit.cu_context.ctx_entry = SOME name /\
    lookup_function name out.po_unit.cu_context.ctx_functions = SOME fn /\
    i < LENGTH out.po_unit.cu_context.ctx_functions /\
    EL i out.po_unit.cu_context.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    contextCodegenRel$codegen_context_obligations
      Inv out.po_unit.cu_context cp /\
    contextCodegenRel$codegen_reachability_package
      Inv out.po_unit.cu_context vs /\
    initial_codegen_state_rel cp vs /\
    codegenCorrectness$initial_ctx_rel_legacy cp prog off
      out.po_unit.cu_context vs es /\
    asm_pc_to_offset prog off = 0 /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel tops runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call am tx tenv (buffer_to_list ctxt.msgParams.data) ret /\
    cenv.ce_type_env = tenv /\
    cenv.ce_event_info = compiled_event_info tops /\
    checked_unit_transform_correct_legacy pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    finalizer_correct rpolicy finalizer
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence tenv (compiled_event_info tops) ret am tx es
Proof
  rpt strip_tac >> drule_all e2e_vyper_to_evm >> simp[]
QED

*)

(* Preserved legacy wrapper, STAGE-ADMITTED. Its existing admitted
   dependencies remain classified as such; NOT a new-boundary certificate.
   Not the top theorem: that is vyper_call_correct at the end. *)
Theorem vyper_call_correct_legacy:
  !tops pipeline finalizer policy rpolicy unit out prog deploy_bc runtime_bc
   cp name i r fn off Inv cenv am tx tenv ret ctxt rb rest es vs R_ok R_term.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    runtime_bc = assemble prog /\
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc) /\
    source_deployment_rel_legacy tops am tx cenv /\
    source_unit_execution_correct_legacy tenv cenv am tx ret unit vs /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    out.po_unit.cu_context.ctx_entry = SOME name /\
    lookup_function name out.po_unit.cu_context.ctx_functions = SOME fn /\
    i < LENGTH out.po_unit.cu_context.ctx_functions /\
    EL i out.po_unit.cu_context.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    contextCodegenRel$codegen_context_obligations
      Inv out.po_unit.cu_context cp /\
    contextCodegenRel$codegen_reachability_package
      Inv out.po_unit.cu_context vs /\
    initial_codegen_state_rel cp vs /\
    codegenCorrectness$initial_ctx_rel_legacy cp prog off
      out.po_unit.cu_context vs es /\
    asm_pc_to_offset prog off = 0 /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel_legacy tops runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call_legacy am tx tenv (buffer_to_list ctxt.msgParams.data) ret /\
    cenv.ce_type_env = tenv /\
    cenv.ce_event_info = compiled_event_info tops /\
    checked_unit_transform_correct_legacy pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    finalizer_correct_legacy rpolicy finalizer
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence_legacy tenv (compiled_event_info tops) ret am tx es
Proof
  (* Original proof text retained above verbatim under TASK049 provenance.
     TASK054 changes only the target name of this legacy caller. *)
  rpt strip_tac >> drule_all e2e_vyper_to_evm_legacy >> simp[]
QED

*)

(* entry_venom_state_initial_venom_state_rel for opt_entry_state.  Stated
   here rather than in e2eEntry because the proof uses e2eProducers. *)
Theorem opt_entry_initial_venom_state_rel:
  !tops prog prog' am tx es cplan.
  call_state_rel tops (assemble prog') am tx es ==>
  initial_venom_state_rel tops am
    (tx with code := (opt_entry_state prog prog' cplan es).vs_code)
    (opt_entry_state prog prog' cplan es)
Proof
  rpt strip_tac >>
  drule_then (qspec_then `cplan` mp_tac) entry_venom_state_initial_venom_state_rel >>
  simp[initial_venom_state_rel_def, venom_env_rel_def, opt_entry_state_def,
       entry_venom_state_frame_fields] >>
  simp[entry_venom_state_def] >> strip_tac >>
  gvs[value_transfer_ok_def, accounts_after_transfer_def,
      loweringStateRelDefsTheory.tx_env_ok_def,
      loweringStateRelDefsTheory.call_ctx_rel_def]
QED

(* generated_entry_code_layout_shape for opt_entry_state.  Stated here
   rather than in e2eEntry because the proof uses e2eProducers and
   immutableCodeLayout. *)
Theorem opt_entry_code_layout_valid:
  !tops prog prog' am tx es cplan policy unit.
  call_state_rel tops (assemble prog') am tx es /\
  codegen_assembly policy unit = SOME prog /\ unit_shape_ok unit ==>
  code_layout_valid (opt_entry_state prog prog' cplan es)
Proof
  rpt strip_tac >>
  drule_all codegenEncodingWfTheory.codegen_assembly_asm_encoding_wf >> strip_tac >>
  drule codegen_assembly_success_shape >> strip_tac >>
  `FLOOKUP (SND (compute_label_offsets prog)) "code_end" =
     SOME (LENGTH (assemble prog))` by
    (irule immutable_code_end_length >> fs[] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  `LENGTH (assemble prog) < 65536` by
    (qpat_x_assum `asm_encoding_wf prog` mp_tac >>
     qpat_x_assum `FLOOKUP _ "code_end" = _` mp_tac >>
     Cases_on `compute_label_offsets prog` >>
     simp[asmWfTheory.asm_encoding_wf_def] >> rpt strip_tac >>
     qpat_x_assum `!lbl off. _` drule >> strip_tac >>
     drule spillWordBoundsTheory.encode_num_bytes_length_bound >>
     simp[symbolResolveTheory.symbol_size_def]) >>
  `LENGTH (FST (HD es.contexts)).msgParams.code <= 24576` by
    metis_tac[call_state_rel_code_length] >>
  simp[code_layout_valid_def, opt_entry_state_def,
       entry_venom_state_frame_fields] >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  qpat_x_assum `prog = _` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- (qexists_tac `LENGTH (assemble prog)` >> asm_rewrite_tac[]) >>
  decide_tac
QED

(* Raw-variant bridge for the generic call link. *)
Theorem raw_variant_opt_entry_calldata_bound:
  !tops bc am tx prog prog' cp es fmp vs.
    call_state_rel tops bc am tx es /\
    raw_variant fmp vs (opt_entry_state prog prog' cp es) ==>
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64
Proof
  rpt strip_tac >>
  drule raw_variant_call_ctx >> strip_tac >>
  gvs[opt_entry_state_def, entry_venom_state_def,
      call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
      evm_state_ok_def,
      vfmCalldataBoundTheory.calldata_bounded_def] >>
  metis_tac[vfmBufferTheory.LENGTH_buffer_to_list]
QED

(* Dispatch reads the function name and arguments from the transaction. *)
Theorem dispatched_vyper_call_code_update:
  dispatched_vyper_call tops (tx with code := c) calldata ret <=>
  dispatched_vyper_call tops tx calldata ret
Proof
  simp[dispatched_vyper_call_def]
QED

(* The storage guard is unchanged when execution cannot read its own code. *)
Theorem call_storage_ok_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (call_storage_ok am (tx with code := c) os gobs <=>
   call_storage_ok am tx os gobs)
Proof
  strip_tac >>
  `source_storage_trace am (tx with code := c) os gobs =
   source_storage_trace am tx os gobs` by
    simp[source_storage_trace_def, call_external_trace_no_self_code_update] >>
  Cases_on `storage_trace_horizon (source_storage_trace am tx os gobs)` >>
  simp[call_storage_ok_def, call_storage_checks_code_update]
QED

(* The source result and storage horizon come from the same traced call. *)
Theorem call_result_rel_at_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (call_result_rel_at gobs tops am (tx with code := c) es r es' <=>
   call_result_rel_at gobs tops am tx es r es')
Proof
  strip_tac >>
  simp[call_result_rel_at_def, LET_THM, source_storage_trace_def,
       call_external_def, call_external_trace_no_self_code_update,
       tx_return_bytes_def, effects_agree_def]
QED

(* Transport the storage guard and result at each gas observation. *)
Theorem call_result_rel_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (call_result_rel_guarded tops am (tx with code := c) es r es' <=>
   call_result_rel_guarded tops am tx es r es')
Proof
  strip_tac >>
  drule_all_then (fn th =>
    simp[call_result_rel_guarded_def, LET_THM, th, call_result_rel_at_code_update])
    call_storage_ok_code_update
QED

(* ===== PLAN §2.1 call theorem: seven stage leaves, raw O1 source domain ===== *)
(* The call theorem at one fixed gas marking, then at every guarded filling of
   the frame's gas readings through the gas link. *)

Theorem call_at_horizon_composition[local]:
  run_call es = SOME (r, es') /\ ~frame_resource_starved es r es' /\
  external_return_type tops tx.function_name = ret /\
  external_call_result_rel
    (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
    tops ret tx (call_external (SOME (MAP SND (call_trace es))) gs am tx)
    (run_context fuel ctx vs) /\
  ctx_sim
    (external_call_dead
      (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
      tx (call_external (SOME (MAP SND (call_trace es))) gs am tx))
    ctx ctx' vs vs' /\
  (!n. ?r' es''. run_call es = SOME (r', es'') /\
    (frame_resource_starved es r' es'' \/
     venom_frame_rel es r' es'' (run_context n ctx' vs'))) ==>
  call_result_rel_at gs tops am tx es r es'
Proof
  rpt strip_tac >>
  drule_all external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  qpat_x_assum `!n. ?r' es''. _` (qspec_then `fuel'` strip_assume_tac) >>
  gvs[] >>
  drule_all external_call_result_rel_dead_transport >> strip_tac >>
  metis_tac[external_call_result_rel_frame]
QED

(* An ExHalt source run needs only the coarse exceptional S7 observation:
   simulation preserves the abort shape, not necessarily the abort tag. *)
Theorem call_at_horizon_static_abort_composition:
  run_call es = SOME (r,es') /\ ~frame_resource_starved es r es' /\
  external_return_type tops tx.function_name = ret /\
  external_call_result_rel
    (storage_trace_horizon
      (source_storage_trace am tx (MAP SND (call_trace es)) gs))
    tops ret tx (call_external (SOME (MAP SND (call_trace es))) gs am tx)
    (run_context fuel ctx vs) /\
  ctx_sim
    (external_call_dead
      (storage_trace_horizon
        (source_storage_trace am tx (MAP SND (call_trace es)) gs))
      tx (call_external (SOME (MAP SND (call_trace es))) gs am tx))
    ctx ctx' vs vs' /\
  (!n. terminates (run_context n ctx vs) ==>
    ?u. run_context n ctx vs = Abort ExHalt_abort u) /\
  (!n a u. run_context n ctx' vs' = Abort a u ==>
    ?r' es''. run_call es = SOME (r',es'') /\
      (frame_resource_starved es r' es'' \/
       ?exc out lgs. frame_outcome es r' es'' (SOME exc) out lgs)) ==>
  call_result_rel_at gs tops am tx es r es'
Proof
  rpt strip_tac >>
  drule external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `!n. terminates _ ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  `?a u'. run_context fuel' ctx' vs' = Abort a u'` by
    (Cases_on `run_context fuel' ctx' vs'` >> gvs[dead_result_rel_def]) >>
  qpat_x_assum `!n a u. _` (qspecl_then [`fuel'`, `a`, `u'`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `external_call_result_rel _ _ _ _ src _` >>
  PairCases_on `src` >> gvs[call_result_rel_at_def] >>
  Cases_on `src0` >> gvs[external_call_result_rel_def] >>
  rename1 `call_external _ _ _ _ = (INR source_exc,_,_)` >>
  Cases_on `source_exc` >> gvs[exception_outcome_rel_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

(* The S3 memory facts of the raw unit from the entry's memory- and
   pointer-safe runs, through the loweringMemCorrect bridges. *)
Theorem selected_raw_memory[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
  initial_venom_state_rel tops am tx vs /\ code_layout_valid vs /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  (!n. mem_safe_blocks n unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) /\
  (!n. ptr_safe_blocks D 0 n unit.cu_context fn [] FEMPTY entry_taint
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) ==>
  raw_unit_memory_ok unit.cu_context vs /\
  ptr_discipline 0 unit.cu_context vs /\ taint_within D unit.cu_context vs /\
  mem_inv dload_offset_ok unit.cu_context vs /\
  mem_inv dload_headroom_ok unit.cu_context vs /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    unit.cu_context vs
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`tops`, `rp`, `unit`, `am`, `tx`, `vs`, `fn`, `"__entry"`, `D`]
            lower_vyper_runtime_unit_memory_ok) >>
  impl_tac >- fs[] >> strip_tac >> simp[] >>
  conj_tac
  >- metis_tac[lower_vyper_runtime_unit_dload_offset_ok] >>
  conj_tac
  >- metis_tac[lower_vyper_runtime_unit_dload_headroom_ok] >>
  metis_tac[lower_vyper_runtime_unit_dload_in_section]
QED

Theorem selected_run:
  o1_source_unit_ok unit /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  MEM fn unit.cu_context.ctx_functions /\
  gas_origin_path T explicit unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) marks rv /\
  exit_result rv ==>
  (?fuel. run_context fuel unit.cu_context vs = rv) /\
  (!fuel. mem_safe_blocks fuel unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>))
Proof
  strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >>
  disch_then (strip_assume_tac o MATCH_MP gas_path_mem_exec) >>
  fs[]
  >- (gvs[exit_result_def]) >>
  `!e. rv <> Error e` by (Cases_on `rv` >> gvs[exit_result_def]) >>
  `!m. mem_safe_run m unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)` by
    (irule mem_safe_run_all_fuel >> metis_tac[]) >>
  `?bb. lookup_block "__entry" fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` by
    (qpat_x_assum `fn_entry_label fn = _` mp_tac >>
     Cases_on `fn.fn_blocks` >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >> strip_tac >>
     qexists_tac `h` >> simp[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
     irule no_phis_phi_prefix_length_zero >>
     fs[o1_source_unit_ok_def, listTheory.EVERY_MEM] >>
     rpt strip_tac >>
     `MEM inst (fn_insts fn)` by
       (irule lookup_block_fn_insts >> qexists_tac `h` >>
        qexists_tac `"__entry"` >> simp[venomInstTheory.lookup_block_def, listTheory.FIND_thm]) >>
     metis_tac[raw_opcode_ok_def, listTheory.MEM]) >>
  conj_tac
  >- (qexists_tac `SUC fuel` >>
      simp[run_context_def, run_function_def] >>
      simp[fragExecTheory.run_blocks_run_from_no_phi]) >>
  gen_tac >> Cases_on `fuel'` >- simp[Once mem_safe_blocks_def] >>
  `eval_phis
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
    bb.bb_instructions = OK
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)` by
    simp[eval_phis_no_phi] >>
  `lookup_block
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>).vs_current_bb
    fn.fn_blocks = SOME bb` by simp[] >>
  drule_all mem_safe_blocks_run >> simp[]
QED

(* The call theorem at one fixed gas marking (argon, 2026-11-12): the raw-unit
   entry state vs is a gas variant of the compiled run's entry state, carries
   the S4 simulation facts at every trace horizon, and S1's selected-run
   certificate at marks; the result relation holds at every filling past the
   marked readings where the storage guards hold. *)
Theorem opt_entry_data_section_bound[local]:
  !tops prog prog' am tx es cplan policy unit.
    call_state_rel tops (assemble prog') am tx es /\
    codegen_assembly policy unit = SOME prog /\ unit_shape_ok unit /\
    assemble prog <> [] ==>
    LENGTH (opt_entry_state prog prog' cplan es).vs_data_section <
      dimword (:256) DIV 2
Proof
  rpt strip_tac >>
  drule_all opt_entry_code_layout_valid >>
  disch_then (qspec_then `cplan` assume_tac) >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan es` >>
  `vs.vs_code = assemble prog ++ vs.vs_data_section` by
    simp[Abbr `vs`, opt_entry_state_def, entry_venom_state_frame_fields] >>
  `0 < LENGTH (assemble prog)` by
    (Cases_on `assemble prog` >> fs[]) >>
  fs[code_layout_valid_def] >> decide_tac
QED

Theorem abort_context_obligations_raw[local]:
  !Inv ctx cp vs.
  codegen_context_obligations_abort Inv ctx cp /\
  codegen_reachability_package Inv ctx vs ==>
  codegen_context_obligations_abort (raw_reachable vs) ctx cp /\
  codegen_reachability_package (raw_reachable vs) ctx vs
Proof
  rpt gen_tac >> strip_tac >>
  `!fn inst s. raw_reachable vs ctx fn inst s ==> Inv ctx fn inst s` by
    metis_tac[raw_reachable_least] >>
  conj_tac
  >- (fs[codegen_context_obligations_abort_def,
         codegen_memory_obligations_abort_def] >> metis_tac[]) >>
  fs[raw_reachable_package_iff, codegen_reachability_package_def] >> metis_tac[]
QED

Theorem vyper_call_correct_at_marks:
  !fin policy tops deploy_bc runtime_bc rpolicy unit out prog prog' cp
   am tx txp ret es vs0 fmp vs marks.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am txp /\
    call_state_rel tops (assemble prog') am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    fin rpolicy prog = SOME prog' /\
    vs0 = opt_entry_state prog prog' cp es /\
    txp = tx with code := vs0.vs_code /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    external_return_type tops tx.function_name = ret /\
    raw_variant fmp vs vs0 /\
    (!H:(bool # bytes32 # type_value) list # num list.
       (?fr. terminates (run_context fr unit.cu_context vs)) /\
       raw_unit_memory_ok unit.cu_context vs /\
       ptr_discipline 0 unit.cu_context vs /\
       taint_within
         (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
         unit.cu_context vs /\
       mem_inv dload_offset_ok unit.cu_context vs /\
       mem_inv dload_headroom_ok unit.cu_context vs /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
         s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
         unit.cu_context vs ==>
       ctx_sim
         (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
         unit.cu_context out.po_unit.cu_context vs
         vs0 /\
       (fin = asm_opt_finalizer ==>
          code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
                              ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
       ((o1_lowered_inv out.po_unit.cu_context vs0 /\
         (fin = asm_opt_finalizer ==>
            code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
        ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
           mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                     lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
             out.po_unit.cu_context vs0) /\
         !fuel. terminates (run_context fuel unit.cu_context vs) ==>
                ?u. run_context fuel unit.cu_context vs = Abort ExHalt_abort u))) /\
    source_unit_execution_correct_at marks tops ret am txp unit vs
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       !tail.
         call_storage_ok am txp (MAP SND (call_trace es))
           (gas_explicit marks vs.vs_gas_readings ++ tail) ==>
         call_result_rel_at (gas_explicit marks vs.vs_gas_readings ++ tail)
           tops am txp es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts txp.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec unit = SOME out`
    by fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  `code_layout_valid vs0` by metis_tac[opt_entry_code_layout_valid] >>
  `vs.vs_outcomes = MAP SND (call_trace es) /\
   code_layout_valid vs /\ vs.vs_initial_fmp = fmp /\ vs.vs_fmp = fmp` by
    (`code_layout_valid vs` by
       (MATCH_MP_TAC (Q.INST
          [`si` |-> `vs`, `so` |-> `vs0 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>`]
          gas_variant_code_layout_valid) >>
        conj_tac >- metis_tac[raw_variant_def] >>
        qpat_x_assum `code_layout_valid vs0` mp_tac >>
        simp[code_layout_valid_def]) >>
     qpat_x_assum `raw_variant _ _ _` mp_tac >>
     simp[raw_variant_def, gas_variant_def] >>
     disch_then (mp_tac o Q.AP_TERM
       `\s:venom_state. (s.vs_outcomes, s.vs_initial_fmp, s.vs_fmp)`) >>
     simp[opt_entry_state_def, entry_venom_state_def] >> metis_tac[]) >>
  `initial_venom_state_rel tops am txp vs` by
    (irule raw_variant_initial_venom_state_rel >>
     qexistsl_tac [`fmp`, `vs0`] >> simp[] >>
     metis_tac[opt_entry_initial_venom_state_rel]) >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _` mp_tac >>
  simp[source_unit_execution_correct_at_def] >> strip_tac
  >- metis_tac[]
  >- (gen_tac >> strip_tac >>
      qpat_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `tail` assume_tac) >>
      drule call_external_trace_result >> strip_tac >>
      irule source_exempt_call_result_rel >> gvs[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `tail` assume_tac) >>
  drule call_external_trace_result >> strip_tac >>
  Cases_on `source_exempt tops (res,am',rqs)`
  >- (irule source_exempt_call_result_rel >> simp[]) >>
  fs[] >>
  drule_all selected_run >> strip_tac >>
  `terminates (run_context fuel unit.cu_context vs)` by
    (qpat_assum `run_context fuel unit.cu_context vs = r'` (fn th => REWRITE_TAC [th]) >>
     Cases_on `r'` >> fs[exit_result_def, terminates_def]) >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts txp NONE)
     (initial_state am []) (storage_trace_horizon obs) obs` by
    metis_tac[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon obs` mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_safe_blocks D` >>
  `w2n vs.vs_initial_fmp <= w2n vs.vs_fmp` by simp[] >>
  `raw_unit_memory_ok unit.cu_context vs /\
   ptr_discipline 0 unit.cu_context vs /\ taint_within D unit.cu_context vs /\
   mem_inv dload_offset_ok unit.cu_context vs /\
   mem_inv dload_headroom_ok unit.cu_context vs /\
   mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
     s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
     unit.cu_context vs` by
    (irule selected_raw_memory >> metis_tac[]) >>
  Q.SUBGOAL_THEN
  `ctx_sim D unit.cu_context out.po_unit.cu_context vs vs0 /\
   (fin = asm_opt_finalizer ==>
      code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
                          ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
   ((o1_lowered_inv out.po_unit.cu_context vs0 /\
     (fin = asm_opt_finalizer ==>
        code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
    ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
       mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                 lowered_mem_fact eom ctx fn inst s)
         out.po_unit.cu_context vs0) /\
     !n. terminates (run_context n unit.cu_context vs) ==>
       ?u. run_context n unit.cu_context vs = Abort ExHalt_abort u))`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))
  >-
    (fs[Abbr `D`] >>
     qpat_x_assum `!H. _ ==> _` (qspec_then `storage_trace_horizon obs` mp_tac) >>
     impl_tac >- (gvs[] >> metis_tac[]) >>
     simp[lowered_mem_fact_def]) >>
  `vs0.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs0.vs_code = assemble prog ++ vs0.vs_data_section` by
    fs[opt_entry_state_def, entry_venom_state_def] >>
  qspec_then `tops` mp_tac
    (Q.INST [`mem_ok` |-> `K T`, `calling_ok` |-> `K T`, `post_ok` |-> `K T`]
      runtime_codegen_compute_labels_bound) >>
  impl_tac >- gvs[] >> disch_tac >>
  Cases_on `fin = K SOME`
  >- (`prog' = prog` by fs[] >>
      `vs0 = entry_venom_state prog cplan es /\ txp = tx` by
        metis_tac[opt_entry_state_identity, opt_entry_txp_identity] >>
      qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
      `tx with code := (opt_entry_state prog prog cplan es).vs_code = tx` by
        metis_tac[opt_entry_txp_identity] >>
      qpat_x_assum `tx with code := _ = tx` SUBST_ALL_TAC >>
      qpat_x_assum `txp = tx` SUBST_ALL_TAC >>
      `initial_ctx_rel cplan prog out.po_unit.cu_context vs0 es` by
        metis_tac[entry_venom_state_initial_ctx_rel] >>
      qpat_x_assum `(o1_lowered_inv _ _ /\ _) \/ _`
        (DISJ_CASES_THEN STRIP_ASSUME_TAC)
      >- (qspecl_then [`out`, `cplan`, `vs0`]
            mp_tac o1_pipeline_memory_obligations_raw >>
          impl_tac >- gvs[] >> strip_tac >>
          drule_all o1_pipeline_codegen_obligations >> strip_tac >>
          `!n. ?r' es''. run_call es = SOME (r',es'') /\
             (frame_resource_starved es r' es'' \/
              venom_frame_rel es r' es'' (run_context n out.po_unit.cu_context vs0))` by
            (qx_gen_tac `n` >>
             qspecl_then [`n`, `rpolicy`, `out.po_unit`, `cplan`, `prog`,
                          `raw_reachable vs0`, `vs0`, `es`] mp_tac codegen_correct >>
             impl_tac >- gvs[] >> disch_then ACCEPT_TAC) >>
          mp_tac (Q.INST
            [`ctx` |-> `unit.cu_context`, `ctx'` |-> `out.po_unit.cu_context`,
             `vs'` |-> `vs0`,
             `gs` |-> `gas_explicit marks vs.vs_gas_readings ++ tail`]
            call_at_horizon_composition) >>
          impl_tac
          >- (gvs[Abbr `D`, cx_dead_def, external_call_dead_def,
                  initial_evaluation_context_def] >> metis_tac[]) >> gvs[]) >>
      fs[] >>
      qspecl_then [`rpolicy`, `unit`, `out`, `cplan`, `vs0`]
        mp_tac o1_pipeline_context_obligations_lowered_abort >>
      impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
      drule_all abort_context_obligations_raw >> strip_tac >>
      `!n a u. run_context n out.po_unit.cu_context vs0 = Abort a u ==>
         ?r' es''. run_call es = SOME (r',es'') /\
           (frame_resource_starved es r' es'' \/
            ?exc out lgs. frame_outcome es r' es'' (SOME exc) out lgs)` by
        (rpt gen_tac >> strip_tac >>
         qspecl_then [`n`, `rpolicy`, `out.po_unit`, `cplan`, `prog`,
                      `raw_reachable vs0`, `vs0`, `es`, `a`, `u`]
           mp_tac codegen_correct_static_abort >>
         impl_tac >- (gvs[] >> metis_tac[]) >> metis_tac[]) >>
      mp_tac (Q.INST
        [`ctx` |-> `unit.cu_context`, `ctx'` |-> `out.po_unit.cu_context`,
         `vs'` |-> `vs0`,
         `gs` |-> `gas_explicit marks vs.vs_gas_readings ++ tail`]
        call_at_horizon_static_abort_composition) >>
      impl_tac
      >- (gvs[Abbr `D`, cx_dead_def, external_call_dead_def,
              initial_evaluation_context_def] >> metis_tac[]) >> gvs[]) >>
  `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  `~program_reads_self_code tops` by fs[] >>
  drule_all lower_vyper_runtime_unit_sym_src_ok >> strip_tac >>
  drule_all o1_pipeline_label_flow_preserved >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  drule_all opt_entry_codegen_asm_entry_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  `assemble prog' <> []` by
    (irule codegen_assembly_finalizer_nonempty >> metis_tac[]) >>
  drule_all opt_entry_asm_frame_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  qpat_x_assum `(o1_lowered_inv _ _ /\ _) \/ _`
    (DISJ_CASES_THEN STRIP_ASSUME_TAC)
  >- (qspecl_then [`out`, `cplan`, `vs0`]
        mp_tac o1_pipeline_memory_obligations_raw >>
      impl_tac >- gvs[] >> strip_tac >>
      drule_all o1_pipeline_codegen_obligations >> strip_tac >>
      `!n. ?r' es''. run_call es = SOME (r',es'') /\
         (frame_resource_starved es r' es'' \/
          venom_frame_rel es r' es'' (run_context n out.po_unit.cu_context vs0))` by
        (qx_gen_tac `n` >>
         qspecl_then [`n`, `rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`,
                      `raw_reachable vs0`, `vs0`, `es`] mp_tac codegen_correct_asm_opt >>
         impl_tac >- gvs[] >> disch_then ACCEPT_TAC) >>
      mp_tac (Q.INST
        [`ctx` |-> `unit.cu_context`, `ctx'` |-> `out.po_unit.cu_context`,
         `vs'` |-> `vs0`, `tx` |-> `txp`,
         `gs` |-> `gas_explicit marks vs.vs_gas_readings ++ tail`]
        call_at_horizon_composition) >>
      impl_tac
      >- (gvs[Abbr `D`, cx_dead_def, external_call_dead_def,
              initial_evaluation_context_def] >> metis_tac[]) >> gvs[]) >>
  fs[] >>
  qspecl_then [`rpolicy`, `unit`, `out`, `cplan`, `vs0`]
    mp_tac o1_pipeline_context_obligations_lowered_abort >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  drule_all abort_context_obligations_raw >> strip_tac >>
  `!n a u. run_context n out.po_unit.cu_context vs0 = Abort a u ==>
     ?r' es''. run_call es = SOME (r',es'') /\
       (frame_resource_starved es r' es'' \/
        ?exc out lgs. frame_outcome es r' es'' (SOME exc) out lgs)` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`n`, `rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`,
                  `raw_reachable vs0`, `vs0`, `es`, `a`, `u`]
       mp_tac codegen_correct_static_abort_asm_opt >>
     impl_tac >- (gvs[] >> metis_tac[]) >> metis_tac[]) >>
  mp_tac (Q.INST
    [`ctx` |-> `unit.cu_context`, `ctx'` |-> `out.po_unit.cu_context`,
     `vs'` |-> `vs0`, `tx` |-> `txp`,
     `gs` |-> `gas_explicit marks vs.vs_gas_readings ++ tail`]
    call_at_horizon_static_abort_composition) >>
  impl_tac
  >- (gvs[Abbr `D`, cx_dead_def, external_call_dead_def,
          initial_evaluation_context_def] >> metis_tac[]) >> gvs[]
QED

(* ADMISSION (argon, 2026-11-13; the call twin of deploy_pipeline_gas_link).
   Where the frame is not starved, every filling of its gas readings that
   meets the source run's storage guards extends the marked readings of a raw
   entry state carrying the S4 facts and the selected-run certificate.  The
   raw state, marks and tail are chosen inside each filling.  The only
   admission on vyper_call_correct_identity's path. *)
(* HELD ADMISSION: call-side gas synchronization; gas-link track owns removal. *)
Theorem call_pipeline_gas_link:
  !fin policy tops deploy_bc runtime_bc rpolicy unit out prog prog' cp
   am tx txp ret es vs0 fmp r es'.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am txp /\
    call_state_rel tops (assemble prog') am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    fin rpolicy prog = SOME prog' /\
    vs0 = opt_entry_state prog prog' cp es /\
    txp = tx with code := vs0.vs_code /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (?shadow_ctx. !vs.
       raw_variant fmp vs vs0 ==>
       ?marks.
         source_unit_execution_correct_with shadow_ctx marks
           tops ret am txp unit vs) /\
    run_call es = SOME (r, es') /\
    ~frame_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. call_storage_ok am txp (MAP SND (call_trace es)) gs ==>
         ?vs marks tail.
           gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
           raw_variant fmp vs vs0 /\
           (!H:(bool # bytes32 # type_value) list # num list.
              (?fr. terminates (run_context fr unit.cu_context vs)) /\
              raw_unit_memory_ok unit.cu_context vs /\
              ptr_discipline 0 unit.cu_context vs /\
              taint_within
                (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
                unit.cu_context vs /\
              mem_inv dload_offset_ok unit.cu_context vs /\
              mem_inv dload_headroom_ok unit.cu_context vs /\
              mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
                unit.cu_context vs ==>
              ctx_sim
                (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
                unit.cu_context out.po_unit.cu_context vs
                vs0 /\
              (fin = asm_opt_finalizer ==>
                 code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
                                     ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
              ((o1_lowered_inv out.po_unit.cu_context vs0 /\
                (fin = asm_opt_finalizer ==>
                   code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
               ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
                  mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                            lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
                    out.po_unit.cu_context vs0) /\
                !fuel. terminates (run_context fuel unit.cu_context vs) ==>
                       ?u. run_context fuel unit.cu_context vs = Abort ExHalt_abort u))) /\
           source_unit_execution_correct_at marks tops ret am txp unit vs)
Proof
  cheat
QED

(* Where the frame is not starved and the gas link holds, the call result
   relation holds at every guarded filling. *)
Theorem vyper_call_correct_from_gas_link:
  !fin policy tops deploy_bc runtime_bc rpolicy unit out prog prog' cp
   am tx txp ret es vs0 fmp r es'.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am txp /\
    call_state_rel tops (assemble prog') am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    fin rpolicy prog = SOME prog' /\
    vs0 = opt_entry_state prog prog' cp es /\
    txp = tx with code := vs0.vs_code /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    external_return_type tops tx.function_name = ret /\
    run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/
     gas_readings_rel (gas_readings es)
       (\gs. call_storage_ok am txp (MAP SND (call_trace es)) gs ==>
          ?vs marks tail.
            gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
            raw_variant fmp vs vs0 /\
            (!H:(bool # bytes32 # type_value) list # num list.
               (?fr. terminates (run_context fr unit.cu_context vs)) /\
               raw_unit_memory_ok unit.cu_context vs /\
               ptr_discipline 0 unit.cu_context vs /\
               taint_within
                 (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
                 unit.cu_context vs /\
               mem_inv dload_offset_ok unit.cu_context vs /\
               mem_inv dload_headroom_ok unit.cu_context vs /\
               mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                 s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
                 unit.cu_context vs ==>
               ctx_sim
                 (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
                 unit.cu_context out.po_unit.cu_context vs
                 vs0 /\
               (fin = asm_opt_finalizer ==>
                  code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
                                      ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
               ((o1_lowered_inv out.po_unit.cu_context vs0 /\
                 (fin = asm_opt_finalizer ==>
                    code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
                ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
                   mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                             lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
                     out.po_unit.cu_context vs0) /\
                 !fuel. terminates (run_context fuel unit.cu_context vs) ==>
                        ?u. run_context fuel unit.cu_context vs = Abort ExHalt_abort u))) /\
            source_unit_execution_correct_at marks tops ret am txp unit vs))
    ==>
    frame_resource_starved es r es' \/
    call_result_rel_guarded tops am txp es r es'
Proof
  rpt strip_tac >>
  Cases_on `frame_resource_starved es r es'` >> fs[] >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  simp[call_result_rel_guarded_def] >>
  drule gas_readings_rel_mono >> disch_then irule >>
  rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `call_storage_ok _ _ _ gs ==> _` mp_tac >>
  impl_tac >- gvs[] >> strip_tac >>
  qpat_x_assum `gs = gas_explicit _ _ ++ _` SUBST_ALL_TAC >>
  qspecl_then [`fin`, `policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`,
               `unit`, `out`, `prog`, `prog'`, `cplan`, `am`, `tx`, `txp`, `ret`,
               `es`, `vs0`, `fmp`, `vs`, `marks`] mp_tac vyper_call_correct_at_marks >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >> gvs[]
QED

Theorem vyper_call_correct_identity:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    dispatched_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel_guarded tops am tx es r es')
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def, frame_fresh_def,
                                           frame_tx_rel_def, world_rel_def] >>
  `external_return_type tops tx.function_name = ret` by
    (fs[dispatched_vyper_call_def] >> simp[external_return_type_def]) >>
  `outcomes_accounts_typed (SOME (MAP SND (call_trace es)))` by
    (`wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
       fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
          evm_state_ok_def] >>
     drule_all call_trace_outcomes_bounded >>
     simp[exprSimHypsDefsTheory.outcomes_accounts_typed_def, listTheory.EVERY_MEM]) >>
  `initial_venom_state_rel tops am tx (entry_venom_state prog cplan es)` by
    (irule entry_venom_state_initial_venom_state_rel >> gvs[]) >>
  `K SOME IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  `K SOME <> asm_opt_finalizer` by
    (strip_tac >>
     qpat_x_assum `K SOME = asm_opt_finalizer`
       (fn th => mp_tac (Q.AP_THM
         (Q.AP_THM th `rpolicy with rpol_final_assembly := FAP_Optimize`)
         `[AsmOp "STOP"; AsmOp "STOP"]`)) >>
     EVAL_TAC) >>
  `K SOME rpolicy prog = SOME prog` by simp[] >>
  `runtime_bc = assemble prog` by fs[] >>
  `opt_entry_state prog prog cplan es = entry_venom_state prog cplan es /\
   tx with code := (opt_entry_state prog prog cplan es).vs_code = tx` by
    metis_tac[opt_entry_state_identity, opt_entry_txp_identity] >>
  qabbrev_tac `fmp = (n2w (MAX cplan.cp_initial_fmp
    (unit_alloca_budget unit.cu_context +
     32 * ctx_dload_count unit.cu_context)) : bytes32)` >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `cplan`, `prog`, `prog`, `es`,
               `fmp`] mp_tac raw_fmp_choice >>
  impl_tac >- simp[Abbr `fmp`] >> strip_tac >>
  drule_all lower_vyper_runtime_unit_correct_dispatched_with >> strip_tac >>
  `?shadow_ctx. !vs. raw_variant fmp vs (opt_entry_state prog prog cplan es) ==>
     ?marks. source_unit_execution_correct_with shadow_ctx marks
       tops ret am tx unit vs` by
    (qexists_tac `shadow_ctx` >>
    (rpt strip_tac >>
     `vs.vs_outcomes = MAP SND (call_trace es) /\
      vs.vs_call_ctx.cc_calldata =
        buffer_to_list (FST (HD es.contexts)).msgParams.data /\
      vs.vs_fmp = fmp /\ vs.vs_initial_fmp = fmp` by
       (qpat_x_assum `raw_variant _ _ _` mp_tac >>
        simp[raw_variant_def, gas_variant_def] >>
        disch_then (mp_tac o Q.AP_TERM
          `\s:venom_state. (s.vs_outcomes, s.vs_call_ctx.cc_calldata,
             s.vs_fmp, s.vs_initial_fmp)`) >>
        simp[opt_entry_state_def, entry_venom_state_def] >> metis_tac[]) >>
     `LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64` by
       metis_tac[raw_variant_opt_entry_calldata_bound] >>
     `initial_venom_state_rel tops am tx vs` by
       metis_tac[raw_variant_initial_venom_state_rel] >>
     qpat_x_assum `!am tx ret vs. _` (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
     gvs[])) >>
  qspecl_then [`K SOME`, `policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`,
               `unit`, `out`, `prog`, `prog`, `cplan`, `am`, `tx`, `tx`, `ret`,
               `es`, `opt_entry_state prog prog cplan es`, `fmp`, `r`, `es'`]
    mp_tac call_pipeline_gas_link >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  qspecl_then [`K SOME`, `policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`,
               `unit`, `out`, `prog`, `prog`, `cplan`, `am`, `tx`, `tx`, `ret`,
               `es`, `opt_entry_state prog prog cplan es`, `fmp`, `r`, `es'`]
    mp_tac vyper_call_correct_from_gas_link >>
  impl_tac >- (gvs[] >> metis_tac[]) >> simp[]
QED

(* The final assembly optimizer's case: the program, compiled with Python's
   O1 final assembly optimizer, under the same hypotheses plus the temporary
   exclusion of programs that read their own code. *)
Theorem vyper_call_correct_asm_opt:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    dispatched_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel_guarded tops am tx es r es')
Proof
  cheat
QED

(* TOP-LEVEL: one theorem over the accepted finalizers (Python's -O none and
   O1 final assembly).  The optimizer's case excludes, for now, programs that
   read their own code. *)
Theorem vyper_call_correct_dispatched:
  !fin policy tops deploy_bc runtime_bc am tx ret es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    dispatched_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel_guarded tops am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
  >- (drule_all vyper_call_correct_identity >> simp[])
  >> `~program_reads_self_code tops` by fs[] >>
  drule_all vyper_call_correct_asm_opt >> simp[]
QED

(* ===== Component Theorems ===== *)

(* Pipeline preserves observable semantics.
   Given ctx_pass_correct with R_ok/R_term that each imply
   observable_equiv, every terminating execution of the original
   context has a fuel for the transformed context with
   observably equivalent results. *)
Theorem e2e_venom_pipeline:
  !(R_ok : venom_state -> venom_state -> bool) R_term ctx pipeline vs fuel.
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    ctx_pass_correct pipeline R_ok R_term ctx vs /\
    terminates (run_context fuel ctx vs)
    ==>
    ?fuel'. observable_result_equiv
              (run_context fuel ctx vs)
              (run_context fuel' (pipeline ctx) vs)
Proof
  simp[ctx_pass_correct_def, pass_correct_def] >>
  rpt strip_tac >>
  `?fuel'. terminates (run_context fuel' (pipeline ctx) vs)` by
    (gvs[] >> metis_tac[]) >>
  qexists_tac `fuel'` >>
  first_x_assum drule_all >> strip_tac >>
  `!r1 r2. lift_result R_ok R_term R_term r1 r2 ==>
           observable_result_equiv r1 r2` by
    (rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
     fs[lift_result_def, observable_result_equiv_def,
        observable_equiv_def, revert_equiv_def] >>
     metis_tac[]) >>
  metis_tac[]
QED

(* ===== Two-Phase compile_vyper ===== *)

(* Successful generic compilation exposes the concrete runtime lowering,
   pipeline output, matching final-assembly policy, and finalization result. *)
Theorem compile_vyper_runtime_bytecode:
  !tops pipeline finalizer policy deploy_bc runtime_bc.
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc)
    ==>
    ?rpolicy runtime_unit out.
      resolve_o1_policy policy = SOME rpolicy /\
      lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
      pipeline rpolicy runtime_unit = SOME out /\
      out.po_final_assembly = rpolicy.rpol_final_assembly /\
      finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc
Proof
  simp[compile_vyper_with_def, checked_unit_pipeline_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  goal_assum $ drule_at Any
QED

(* ===== Every calldata ===== *)

Theorem raw_variant_revert_facts:
  !tops rpolicy unit am tx vs vi.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\ code_layout_valid vs /\
    vs.vs_fmp = vs.vs_initial_fmp /\ raw_variant vs.vs_initial_fmp vi vs ==>
    raw_unit_memory_ok unit.cu_context vi /\
    ptr_discipline 0 unit.cu_context vi /\
    mem_inv dload_offset_ok unit.cu_context vi /\
    mem_inv dload_headroom_ok unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                              s.vs_code = vi.vs_code /\
                              s.vs_data_section = vi.vs_data_section)
      unit.cu_context vi /\
    ?fuel s. run_context fuel unit.cu_context vi = Abort Revert_abort s /\
             s.vs_returndata = []
Proof
  rpt gen_tac >> strip_tac >>
  `initial_venom_state_rel tops am tx vi` by
    metis_tac[raw_variant_initial_venom_state_rel] >>
  `vi.vs_call_ctx = vs.vs_call_ctx` by metis_tac[raw_variant_call_ctx] >>
  `gas_variant vi vs` by metis_tac[raw_variant_gas_variant] >>
  `code_layout_valid vi` by metis_tac[gas_variant_code_layout_valid] >>
  `vi.vs_fmp = vi.vs_initial_fmp` by
    fs[gas_variant_def, venomStateTheory.venom_state_component_equality] >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vi`]
    mp_tac lower_vyper_runtime_unit_reverts >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`func`, `s`, `G'`, `tn'`] strip_assume_tac) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vi`, `func`, `s`]
    mp_tac lower_vyper_runtime_unit_reverts_memory_ok >>
  impl_tac >- simp[] >> strip_tac >>
  `mem_inv dload_headroom_ok unit.cu_context vi` by
    (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
  metis_tac[]
QED

(* Keep the source unit's empty revert through the pipeline, with enough
   room for the generated frame's static layout. *)
Theorem o1_pipeline_reverts_empty:
  !tops rpolicy unit out am tx vs fuel s.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_run_state_ok vs /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs.vs_initial_fmp) /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    run_context fuel out.po_unit.cu_context vs = Abort Revert_abort s
    ==>
    s.vs_returndata = []
Proof
  rpt strip_tac >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
  qabbrev_tac `D0 = <|d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV|>` >>
  `dead_wf D0` by simp[Abbr `D0`, dead_wf_def] >>
  `run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec unit = SOME out` by
    fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all o1_pipeline_sim_revert_empty >> strip_tac >>
  qpat_x_assum `!D fmp vs_out. _`
    (qspecl_then [`D0`, `vs.vs_initial_fmp`, `vs`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `vi` strip_assume_tac) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `vi`]
    mp_tac raw_variant_revert_facts >>
  impl_tac >- fs[o1_run_state_ok_def] >> strip_tac >>
  rename1 `run_context sf unit.cu_context vi = Abort Revert_abort ss` >>
  `taint_within D0 unit.cu_context vi` by
    simp[Abbr `D0`, taint_within_def] >>
  `fmp_free_ctx unit.cu_context` by metis_tac[source_fmp_free] >>
  `EVERY pre_fmp_ops unit.cu_context.ctx_functions` by
    (simp[EVERY_MEM] >> metis_tac[source_pre_fmp_ops]) >>
  `gas_variant vi vs` by
    metis_tac[raw_variant_gas_variant, o1_run_state_ok_def] >>
  `vi.vs_fmp = vi.vs_initial_fmp` by
    fs[o1_run_state_ok_def, gas_variant_def,
       venomStateTheory.venom_state_component_equality] >>
  `mem_inv raw_mem_ok unit.cu_context vi` by
    (simp[raw_unit_memory_ok_mem_inv] >> rpt gen_tac >> strip_tac >>
     drule raw_reachable_fmp_fixed >> simp[] >> strip_tac >>
     drule ctxLookupAgreeTheory.raw_reachable_initial_fmp >> strip_tac >>
     `inst.inst_opcode <> DALLOCA` by
       (`EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)` by
          (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
        imp_res_tac EVERY_active_inst >> gvs[]) >>
     simp[dalloca_no_wrap_def]) >>
  `o1_src_inv D0 unit.cu_context vi` by
    (fs[o1_src_inv_def] >> metis_tac[]) >>
  `o1_pre_walk_inv D0 unit.cu_context vi` by
    (irule o1_source_pre_walk_inv >> simp[]) >>
  `fmp_variant_room (SOME vs.vs_initial_fmp) out.po_unit.cu_context vs` by
    (simp[fmp_variant_room_def] >> first_assum ACCEPT_TAC) >>
  `?t. run_context (cfg_norm_fuel out.po_unit.cu_context sf)
         out.po_unit.cu_context vs = Abort Revert_abort t /\ t.vs_returndata = []` by
    metis_tac[] >>
  `run_context (MAX fuel (cfg_norm_fuel out.po_unit.cu_context sf))
     out.po_unit.cu_context vs = run_context fuel out.po_unit.cu_context vs` by
    (irule run_context_terminates_mono >> simp[terminates_def]) >>
  `run_context (MAX fuel (cfg_norm_fuel out.po_unit.cu_context sf))
     out.po_unit.cu_context vs =
   run_context (cfg_norm_fuel out.po_unit.cu_context sf) out.po_unit.cu_context vs` by
    (irule run_context_terminates_mono >> simp[terminates_def]) >>
  gvs[]
QED

Theorem static_shadow_initial_venom_state_rel[local]:
  initial_venom_state_rel tops am tx vs ==>
  initial_venom_state_rel tops am (tx with is_static := F) (static_shadow vs)
Proof
  simp[initial_venom_state_rel_def, venom_env_rel_def, static_shadow_def,
       loweringStateRelDefsTheory.call_ctx_rel_def,
       loweringStateRelDefsTheory.tx_env_ok_def,
       value_transfer_ok_def, accounts_after_transfer_def] >>
  strip_tac >> fs[]
QED

Theorem o1_pipeline_reverts_empty_any_static:
  !tops rpolicy unit out am tx vs fuel s.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
    code_layout_valid vs /\
    (!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
           eom <= w2n vs.vs_initial_fmp) /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    run_context fuel out.po_unit.cu_context vs = Abort Revert_abort s
    ==>
    s.vs_returndata = []
Proof
  rpt strip_tac >> Cases_on `vs.vs_call_ctx.cc_static`
  >- (mp_tac (Q.INST [`s` |-> `vs`, `sh` |-> `static_shadow vs`,
                     `C` |-> `out.po_unit.cu_context`, `v` |-> `s`]
                    static_shadow_run_context_revert) >>
      impl_tac >- simp[static_shadow_rel_initial] >>
      disch_then (qx_choose_then `sh` strip_assume_tac) >>
      `source_typing_ok tops am (tx with is_static := F)` by
        (qpat_assum `source_typing_ok tops am tx`
           (strip_assume_tac o REWRITE_RULE [source_typing_ok_def]) >>
         simp[source_typing_ok_def] >>
         fs[vyperTypeContractSoundnessTheory.call_tx_well_typed_def]) >>
      `source_deployment_rel tops am (tx with is_static := F)` by
        fs[source_deployment_rel_def, layouts_agree_def] >>
      `initial_venom_state_rel tops am (tx with is_static := F) (static_shadow vs)` by
        metis_tac[static_shadow_initial_venom_state_rel] >>
      `o1_run_state_ok (static_shadow vs)` by
        metis_tac[static_shadow_o1_run_state_ok] >>
      qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `am`, `tx with is_static := F`,
                   `static_shadow vs`, `fuel`, `sh`] mp_tac o1_pipeline_reverts_empty >>
      impl_tac >- (simp[static_shadow_def] >> first_assum ACCEPT_TAC) >>
      gvs[static_shadow_rel_def, static_shadow_def,
          venomStateTheory.venom_state_component_equality]) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `am`, `tx`, `vs`, `fuel`, `s`]
    mp_tac o1_pipeline_reverts_empty >>
  impl_tac >- (simp[o1_run_state_ok_def] >> first_assum ACCEPT_TAC) >> simp[]
QED

(* Calldata that dispatches to nothing (no fallback, a short head, or
   arguments the decoder rejects) makes the compiled contract revert with
   empty returndata, or run out of resources: the identity finalizer. *)
Theorem vyper_call_reverts_identity:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    calldata_dispatch tops
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) = NONE
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       frame_raises es Reverted /\ ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs)
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
  drule_all entry_venom_state_initial_venom_state_rel >>
  disch_then (qspec_then `cplan` assume_tac) >>
  drule_all entry_venom_state_initial_ctx_rel >>
  disch_then (qspec_then `cplan` assume_tac) >>
  drule_all generated_entry_code_layout_shape >>
  disch_then (qspec_then `cplan` assume_tac) >>
  qabbrev_tac `vs = entry_venom_state prog cplan es` >>
  `o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_call_ctx.cc_calldata =
     buffer_to_list (FST (HD es.contexts)).msgParams.data` by
    simp[Abbr `vs`, entry_venom_state_def, entry_venom_state_fresh] >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def, frame_fresh_def,
                                           frame_tx_rel_def, world_rel_def] >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  qabbrev_tac `D0 = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D0` by simp[Abbr `D0`, dead_wf_def] >>
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
          eom <= w2n vs.vs_initial_fmp` by
    (qspecl_then [`out.po_unit.cu_context`, `cplan`, `vs`]
       mp_tac generate_context_plan_eom_room >> simp[]) >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[lower_vyper_runtime_unit_no_runtime_begin] >>
  qspecl_then [`D0`, `0`, `rpolicy`, `unit`, `out`, `vs`, `vs.vs_initial_fmp`]
    mp_tac run_venom_pipeline_correct_static_abort >>
  impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `vs_in` strip_assume_tac) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `vs_in`]
    mp_tac raw_variant_revert_facts >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_context fuel unit.cu_context vs_in = Abort Revert_abort s` >>
  `taint_within D0 unit.cu_context vs_in` by
    simp[Abbr `D0`, taint_within_def] >>
  qpat_x_assum `raw_unit_memory_ok _ vs_in /\ _ ==> _` mp_tac >>
  impl_tac >- metis_tac[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `terminates (run_context fuel unit.cu_context vs_in)` by
    simp[terminates_def] >>
  `o1_lowered_inv out.po_unit.cu_context vs` by
    (qpat_x_assum `o1_lowered_inv _ _ \/ _` strip_assume_tac >> simp[] >>
     first_x_assum (qspec_then `fuel` mp_tac) >> simp[]) >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  rename1 `dead_result_rel D0 _ (run_context fuel' _ vs)` >>
  `?s'. run_context fuel' out.po_unit.cu_context vs = Abort Revert_abort s'` by
    (qpat_x_assum `dead_result_rel _ _ _` mp_tac >>
     Cases_on `run_context fuel' out.po_unit.cu_context vs` >>
     simp[dead_result_rel_def]) >>
  `s'.vs_returndata = []` by
    (qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `am`, `tx`, `vs`,
                  `fuel'`, `s'`] mp_tac o1_pipeline_reverts_empty_any_static >>
     impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> simp[]) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qspecl_then [`fuel'`, `rpolicy`, `out.po_unit`, `cplan`, `prog`,
               `raw_reachable vs`, `vs`, `es`] mp_tac codegen_correct >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl_tac [`r`, `es'`] >> gvs[venom_frame_rel_def] >>
  metis_tac[frameGasTheory.frame_raises_inst_raises]
QED

(* The same under the final assembly optimizer, which excludes, for now,
   programs that read their own code. *)
Theorem vyper_call_reverts_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    calldata_dispatch tops
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) = NONE
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       frame_raises es Reverted /\ ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs)
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
  `assemble prog <> []` by
    metis_tac[codegenAsmProgOkTheory.codegen_assembly_nonempty] >>
  `assemble prog' <> []` by
    (irule codegen_assembly_finalizer_nonempty >> metis_tac[]) >>
  drule_all opt_entry_codegen_asm_entry_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  drule_all opt_entry_asm_frame_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `rpolicy`, `out.po_unit`] mp_tac opt_entry_code_layout_valid >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan es` >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `vs`]
    mp_tac opt_entry_fields >>
  impl_tac >- simp[Abbr `vs`] >> strip_tac >>
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  `initial_venom_state_rel tops am txp vs` by
    metis_tac[opt_entry_initial_venom_state_rel] >>
  `source_typing_ok tops am txp` by
    (simp[Abbr `txp`] >> irule source_typing_ok_code_update >>
     qpat_x_assum `prog = _` SUBST_ALL_TAC >>
     fs[code_layout_valid_def, wordsTheory.dimword_def,
        fcpLib.INDEX_CONV ``dimindex(:256)``] >> decide_tac) >>
  `source_deployment_rel tops am txp` by
    (fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
        Abbr `txp`, source_deployment_rel_def,
        layouts_agree_def]) >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  qabbrev_tac `D0 = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D0` by simp[Abbr `D0`, dead_wf_def] >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
                  `rpolicy`, `out.po_unit`] mp_tac opt_entry_data_section_bound >>
     impl_tac >- simp[] >> simp[Abbr `vs`]) >>
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
          eom <= w2n vs.vs_initial_fmp` by
    (qspecl_then [`out.po_unit.cu_context`, `cplan`, `vs`]
       mp_tac generate_context_plan_eom_room >> simp[]) >>
  drule_all lower_vyper_runtime_unit_sym_src_ok >> strip_tac >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[lower_vyper_runtime_unit_no_runtime_begin] >>
  `!vi. raw_variant vs.vs_initial_fmp vi vs ==>
     raw_unit_memory_ok unit.cu_context vi /\
     ptr_discipline 0 unit.cu_context vi /\
     mem_inv dload_offset_ok unit.cu_context vi /\
     mem_inv dload_headroom_ok unit.cu_context vi /\
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vi.vs_code /\
                               s.vs_data_section = vi.vs_data_section)
       unit.cu_context vi /\
     ?fuel s. run_context fuel unit.cu_context vi = Abort Revert_abort s /\
              s.vs_returndata = []` by
    (gen_tac >> strip_tac >>
     qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `txp`, `vs`, `vi`]
       mp_tac raw_variant_revert_facts >> simp[]) >>
  `code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context` by
    (qspecl_then [`D0`, `0`, `rpolicy`, `unit`, `out`, `vs`, `vs.vs_initial_fmp`]
       mp_tac o1_pipeline_code_end_offset_ok_static_abort >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `vcode` strip_assume_tac) >>
     `taint_within D0 unit.cu_context vcode` by
       simp[Abbr `D0`, taint_within_def] >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _`
       (qspec_then `vcode` (drule_then strip_assume_tac)) >>
     qpat_x_assum `raw_unit_memory_ok _ vcode /\ _ ==> _` mp_tac >>
     (impl_tac >- metis_tac[]) >>
     disch_then (CONJUNCTS_THEN2 kall_tac strip_assume_tac) >> simp[] >>
     rename1 `run_context fuel unit.cu_context vcode = Abort Revert_abort s` >>
     qpat_x_assum `!fuel. terminates (run_context fuel unit.cu_context vcode) ==> _`
       (qspec_then `fuel` mp_tac) >> simp[terminates_def]) >>
  qspecl_then [`D0`, `0`, `rpolicy`, `unit`, `out`, `vs`, `vs.vs_initial_fmp`]
    mp_tac run_venom_pipeline_correct_static_abort >>
  impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `vs_in` strip_assume_tac) >>
  qpat_assum `!vi. raw_variant _ vi vs ==> _`
    (qspec_then `vs_in` (drule_then strip_assume_tac)) >>
  rename1 `run_context fuel unit.cu_context vs_in = Abort Revert_abort s` >>
  `taint_within D0 unit.cu_context vs_in` by
    simp[Abbr `D0`, taint_within_def] >>
  qpat_x_assum `raw_unit_memory_ok _ vs_in /\ _ ==> _` mp_tac >>
  impl_tac >- metis_tac[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `terminates (run_context fuel unit.cu_context vs_in)` by
    simp[terminates_def] >>
  `o1_lowered_inv out.po_unit.cu_context vs` by
    (qpat_x_assum `o1_lowered_inv _ _ \/ _` strip_assume_tac >> simp[] >>
     first_x_assum (qspec_then `fuel` mp_tac) >> simp[]) >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  rename1 `dead_result_rel D0 _ (run_context fuel' _ vs)` >>
  `?s'. run_context fuel' out.po_unit.cu_context vs = Abort Revert_abort s'` by
    (qpat_x_assum `dead_result_rel _ _ _` mp_tac >>
     Cases_on `run_context fuel' out.po_unit.cu_context vs` >>
     simp[dead_result_rel_def]) >>
  `s'.vs_returndata = []` by
    (qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `am`, `txp`, `vs`,
                  `fuel'`, `s'`] mp_tac o1_pipeline_reverts_empty_any_static >>
     impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> simp[]) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  drule_all o1_pipeline_label_flow_preserved >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  qspecl_then [`fuel'`, `rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`,
               `raw_reachable vs`, `vs`, `s'`, `es`]
    mp_tac codegen_reverts_asm_opt >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl_tac [`r`, `es'`] >> fs[] >>
  metis_tac[frameGasTheory.frame_raises_inst_raises]
QED

(* Both accepted finalizers. *)
Theorem vyper_call_reverts:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    calldata_dispatch tops
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) = NONE
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       frame_raises es Reverted /\ ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs)
Proof
  rpt gen_tac >> strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
  >- (drule_all vyper_call_reverts_identity >> simp[])
  >> `~program_reads_self_code tops` by fs[] >>
  drule_all vyper_call_reverts_asm_opt >> simp[]
QED

(* What the call does for the calldata tx carries: revert with empty
   returndata when it dispatches to nothing, else the source result of
   the external call it dispatches to. *)
Definition calldata_result_rel_guarded_def:
  calldata_result_rel_guarded tops am tx es r es' <=>
    case calldata_dispatch tops tx.calldata of
      NONE => frame_raises es Reverted /\
              ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs
    | SOME (f, vals) =>
        call_result_rel_guarded tops am
          (tx with <| function_name := f; args := vals |>) es r es'
End

(* Guarded compiler correctness for a single external call, for every
   calldata and both accepted finalizers (Python's -O none and O1 final
   assembly; the optimizer's case excludes, for now, programs that read
   their own code): the compiled contract does what the source does with
   the call the calldata dispatches to (tx supplies only the environment:
   sender, target, value, block), and reverts with empty returndata when it
   dispatches to nothing. *)
Theorem vyper_call_correct_guarded:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       calldata_result_rel_guarded tops am tx es r es')
Proof
  rpt strip_tac >> simp[calldata_result_rel_guarded_def] >>
  `tx.calldata = buffer_to_list (FST (HD es.contexts)).msgParams.data` by
    gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def,
        world_rel_def] >>
  asm_rewrite_tac[] >>
  Cases_on `calldata_dispatch tops
              (buffer_to_list (FST (HD es.contexts)).msgParams.data)` >>
  gvs[]
  >- (drule_all vyper_call_reverts >> simp[]) >>
  rename1 `_ = SOME fv` >> PairCases_on `fv` >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule_all calldata_dispatch_has_source_entry >> strip_tac >>
  qspecl_then [`fin`, `policy`, `tops`, `deploy_bc`, `runtime_bc`, `am`,
               `tx with <| function_name := fv0; args := fv1 |>`, `ret`, `es`]
    mp_tac vyper_call_correct_dispatched >>
  impl_tac >- gvs[dispatched_vyper_call_def, call_premises_dispatch_invariant] >>
  strip_tac >> simp[external_return_type_def] >> metis_tac[]
QED

(* The fixed persistent and transient regions decode in the source state,
   with consistent layouts and separated nonreentrant locks. *)
Definition storage_ok_def:
  storage_ok H am tx <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
      regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
      storage_well_formed_on cx (initial_state am []) (FST H)
End

(* Every gas filling of the dispatched call stays within the fixed regions. *)
Definition call_within_def:
  call_within H tops am tx es <=>
    let cx = initial_evaluation_context am.sources am.layouts tx NONE in
    !f vals gobs.
      calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
      storage_observations_ok cx H
        (source_storage_trace am (tx with <| function_name := f; args := vals |>)
           (MAP SND (call_trace es)) gobs)
End

(* Result agreement at the run's own storage horizon and preservation of H. *)
Definition call_result_rel_def:
  call_result_rel H tops am tx es r es' <=>
    let os = MAP SND (call_trace es) in
    gas_readings_rel (gas_readings es)
      (\gobs. call_result_rel_at gobs tops am tx es r es' /\
              let (res, am', rqs) = call_external (SOME os) gobs am tx in
                storage_ok H am' tx)
End

Definition calldata_result_rel_def:
  calldata_result_rel H tops am tx es r es' <=>
    case calldata_dispatch tops tx.calldata of
      NONE => frame_raises es Reverted /\
              ?lgs. frame_outcome es r es' (SOME Reverted) [] lgs
    | SOME (f, vals) =>
        call_result_rel H tops am (tx with <| function_name := f; args := vals |>) es r es'
End

Triviality valid_horizon_for_dispatch:
  storage_ok H am tx /\ call_within H tops am tx es /\
  calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
  valid_horizon
    (initial_evaluation_context am.sources am.layouts
       (tx with <| function_name := f; args := vals |>) NONE)
    (initial_state am []) H
    (source_storage_trace am (tx with <| function_name := f; args := vals |>)
       (MAP SND (call_trace es)) gobs)
Proof
  simp[storage_ok_def, call_within_def, valid_horizon_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `storage_well_formed_on cx _ _` >>
  qmatch_goalsub_abbrev_tac `storage_well_formed_on dispatched_cx _ _` >>
  `dispatched_cx.txn.target = cx.txn.target` by
    simp[Abbr `cx`, Abbr `dispatched_cx`, initial_evaluation_context_def] >>
  `storage_well_formed_on dispatched_cx (initial_state am []) (FST H) <=>
   storage_well_formed_on cx (initial_state am []) (FST H)` by
    (irule storage_well_formed_on_target >> simp[]) >>
  drule storage_observations_ok_target >> strip_tac >>
  fs[]
QED

Triviality call_result_rel_from_guarded:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  (!gobs. valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) H (source_storage_trace am tx (MAP SND (call_trace es)) gobs)) /\
  call_result_rel_guarded tops am tx es r es' ==>
  call_result_rel H tops am tx es r es'
Proof
  simp[call_result_rel_guarded_def, call_result_rel_def] >>
  strip_tac >>
  drule gas_readings_rel_mono >> disch_then irule >>
  qx_gen_tac `gobs` >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!gobs. valid_horizon _ _ _ _` (qspec_then `gobs` assume_tac) >>
  conj_tac
  >- (qpat_x_assum `call_storage_ok _ _ _ gobs ==> _` match_mp_tac >>
      irule valid_horizon_call_storage_ok >> qexists_tac `H` >> simp[]) >>
  qabbrev_tac `os = MAP SND (call_trace es)` >>
  `?res am' rqs obs. call_external_trace (SOME os) gobs am tx =
     (res,am',rqs,obs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  drule call_external_trace_result >> strip_tac >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) H obs` by fs[] >>
  drule_all source_call_final_storage_well_formed >> strip_tac >>
  `storage_well_formed_on (initial_evaluation_context am'.sources am'.layouts tx NONE)
     (initial_state am' []) (FST H) <=>
   storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am' []) (FST H)` by
    (irule storage_well_formed_on_target >> simp[initial_evaluation_context_def]) >>
  fs[storage_ok_def, valid_horizon_def]
QED

(* TOP-LEVEL: single-call compiler correctness with fixed storage regions. *)
Theorem vyper_call_correct:
  !fin policy tops deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    storage_ok H am tx /\
    call_within H tops am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       calldata_result_rel H tops am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all vyper_call_correct_guarded >>
  disch_then (qx_choose_then `r` (qx_choose_then `es'` strip_assume_tac)) >>
  qexistsl_tac [`r`, `es'`] >> asm_rewrite_tac[] >>
  DISJ2_TAC >>
  qpat_x_assum `calldata_result_rel_guarded _ _ _ _ _ _` mp_tac >>
  simp[calldata_result_rel_def, calldata_result_rel_guarded_def] >>
  Cases_on `calldata_dispatch tops tx.calldata` >> simp[] >>
  rename1 `_ = SOME entry` >> PairCases_on `entry` >>
  simp[pairTheory.pair_case_thm] >>
  rename1 `calldata_dispatch tops tx.calldata = SOME (f, vals)` >>
  strip_tac >>
  qabbrev_tac `dispatched_tx = tx with <| function_name := f; args := vals |>` >>
  `source_typing_ok tops am dispatched_tx /\
   call_state_rel tops runtime_bc am dispatched_tx es` by
    simp[Abbr `dispatched_tx`, call_premises_dispatch_invariant] >>
  `source_deployment_rel tops am dispatched_tx` by
    (qpat_assum `call_state_rel _ _ _ dispatched_tx _`
       (strip_assume_tac o REWRITE_RULE [call_state_rel_def]) >>
     first_assum ACCEPT_TAC) >>
  irule call_result_rel_from_guarded >> simp[] >>
  gen_tac >> simp[Abbr `dispatched_tx`] >>
  irule valid_horizon_for_dispatch >> simp[] >> qexists_tac `tops` >> simp[]
QED
