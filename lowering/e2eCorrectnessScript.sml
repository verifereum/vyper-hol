(* End-to-End Vyper-to-EVM Correctness (PLAN §2.1/§8.1).
 * TOP-LEVEL: vyper_call_correct (exact §2.1, composed from S1-S7, over the
 * accepted finalizers; vyper_call_correct_identity and
 * vyper_call_correct_asm_opt are its two cases),
 * vyper_call_correct_at_marks (the call theorem at fixed gas marks),
 * call_pipeline_gas_link (admission: the guarded fillings of the frame's gas
 * readings select raw entry states; the call twin of deploy_pipeline_gas_link),
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
  e2eProducers e2eEntry o1PipelineCorrect o1PassContract contextCodegenRel
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeProps loweringShapeSource vfmExecution
  passSimulationDefs
  codegenCorrectness immutableCodeLayout asmOptimizer
  stateEquiv stateEquivProps
  venomExecSemantics
  vyperABI
  vyperInterpreter
  compileEnv loweringStateRelDefs compileVyper
  venomInst
  sourceUnitExecution gasSummary supportedProgram callTrace frameOutcome
  vyperStorageFootprint fragGasPathMem fragExecMem fragGasOrigin fragGasMode
  fragExec memSafeRun venomExecProofs unitShapeDefs
  list

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
         (frame_resource_starved es r es' \/ precompile_call_starved es \/
          venom_frame_rel es r es' (run_context fuel ctx' vs_out)))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/ precompile_call_starved es \/
             call_result_rel_at gobs tops ret am tx es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `source_exempt tops (call_external (SOME vs_in.vs_outcomes) gobs am tx)`
  >- (disj2_tac >> disj2_tac >>
      irule source_exempt_call_result_rel >> gvs[]) >>
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
  drule_all external_call_result_rel_frame >> simp[]
QED

Theorem e2e_vyper_to_evm:
  !gobs tops ret am tx ctx ctx' vs es.
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
             call_result_rel_at gobs tops ret am tx es r es')
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
  drule_all external_call_result_rel_frame >> simp[]
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

Theorem gas_variant_outcomes:
  gas_variant si so ==> si.vs_outcomes = so.vs_outcomes
Proof
  rw[gas_variant_def] >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem gas_variant_call_ctx:
  gas_variant si so ==> si.vs_call_ctx = so.vs_call_ctx
Proof
  rw[gas_variant_def] >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem gas_variant_initial_venom_state_rel:
  gas_variant si so /\ initial_venom_state_rel tops am tx so ==>
  initial_venom_state_rel tops am tx si
Proof
  rw[gas_variant_def] >>
  qpat_x_assum `so = _` SUBST_ALL_TAC >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def]
QED

(* ===== PLAN §2.1 call theorem: seven stage leaves, raw O1 source domain ===== *)
(* The call theorem at one fixed gas marking, then at every guarded filling of
   the frame's gas readings through the gas link. *)

Theorem gas_readings_rel_mono[local]:
  !readings P Q.
    gas_readings_rel readings P T /\ (!gs. P gs ==> Q gs) ==>
    gas_readings_rel readings Q T
Proof
  rw[gas_readings_rel_def] >> metis_tac[]
QED

Theorem call_at_horizon_composition[local]:
  run_call es = SOME (r, es') /\ ~frame_resource_starved es r es' /\
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
  call_result_rel_at gs tops ret am tx es r es'
Proof
  rpt strip_tac >>
  drule_all external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  qpat_x_assum `!n. ?r' es''. _` (qspec_then `fuel'` strip_assume_tac) >>
  gvs[] >>
  drule_all external_call_result_rel_dead_transport >> strip_tac >>
  drule_all external_call_result_rel_frame >> simp[]
QED

(* The S3 memory facts of the raw unit from the entry's memory- and
   pointer-safe runs, through the loweringMemCorrect bridges. *)
Theorem selected_raw_memory[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  o1_source_unit_ok unit /\
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
  mem_inv dload_headroom_ok unit.cu_context vs
Proof
  strip_tac >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  mp_tac (Q.SPECL [`tops`, `rp`, `unit`, `am`, `tx`, `vs`, `fn`, `"__entry"`, `D`]
            lower_vyper_runtime_unit_memory_ok) >>
  impl_tac >- fs[] >> strip_tac >> simp[] >>
  conj_tac
  >- metis_tac[lower_vyper_runtime_unit_dload_offset_ok] >>
  metis_tac[lower_vyper_runtime_unit_dload_headroom_ok]
QED

Theorem selected_run[local]:
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
Theorem vyper_call_correct_at_marks:
  !policy tops deploy_bc runtime_bc am tx ret es rpolicy unit out prog cp vs marks.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    gas_variant vs (entry_venom_state prog cp es) /\
    (!H:(bool # bytes32 # type_value) list # num list. raw_unit_memory_ok unit.cu_context vs /\
         ptr_discipline 0 unit.cu_context vs /\
         taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
           unit.cu_context vs /\
         mem_inv dload_offset_ok unit.cu_context vs /\
         mem_inv dload_headroom_ok unit.cu_context vs ==>
         ctx_sim (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
           unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
         o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
    source_unit_execution_correct_at marks tops ret am tx unit vs
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       !tail.
         source_storage_ok am tx (MAP SND (call_trace es))
           (gas_explicit marks vs.vs_gas_readings ++ tail) /\
         call_outcomes_storage_ok am tx (MAP SND (call_trace es))
           (gas_explicit marks vs.vs_gas_readings ++ tail) ==>
         call_result_rel_at (gas_explicit marks vs.vs_gas_readings ++ tail)
           tops ret am tx es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  `runtime_bc = assemble prog` by
    (drule compile_vyper_runtime_phases >> strip_tac >> gvs[]) >>
  qpat_x_assum `runtime_bc = _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `code_layout_valid (entry_venom_state prog cplan es)` by
    (irule immutableCodeLayoutTheory.generated_entry_code_layout_shape >> metis_tac[]) >>
  `vs.vs_outcomes = MAP SND (call_trace es) /\ code_layout_valid vs` by
    (qpat_assum `gas_variant _ _` mp_tac >>
     pure_rewrite_tac[gas_variant_def] >>
     disch_then (mp_tac o Q.AP_TERM
       `\s:venom_state. (s.vs_outcomes,code_layout_valid s)`) >>
     simp[code_layout_valid_def] >>
     simp[entry_venom_state_def, venomStateTheory.init_venom_state_def] >>
     fs[code_layout_valid_def, entry_venom_state_def]) >>
  `initial_venom_state_rel tops am tx vs` by
    (irule gas_variant_initial_venom_state_rel >>
     qexists_tac `entry_venom_state prog cplan es` >> simp[] >>
     irule entry_venom_state_initial_venom_state_rel >> simp[]) >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _` mp_tac >>
  simp[source_unit_execution_correct_at_def] >> strip_tac
  >- metis_tac[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `tail` assume_tac) >>
  drule call_external_trace_result >> strip_tac >>
  Cases_on `source_exempt tops (res,am',rqs)`
  >- (irule source_exempt_call_result_rel >> simp[]) >>
  gvs[] >>
  drule_all selected_run >> strip_tac >>
  drule_all (REWRITE_RULE [storage_trace_domain_def] source_storage_guards_domain) >>
  strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_safe_blocks D` >>
  `raw_unit_memory_ok unit.cu_context vs /\
   ptr_discipline 0 unit.cu_context vs /\ taint_within D unit.cu_context vs /\
   mem_inv dload_offset_ok unit.cu_context vs /\
   mem_inv dload_headroom_ok unit.cu_context vs` by
    (irule selected_raw_memory >> metis_tac[]) >>
  `ctx_sim D unit.cu_context out.po_unit.cu_context vs
     (entry_venom_state prog cplan es) /\
   o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cplan es)` by
    (fs[Abbr `D`] >>
     qpat_x_assum `!H. taint_within (cx_dead H _) _ _ ==> _` drule >>
     simp[]) >>
  `(entry_venom_state prog cplan es).vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[entry_venom_state_def] >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `initial_ctx_rel cplan prog out.po_unit.cu_context
     (entry_venom_state prog cplan es) es` by
    (irule entry_venom_state_initial_ctx_rel >> metis_tac[]) >>
  `!n. ?rr ee. run_call es = SOME (rr,ee) /\
     (frame_resource_starved es rr ee \/
      venom_frame_rel es rr ee
        (run_context n out.po_unit.cu_context (entry_venom_state prog cplan es)))` by
    (gen_tac >> irule codegen_correct >> metis_tac[]) >>
  irule call_at_horizon_composition >>
  simp[] >>
  qexistsl_tac [`unit.cu_context`, `out.po_unit.cu_context`, `fuel`, `vs`,
               `entry_venom_state prog cplan es`] >>
  simp[] >>
  fs[Abbr `D`, cx_dead_def, external_call_dead_def,
     initial_evaluation_context_def] >>
  gen_tac >> qpat_x_assum `!n. ?rr ee. _` (qspec_then `n` strip_assume_tac) >>
  gvs[]
QED

(* ADMISSION (argon, 2026-11-13; the call twin of deploy_pipeline_gas_link).
   Where the frame is not starved, every filling of its gas readings that
   meets the source run's storage guards extends the marked readings of a raw
   entry state carrying the S4 facts and the selected-run certificate.  The
   raw state, marks and tail are chosen inside each filling.  The only
   admission on vyper_call_correct_identity's path. *)
Theorem call_pipeline_gas_link:
  !policy tops deploy_bc runtime_bc rpolicy unit out prog cp am tx ret es r es'.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    (!vs. gas_variant vs (entry_venom_state prog cp es) ==>
          source_unit_execution_correct tops ret am tx unit vs) /\
    run_call es = SOME (r, es') /\
    ~frame_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. source_storage_ok am tx (MAP SND (call_trace es)) gs /\
            call_outcomes_storage_ok am tx (MAP SND (call_trace es)) gs ==>
            ?vs marks tail.
              gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
              gas_variant vs (entry_venom_state prog cp es) /\
              (!H:(bool # bytes32 # type_value) list # num list.
                 raw_unit_memory_ok unit.cu_context vs /\
                 ptr_discipline 0 unit.cu_context vs /\
                 taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
                   unit.cu_context vs /\
                 mem_inv dload_offset_ok unit.cu_context vs /\
                 mem_inv dload_headroom_ok unit.cu_context vs ==>
                 ctx_sim (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
                   unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
                 o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
              source_unit_execution_correct_at marks tops ret am tx unit vs) T
Proof
  cheat
QED

(* Where the frame is not starved and the gas link holds, the call result
   relation holds at every guarded filling. *)
Theorem vyper_call_correct_from_gas_link:
  !policy tops deploy_bc runtime_bc am tx ret es r es' rpolicy unit out prog cp.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/
     gas_readings_rel (gas_readings es)
       (\gs. source_storage_ok am tx (MAP SND (call_trace es)) gs /\
             call_outcomes_storage_ok am tx (MAP SND (call_trace es)) gs ==>
             ?vs marks tail.
               gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
               gas_variant vs (entry_venom_state prog cp es) /\
               (!H:(bool # bytes32 # type_value) list # num list.
                  raw_unit_memory_ok unit.cu_context vs /\
                  ptr_discipline 0 unit.cu_context vs /\
                  taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
                    unit.cu_context vs /\
                  mem_inv dload_offset_ok unit.cu_context vs /\
                  mem_inv dload_headroom_ok unit.cu_context vs ==>
                  ctx_sim (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
                    unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
                  o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
               source_unit_execution_correct_at marks tops ret am tx unit vs) T)
    ==>
    frame_resource_starved es r es' \/
    call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >>
  Cases_on `frame_resource_starved es r es'` >> fs[] >>
  simp[call_result_rel_def] >>
  drule gas_readings_rel_mono >> disch_then irule >>
  rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `_ /\ _ ==> ?vs marks tail. _` mp_tac >>
  impl_tac >- fs[] >> strip_tac >>
  gvs[] >>
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `am`, `tx`, `ret`, `es`,
               `rpolicy`, `unit`, `out`, `prog`, `cp`, `vs`, `marks`] mp_tac
    vyper_call_correct_at_marks >>
  impl_tac >- fs[] >> strip_tac >> gvs[]
QED

Theorem vyper_call_correct_identity:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel tops ret am tx es r es')
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  `outcomes_accounts_typed (SOME (MAP SND (call_trace es)))` by
    (`wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
       fs[call_state_rel_def] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, listTheory.EVERY_MEM]) >>
  `initial_venom_state_rel tops am tx (entry_venom_state prog cplan es)` by
    (irule entry_venom_state_initial_venom_state_rel >> gvs[]) >>
  `!vs. gas_variant vs (entry_venom_state prog cplan es) ==>
        source_unit_execution_correct tops ret am tx unit vs` by
    (rpt strip_tac >>
     `vs.vs_outcomes = MAP SND (call_trace es) /\
      vs.vs_call_ctx.cc_calldata =
        buffer_to_list (FST (HD es.contexts)).msgParams.data` by
       (imp_res_tac gas_variant_outcomes >> imp_res_tac gas_variant_call_ctx >>
        gvs[entry_venom_state_def]) >>
     `initial_venom_state_rel tops am tx vs` by
       metis_tac[gas_variant_initial_venom_state_rel] >>
     irule lower_vyper_runtime_unit_correct >>
     qexists_tac `rpolicy` >> gvs[]) >>
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`, `unit`,
               `out`, `prog`, `cplan`, `am`, `tx`, `ret`, `es`, `r`, `es'`] mp_tac
    call_pipeline_gas_link >>
  impl_tac >- fs[] >> strip_tac >>
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `am`, `tx`, `ret`, `es`,
               `r`, `es'`, `rpolicy`, `unit`, `out`, `prog`, `cplan`] mp_tac
    vyper_call_correct_from_gas_link >>
  impl_tac >- fs[] >> simp[]
QED

(* The final assembly optimizer's case: the program, compiled with Python's
   O1 final assembly optimizer, under the same hypotheses plus the temporary
   exclusion of programs that read their own code. *)
Theorem vyper_call_correct_asm_opt:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel tops ret am tx es r es')
Proof
  cheat
QED

(* TOP-LEVEL: one theorem over the accepted finalizers (Python's -O none and
   O1 final assembly).  The optimizer's case excludes, for now, programs that
   read their own code. *)
Theorem vyper_call_correct:
  !fin policy tops deploy_bc runtime_bc am tx ret es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel tops ret am tx es r es')
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
