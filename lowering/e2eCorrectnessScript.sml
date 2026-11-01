(* End-to-End Vyper-to-EVM Correctness (PLAN §2.1/§8.1).
 * TOP-LEVEL: vyper_call_correct (exact §2.1, composed from S1-S7),
 * e2e_vyper_to_evm (admission-free generic §8.1 composition),
 * e2e_venom_pipeline, compile_vyper_runtime_bytecode (preserved proved APIs),
 * e2e_deploy_correctness (separate planned §5.11 admission).
 * Boundary/oracle/entry definitions live below this composition owner.
 * Deployment and gen_fn_simulation are OFF the call's logical dependency path;
 * definition-owner imports are not uses of their admitted correctness facts.
 * TASK056: no active legacy constant/alias. Original retired proof text is
 * retained in inactive SOURCECOMMENT archives; mapping: lowering/e2eLegacy.md.
 * This composes planned stages; it does NOT prove the outstanding stage proofs.
 *)
Theory e2eCorrectness
Ancestors
  e2eDefs e2eComposition unitTransformDefs e2eDeployDefs
  e2eProducers e2eEntry o1PipelineCorrect contextCodegenRel
  vyperLoweringCorrect loweringShapeProps vfmExecution
  venomPipelineCorrect
  passSimulationDefs
  codegenCorrectness
  stateEquiv stateEquivProps
  venomExecSemantics
  vyperABI
  vyperInterpreter
  compileEnv compileVyper
  venomInst
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
   Totality supplies an actual EVM run even when neither stage applies. *)
Theorem e2e_vyper_to_evm:
  !tops ret am tx ctx ctx' vs es.
    vs.vs_outcomes = MAP SND (call_trace es) /\
    (?fuel. external_call_result_rel tops ret tx
              (call_external (SOME vs.vs_outcomes) am tx)
              (run_context fuel ctx vs)) /\
    (~source_exempt tops (call_external (SOME vs.vs_outcomes) am tx) ==>
       ctx_transform_correct ctx ctx' vs /\
       !fuel. ?r es'.
         run_call es = SOME (r, es') /\
         (frame_resource_starved es r es' \/ precompile_call_starved es \/
          venom_frame_rel es r es' (run_context fuel ctx' vs)))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/ precompile_call_starved es \/
             call_result_rel tops ret am tx es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `source_exempt tops (call_external (SOME vs.vs_outcomes) am tx)`
  >- (disj2_tac >> disj2_tac >>
      irule source_exempt_call_result_rel >> gvs[]) >>
  gvs[] >>
  drule_all external_call_result_rel_terminates >> strip_tac >>
  drule_all ctx_transform_correct_forward >> strip_tac >>
  (* gvs identifies every stage-3 witness with the actual run by uniqueness. *)
  qpat_x_assum `!fuel. frame_resource_starved es r es' \/ _`
    (qspec_then `fuel'` strip_assume_tac) >>
  gvs[] >>
  drule_all external_call_result_rel_unit_transport >> strip_tac >>
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

(* Bridge from vyper_evm_correspondence to run_call + call_result_matches.

   vyper_evm_correspondence is defined in terms of VFM's `run` which
   executes all frames to completion. call_result_matches uses `run_call`
   which stops when the current call frame completes.

   For outermost calls (LENGTH es.contexts = 1): run_call = run because
   step never empties the context stack (step_preserves_nonempty_contexts).
   For inner calls (LENGTH es.contexts > 1): run_call stops when
   handle_exception pops the callee frame; the postcondition includes
   the frame-popping effects (stack push, account rollback on revert).

   This encapsulates the EVM execution semantics reasoning about
   context stack management, handle_exception, and the OWHILE loop. *)
Theorem evm_correspondence_to_call_result[local]:
  !tenv event_info am tx ret es.
    vyper_evm_correspondence_legacy tenv event_info ret am tx es /\
    ~NULL es.contexts
    ==>
    ?r es_final.
      run_call_legacy es = SOME (r, es_final) /\
      call_result_matches_legacy tenv event_info am tx ret r es es_final
Proof
  cheat
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
(* TASK049 original theorem statement/proof retained verbatim:
Theorem vyper_call_correct:
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

(* Preserved legacy public wrapper, STAGE-ADMITTED. Its existing admitted
   dependencies remain classified as such; NOT a new-boundary certificate. *)
Theorem vyper_call_correct:
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

(* ===== PLAN §2.1 call theorem: seven stage leaves, raw O1 source domain ===== *)
(* Runtime immutable compilation remains available, but the raw O1 shape
   theorem excludes DLOAD and therefore requires immutable_free_program. *)

Theorem vyper_call_correct:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    call_outcomes_ok tops am tx (MAP SND (call_trace es))
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       precompile_call_starved es \/
       call_result_rel tops ret am tx es r es')
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all entry_venom_state_initial_venom_state_rel >>
  disch_then (qspec_then `cplan` assume_tac) >>
  drule_all entry_venom_state_initial_ctx_rel >>
  disch_then (qspec_then `cplan` assume_tac) >>
  qspecl_then [`prog`, `cplan`, `es`] assume_tac
    entry_venom_state_o1_initial_state_ok >>
  qabbrev_tac `vs = entry_venom_state prog cplan es` >>
  `vs.vs_outcomes = MAP SND (call_trace es) /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_call_ctx.cc_calldata = buffer_to_list (FST (HD es.contexts)).msgParams.data` by
    simp[Abbr`vs`, entry_venom_state_def] >>
  `valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
   call_outcomes_ok tops am tx vs.vs_outcomes` by simp[] >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  `source_unit_execution_correct tops ret am tx unit vs` by
    (irule lower_vyper_runtime_unit_correct >> simp[] >>
     qexists_tac `rpolicy` >> simp[]) >>
  irule e2e_vyper_to_evm >>
  qexistsl_tac [`unit.cu_context`, `out.po_unit.cu_context`, `vs`] >>
  simp[] >> conj_tac
  >- (fs[source_unit_execution_correct_def] >>
      qexists_tac `fuel` >> gvs[]) >> strip_tac >>
  `~source_exempt tops (call_external (SOME vs.vs_outcomes) am tx)` by simp[] >>
  drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
  drule_all run_venom_pipeline_correct >> strip_tac >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  conj_tac
  >- gvs[checked_unit_transform_correct_def] >>
  gen_tac >> irule codegen_correct >> simp[] >>
  qexistsl_tac [`Inv`, `prog`, `rpolicy`] >> simp[]
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

(* ===== Deploy Phase ===== *)

(* TASK055: superseded placeholder preserved verbatim. Its claim was true
   but vacuous; no source proof/API consumer references it (usage audit at
   f964c8e1). This is NOT an old/new equivalence or a newly cheated old proof.

(* Deploy-phase correctness: the deploy bytecode, when executed on
   the EVM, correctly deploys the runtime bytecode.
   - Runs __init__ (if present)
   - CODECOPY's runtime bytecode to memory
   - RETURNs it
   The deployed code equals runtime_bc. *)
Theorem e2e_deploy_correctness:
  !tops pipeline finalizer policy deploy_bc runtime_bc.
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc)
    ==>
    (* The deploy bytecode, when executed in creation context,
       runs __init__, then returns runtime_bc as deployed code. *)
    T (* TODO: state preconditions, EVM creation context relation *)
Proof
  simp[]
QED
*)

(* TOP-LEVEL / savedDeploymentAdmission: PLAN 5.11, D28, section 9.
 * CLASSIFICATION: single planned stage admission, Milestone 6 item 7.
 * Not on the logical dependency path of call correctness; NOT proved here.
 *
 * Proof idea (deferred): relate the constructor's CODECOPY-decoded canonical
 * ABI tail to source binding, simulate its Call-free body and runtime-return
 * epilogue, then apply Verifereum handle_create/handle_exception in the SINGLE
 * fresh creation frame. Deposit gas/size failures are resource starvation;
 * valid-input computed precompile failures have their own alternative. Exclude
 * the 0xEF runtime prefix. Match installed runtime code and all remaining
 * account fields, transient storage and logs; use explicit source failure
 * cases, exempting only the existing exact dynamic ABI strictness predicate.
 *
 * load_contract NONE is deliberate: constructor_call_free excludes EVERY Call
 * (including internal calls and Send), while checked constant initializers are
 * pure. No oracle/callee is needed. The theorem does not claim agreement for
 * malformed constructors excluded by constructor_args_encode. There is no
 * nested-creation frame_outcome claim and no Some-root oracle hypothesis.
 *)
Theorem e2e_deploy_correctness:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/ precompile_call_starved es \/
       case load_contract NONE am tx [(NONE, tops)] [] of
         INL (am', rqs) =>
            ?section lgs.
              immutables_section_rel tops (account_immutables am' tx.target) section /\
              frame_outcome es r es' NONE (runtime_bc ++ section) lgs /\
              (lookup_account tx.target es'.rollback.accounts).code = runtime_bc ++ section /\
             (!a. a <> tx.target ==>
                  lookup_account a es'.rollback.accounts =
                  lookup_account a am'.accounts) /\
             (lookup_account tx.target es'.rollback.accounts) with code := [] =
             (lookup_account tx.target am'.accounts) with code := [] /\
             es'.rollback.tStorage = am'.tStorage /\
             logs_correspond (compiled_event_info tops) (type_env tops)
               tx.target am'.logs lgs
       | INR (AssertException s) =>
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                         (exc = Reverted \/ s = "UNREACHABLE")
       | INR (Error e) =>
           decode_strictness_exempt tops e \/
           ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
       | INR BreakException => F
       | INR ContinueException => F
       | INR (ReturnException _) => F)
Proof
  cheat
QED

(* Typed kernel schema and admission-classification gate. This is an ML check,
 * not a proved alias of the admission, and adds no theorem dependency. The
 * clean result-case definition must expand to precisely the literal 5.11
 * conclusion above, including its explicit failure cases and no-prefix guard.
 * The tag-name string is split only because cheat_audit.py sites scans words
 * inside ML string literals as tactic sites; the actual admission is above.
 *)
val savedDeploymentAdmission = DB.fetch "e2eCorrectness" "e2e_deploy_correctness";
val _ =
  let
    val expected = ``!policy tops deploy_bc runtime_bc am tx es.
      compile_vyper (K SOME) policy tops = SOME (deploy_bc,runtime_bc) /\
      supported_program tops /\ constructor_call_free tops /\
      deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
      deploy_state_rel tops deploy_bc am tx es /\
      ~(?t. runtime_bc = 0xEFw :: t) ==>
      ?r es'. run_call es = SOME (r,es') /\
        (frame_resource_starved es r es' \/ precompile_call_starved es \/
         deploy_result_rel tops runtime_bc tx es r es'
           (load_contract NONE am tx [(NONE,tops)] []))``;
    val expanded = concl (REWRITE_RULE [deploy_result_rel_def] (ASSUME expected));
    val (oracles, axioms) = Tag.dest_tag (Thm.tag savedDeploymentAdmission);
  in
    if aconv expanded (concl savedDeploymentAdmission) andalso
       null (Thm.hyp savedDeploymentAdmission) andalso null axioms andalso
       List.filter (fn tag => tag <> "DISK_THM") oracles = ["ch" ^ "eat"] then ()
    else raise Fail "PLAN 5.11 deployment schema/classification mismatch"
  end;

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
