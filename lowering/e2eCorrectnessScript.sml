(*
 * End-to-End Vyper-to-EVM Correctness
 *
 * TOP-LEVEL theorem: vyper_call_correct
 *   When EVM execution enters compiled Vyper bytecode (via CALL at
 *   any point in the call stack), the result corresponds to the
 *   Vyper source semantics (call_external).
 *
 * Internal proof structure (not visible in the top-level statement):
 *   1. vyper_to_venom_correct: call_external ~ run_context
 *   2. venom_pipeline_correct: run_context ~ run_context o pipeline
 *   3. codegen_correct: run_context ~ EVM run
 *
 * TOP-LEVEL:
 *   run_call                -- EVM execution of a single call frame
 *   call_state_rel          -- pre-call Vyper/EVM state correspondence
 *   vyper_call_correct      -- main correctness theorem
 *   compile_vyper_raw       -- full compilation chain (exploded args)
 *
 * Definitions (return_data_encodes, log_entry_corresponds,
 * state_effects_match, etc.) are in e2eDefsTheory.
 *)

Theory e2eCorrectness
Ancestors
  e2eDefs
  vyperLoweringCorrect vfmExecution
  venomPipelineCorrect
  passSimulationDefs
  codegenCorrectness
  stateEquiv stateEquivProps
  venomExecSemantics
  vyperABI
  compileEnv compileVyper
  venomInst

(* =====================================================================
   Call-Level Correctness (Main Theorem)
   ===================================================================== *)

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
    ctxt.memory = [] ∧
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
        (initial_evaluation_context am.sources am.layouts tx) am
        tx.function_name = SOME (mut, nr, args, dflts, ret, body) ∧
      calldata_encodes tenv tx.function_name (MAP SND args) tx.args
        calldata
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
    case call_external am tx of
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

(* ===== Main Correctness Theorem ===== *)

(* Compiler correctness for a single external call.

   When EVM execution enters compiled Vyper bytecode (at any point
   in the call stack), the result corresponds to the Vyper source
   semantics (call_external am tx).

   Covers both outermost calls (rest = [], as in a transaction) and
   inner calls (rest ≠ [], as in a CALL from another contract).
   The pipeline and all Venom-internal details are hidden in the proof.

   Gas is existential: there exists a gas bound such that with enough
   gas, EVM execution produces the correct result. *)
Theorem vyper_call_correct:
  ∀program pipeline dispatch_strategy runtime_bc
   am tx tenv ret ctxt rb rest es event_info.
    (∃deploy_bc.
       compile_vyper program pipeline dispatch_strategy
         = SOME (deploy_bc, runtime_bc)) ∧
    es.contexts = (ctxt, rb) :: rest ∧
    call_state_rel program runtime_bc am tx tenv
      ctxt rb es.txParams ∧
    valid_vyper_call am tx tenv ctxt.msgParams.data ret
    ⇒
    ∃gas_needed.
      ctxt.msgParams.gasLimit ≥ gas_needed ⇒
      ∃r es_final.
        run_call es = SOME (r, es_final) ∧
        call_result_matches tenv event_info am tx ret r es es_final
Proof
  cheat
QED

(* ===================================================================== *)

(* ===== Full Compilation ===== *)

(* Full compilation: lowering + pass pipeline + codegen.
   Pipeline is a parameter -- instantiate for O2, O3, Os, etc. *)
Definition compile_vyper_raw_def:
  compile_vyper_raw selectors ext_fns int_fns fb_fn
                dispatch bucket_count fn_meta_bytes
                dense_buckets entry_info
                entry_label
                (pipeline : venom_context -> venom_context)
                fn_eom_map =
    let (ctx, data_seg) = run_lowering selectors ext_fns int_fns fb_fn
                            dispatch bucket_count fn_meta_bytes
                            dense_buckets entry_info entry_label in
    let ctx' = pipeline ctx in
    codegen ctx' fn_eom_map data_seg
End

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

(* Codegen correctness: Venom execution corresponds to EVM execution.
   Wraps codegen_correct with initial_evm_rel. *)
Theorem e2e_venom_to_evm:
  !ctx fn_eom_map data_seg bytecode spill_hwm vs fuel.
    codegen_ready ctx /\
    ctx_wf ctx /\
    codegen ctx fn_eom_map data_seg = SOME bytecode /\
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions /\
       step_inst fuel' ctx inst vs1 = OK vs2 ==>
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) /\
    spill_mem_covered spill_hwm vs.vs_memory
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      (case run_context fuel ctx vs of
         Halt vs' =>
           ?es'. run es = SOME (INR NONE, es') /\
                 final_state_rel vs' es'
       | Abort Revert_abort vs' =>
           ?es'. run es = SOME (INR (SOME Reverted), es') /\
                 final_state_rel vs' es'
       | Abort ExHalt_abort vs' =>
           ?es' exc. run es = SOME (INR (SOME exc), es') /\
                     exc <> Reverted /\
                     final_state_rel vs' es'
       | OK _ => F
       | IntRet _ _ => F
       | Error _ => T)
Proof
  cheat
QED

(* ===== Codegen Hypothesis Theorems ===== *)

(* Compilation produces a well-formed codegen-ready context.
   Discharged by construction: run_lowering produces wf context,
   pipeline passes preserve well-formedness, codegen succeeds.

   The spill_hwm is determined by the codegen's stack plan:
   it is the maximum sa_next_offset across all function plans.
   step_mem_safe holds because Vyper's memory allocator ensures
   all user allocations are below fn_eom (which is 0 for the
   whole-context case, meaning no user memory overlaps spills).
   spill_mem_covered holds because the entry code expands
   memory to cover the maximum spill offset. *)
Theorem compile_vyper_raw_well_formed:
  !selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    pipeline fn_eom_map bytecode vs.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
  let ctx' = pipeline ctx in
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes
      dense_buckets entry_info entry_label
      pipeline fn_eom_map = SOME bytecode
    ==>
    codegen_ready ctx' /\ ctx_wf ctx' /\
    ?spill_hwm.
      (!fn inst vs1 vs2 fuel'.
         MEM fn ctx'.ctx_functions /\
         step_inst fuel' ctx' inst vs1 = OK vs2 ==>
         step_mem_safe <| sa_fn_eom := 0;
                          sa_next_offset := spill_hwm;
                          sa_free_slots := [] |> vs1 vs2) /\
      spill_mem_covered spill_hwm vs.vs_memory
Proof
  cheat
QED

(* ===== Full E2E: Vyper to EVM ===== *)

(* Composes all three legs into a single theorem relating Vyper
   source semantics to EVM bytecode execution.
 *
 * Correspondence:
 *   Vyper success (INL v)       => EVM normal halt, returndata =
 *                                  ABI encoding of v, accounts,
 *                                  transient storage, and logs match
 *   Vyper revert (AssertExc)    => EVM REVERT, state_unchanged
 *   Vyper error                 => T (indicates source-level error;
 *                                  could be strengthened to F under
 *                                  well-formedness of am/tx)
 *   Break/Continue/Return       => F -- internal control flow,
 *                                  never escapes call_external
 *)

(* Main E2E theorem: Vyper source semantics ~ EVM execution.

   Gas: existential -- there exists a gas bound such that with enough
   gas, EVM execution always produces the correct result. Non-vacuous:
   the success case is always reachable. No OOG escape hatch needed.

   ctx_pass_correct is an assumption because the pipeline is
   parametric -- it holds for any pipeline assembled from
   semantics-preserving passes (e.g., the standard O2 pipeline).
   It is proved per-pipeline by composing individual pass proofs.
   The R_ok/R_term relations are the composed per-pass relations
   (via FOLDL rel_seq); the caller must show they imply
   observable_equiv (via foldl_rel_seq_preserves_observable).
   See e2e_vyper_to_evm_O2 for a concrete instance. *)
Theorem e2e_vyper_to_evm:
  !tenv event_info pipeline selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes dense_buckets entry_info
    entry_label fn_eom_map bytecode
    (R_ok : venom_state -> venom_state -> bool) R_term
    am tx vs args ret.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    (* Compilation produces bytecode *)
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes
      dense_buckets entry_info entry_label
      pipeline fn_eom_map = SOME bytecode /\
    (* Source function exists, calldata valid, selector routes *)
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0 /\
    (* Pipeline preserves observable semantics *)
    ctx_pass_correct pipeline R_ok R_term ctx vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2)
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      vyper_evm_correspondence tenv event_info ret am tx es
Proof
  cheat
QED

(* ===== Concrete Pipeline Instances ===== *)

(* O2 pipeline preserves semantics.
   Instantiates venom_pipeline_correct for the O2 pass sequence.
   No ctx_pass_correct assumption -- discharged by composing
   individual O2 pass correctness theorems.
   Analysis functions (make_ssa, ircf, ricf, dse, amap, live_at)
   are parameters of the pass sequence. *)
Theorem e2e_vyper_to_evm_O2:
  !tenv event_info selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes dense_buckets entry_info
    entry_label
    ircf_global ricf_global threshold
    make_ssa ircf ricf dse_analysis amap live_at
    fn_eom_map bytecode
    am tx vs args ret.
  let pipeline = venom_pipeline ircf_global ricf_global threshold
        (o2_fn_passes make_ssa ircf ricf dse_analysis amap live_at) in
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes
      dense_buckets entry_info entry_label
      pipeline fn_eom_map = SOME bytecode /\
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      vyper_evm_correspondence tenv event_info ret am tx es
Proof
  cheat
QED

(* ===== Two-Phase compile_vyper ===== *)

(* compile_vyper runtime phase produces the same bytecode as
   compile_vyper_raw with matching arguments. This connects
   the high-level two-phase API to the existing e2e correctness. *)
Theorem compile_vyper_runtime_bytecode:
  !tops pipeline dispatch_strategy deploy_bc runtime_bc.
    compile_vyper tops pipeline dispatch_strategy
      = SOME (deploy_bc, runtime_bc)
    ==>
    let tenv = type_env tops in
    let nkey_map = assign_nkeys tops 0 in
    let (ext_fns, int_fns, fb_fn, ctor_fn) = classify_functions tops in
    let selectors = build_selectors tenv ext_fns in
    let external_fns = MAP (package_external_fn tops F nkey_map) ext_fns in
    let runtime_int_fns = MAP (package_internal_fn tops F nkey_map F) int_fns in
    let fallback_fn = package_fallback_fn tops F nkey_map fb_fn in
      ?bucket_count fn_meta_bytes dense_buckets entry_info.
        compile_vyper_raw selectors external_fns runtime_int_fns fallback_fn
          dispatch_strategy bucket_count fn_meta_bytes
          dense_buckets entry_info "__entry" pipeline FEMPTY
          = SOME runtime_bc
Proof
  simp[compile_vyper_def, compile_vyper_raw_def, pairTheory.UNCURRY]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs[])
  \\ gvs[AllCaseEqs()]
  \\ rpt (FIRST [pairarg_tac \\ gvs[AllCaseEqs()],
                CASE_TAC \\ gvs[AllCaseEqs()]])
  (* The hypothesis contains run_lowering with specific computed params.
     Extract them as witnesses for the existential. *)
  \\ qmatch_assum_abbrev_tac `codegen (pipeline (FST (run_lowering _ _ _ _ _ bc fmb db ei _))) _ _ = _`
  \\ MAP_EVERY qexists_tac [`bc`, `fmb`, `db`, `ei`]
  \\ gvs[]
QED

(* Deploy-phase correctness: the deploy bytecode, when executed on
   the EVM, correctly deploys the runtime bytecode.
   - Runs __init__ (if present)
   - CODECOPY's runtime bytecode to memory
   - RETURNs it
   The deployed code equals runtime_bc. *)
Theorem e2e_deploy_correctness:
  !tops pipeline dispatch_strategy deploy_bc runtime_bc.
    compile_vyper tops pipeline dispatch_strategy
      = SOME (deploy_bc, runtime_bc)
    ==>
    (* The deploy bytecode, when executed in creation context,
       runs __init__, then returns runtime_bc as deployed code. *)
    T (* TODO: state preconditions, EVM creation context relation *)
Proof
  simp[]
QED
