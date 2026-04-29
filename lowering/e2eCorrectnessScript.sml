(*
 * End-to-End Vyper-to-EVM Correctness
 *
 * Two main theorems:
 *
 * 1. vyper_frame_correct (frame-level, primary)
 *    When EVM execution enters compiled Vyper bytecode (via CALL at
 *    any point in the call stack), the call frame's result corresponds
 *    to the Vyper source semantics (call_external).
 *    Uses VFM's run_call (stops when frame completes).
 *
 * 2. vyper_transaction_correct (transaction-level, corollary)
 *    For outermost calls (single context, transaction entry), the
 *    full EVM execution corresponds to Vyper semantics.
 *    Uses VFM's run (runs to completion).
 *    Derived from vyper_frame_correct via run_call_eq_run_single_context.
 *
 * Internal proof structure:
 *   1. vyper_to_venom_correct: call_external ~ run_context
 *   2. venom_pipeline_correct: run_context ~ run_context o pipeline
 *   3. codegen_correct: run_context ~ EVM run_call
 *
 * TOP-LEVEL:
 *   call_state_rel            -- pre-call Vyper/EVM state correspondence
 *   frame_result_matches      -- frame-level postcondition
 *   vyper_frame_correct       -- frame-level correctness (any depth)
 *   vyper_transaction_correct -- transaction-level correctness (single context)
 *   compile_vyper_raw         -- full compilation chain (exploded args)
 *
 * Definitions (return_data_encodes, log_entry_corresponds,
 * state_effects_match, etc.) are in e2eDefsTheory.
 *)

Theory e2eCorrectness
Ancestors
  e2eDefs
  vyperLoweringCorrect vfmExecution vfmRunCall
  venomPipelineCorrect
  passSimulationDefs
  codegenCorrectness
  stateEquiv stateEquivProps
  venomExecSemantics
  vyperABI
  compileEnv compileVyper
  venomInst

(* =====================================================================
   Frame-Level Correctness (Primary Theorem)
   ===================================================================== *)

(* Note: run_call is from vfmExecutionTheory / vfmRunCallTheory.
   It executes until the current call frame completes:
     run_call es = OWHILE (λ(r,s). ISL r ∧ LENGTH s.contexts ≥ LENGTH es.contexts)
                          (step o SND) (INL (), es)

   For single-context execution, run_call es = run es
   (proved as run_call_eq_run_single_context in vfmRunCallTheory). *)

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

(* EVM execution has two different behaviors depending on context depth:

   OUTERMOST (LENGTH es.contexts = 1):
   - handle_exception with n ≤ 1 reraises the exception
   - Result: INR exc_opt (NONE for success, SOME Reverted for revert)
   - Context stack unchanged (still 1 context)
   - run_call es = run es (by run_call_eq_run_single_context)

   INNER CALL (LENGTH es.contexts > 1):
   - handle_exception with n > 1 pops and incorporates
   - Result: INL () (execution continues in caller)
   - Context stack shrinks by 1 (callee frame popped)
   - Caller's context modified: stack pushed, returndata set, etc.

   We define separate predicates for clarity, then unify them. *)

(* ----- Outermost call result (single context, transaction entry) ----- *)

(* For outermost calls, we case-split on call_external FIRST, then
   specify what EVM result (r) is required. This enforces the
   correspondence:
   - call_external success ↔ EVM INR NONE
   - call_external AssertException ↔ EVM INR (SOME Reverted)
   - call_external Error ↔ any EVM result (T)
   - Break/Continue/Return ↔ impossible (F)

   The r parameter is the FULL first component of run_call/run result,
   i.e., (unit + exception option). This ensures the proof retains
   the connection between r and the final state es_f. *)
Definition outermost_result_matches_def:
  outermost_result_matches tenv event_info am tx ret r es es_f ⇔
    case call_external am tx of
      (INL v, am') =>
        (* Vyper success requires EVM success *)
        r = INR NONE ∧
        return_data_encodes tenv ret v es_f ∧
        state_effects_match event_info tx.target tenv am' es_f
    | (INR (AssertException _), _) =>
        (* Vyper revert requires EVM revert *)
        r = INR (SOME Reverted) ∧
        state_unchanged es es_f
    | (INR (Error _), _) => T
    | (INR BreakException, _) => F
    | (INR ContinueException, _) => F
    | (INR (ReturnException _), _) => F
End

(* ----- Inner call result (depth > 1, called from another contract) ----- *)

(* For inner calls, the callee frame is popped and the caller's context
   is modified with the call result. We case-split on call_external
   to specify the expected stack value (1w for success, 0w for revert). *)
Definition inner_call_result_matches_def:
  inner_call_result_matches tenv event_info am tx ret es es_f ⇔
    (* Callee was popped, caller is now on top *)
    LENGTH es_f.contexts = LENGTH es.contexts - 1 ∧
    LENGTH es.contexts > 1 ∧
    (∃caller_ctxt caller_rb rest.
       es_f.contexts = (caller_ctxt, caller_rb) :: rest ∧
       case call_external am tx of
         (INL v, am') =>
           (* Success: stack has 1w, returndata set, state committed *)
           ¬NULL caller_ctxt.stack ∧
           HD caller_ctxt.stack = 1w ∧
           return_data_encodes tenv ret v es_f ∧
           es_f.rollback.accounts = am'.accounts ∧
           es_f.rollback.tStorage = am'.tStorage
           (* Note: logs are pushed to caller by push_logs in
              pop_and_incorporate_context on success *)
       | (INR (AssertException _), _) =>
           (* Revert: stack has 0w, state rolled back *)
           ¬NULL caller_ctxt.stack ∧
           HD caller_ctxt.stack = 0w
           (* Note: rollback restored by set_rollback in
              pop_and_incorporate_context on failure *)
       | (INR (Error _), _) => T
       | (INR BreakException, _) => F
       | (INR ContinueException, _) => F
       | (INR (ReturnException _), _) => F)
End

(* ----- Unified frame result predicate ----- *)

(* Unifies outermost and inner call results based on context depth.
   Case-splits on call_external to determine what EVM result is expected.
   - Outermost: r = INR exc_opt, with exc_opt determined by call_external
   - Inner: r = INL (), with stack flag determined by call_external *)
Definition frame_result_matches_def:
  frame_result_matches tenv event_info am tx ret r es es_f ⇔
    if LENGTH es.contexts = 1 then
      (* Outermost call: r passed directly to outermost_result_matches *)
      outermost_result_matches tenv event_info am tx ret r es es_f
    else
      (* Inner call: r = INL () *)
      r = INL () ∧
      inner_call_result_matches tenv event_info am tx ret es es_f
End

(* ===== Main Frame-Level Correctness Theorem ===== *)

(* Compiler correctness for a single external call (frame-level).

   When EVM execution enters compiled Vyper bytecode (at any point
   in the call stack), the call frame's result corresponds to the
   Vyper source semantics (call_external am tx).

   Covers both outermost calls (rest = [], as in a transaction) and
   inner calls (rest ≠ [], as in a CALL from another contract).
   Uses VFM's run_call which stops when the current frame completes.

   Gas is existential: there exists a gas bound such that with enough
   gas, EVM execution produces the correct result. *)
Theorem vyper_frame_correct:
  ∀program pipeline dispatch_strategy runtime_bc
   am tx tenv ret ctxt rb rest es event_info deploy_bc.
    compile_vyper program pipeline dispatch_strategy
     = SOME (deploy_bc, runtime_bc) ∧
    es.contexts = (ctxt, rb) :: rest ∧
    call_state_rel program runtime_bc am tx tenv
      ctxt rb es.txParams ∧
    valid_vyper_call am tx tenv ctxt.msgParams.data ret
    ⇒
    ∃gas_needed.
      ctxt.msgParams.gasLimit ≥ gas_needed ⇒
      ∃r es_final.
        run_call es = SOME (r, es_final) ∧
        frame_result_matches tenv event_info am tx ret r es es_final
Proof
  (* Direct proof through:
     1. Lowering: vyper_to_venom_correct
     2. Pipeline: venom_pipeline_correct
     3. Codegen: codegen_correct *)
  cheat
QED

(* ===== Transaction-Level Correctness (Corollary) ===== *)

(* Bridge lemma: outermost_result_matches with INR NONE implies the success case of
   vyper_evm_correspondence. This is essentially definitional since
   outermost_result_matches was designed to match. *)
Theorem outermost_success_imp_correspondence:
  ∀tenv event_info am tx ret es es_f v am'.
    call_external am tx = (INL v, am') ∧
    outermost_result_matches tenv event_info am tx ret (INR NONE) es es_f
    ⇒
    return_data_encodes tenv ret v es_f ∧
    state_effects_match event_info tx.target tenv am' es_f
Proof
  rw[outermost_result_matches_def] >> gvs[]
QED

(* Bridge lemma: outermost_result_matches with INR (SOME Reverted) implies the revert case. *)
Theorem outermost_revert_imp_correspondence:
  ∀tenv event_info am tx ret es es_f.
    (∃msg am'. call_external am tx = (INR (AssertException msg), am')) ∧
    outermost_result_matches tenv event_info am tx ret (INR (SOME Reverted)) es es_f
    ⇒
    state_unchanged es es_f
Proof
  rw[outermost_result_matches_def] >>
  Cases_on `call_external am tx` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  Cases_on `e` >> gvs[]
QED

(* Bridge lemma: frame_result_matches for single context with INR NONE
   implies the success case of vyper_evm_correspondence. *)
Theorem frame_result_single_success_imp_correspondence:
  ∀tenv event_info am tx ret es es_f.
    LENGTH es.contexts = 1 ∧
    run es = SOME (INR NONE, es_f) ∧
    frame_result_matches tenv event_info am tx ret (INR NONE) es es_f
    ⇒
    vyper_evm_correspondence tenv event_info ret am tx es
Proof
  rw[frame_result_matches_def, vyper_evm_correspondence_def,
     outermost_result_matches_def] >>
  Cases_on `call_external am tx` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

(* Bridge lemma: frame_result_matches for single context with INR (SOME Reverted)
   implies the revert case of vyper_evm_correspondence. *)
Theorem frame_result_single_revert_imp_correspondence:
  ∀tenv event_info am tx ret es es_f.
    LENGTH es.contexts = 1 ∧
    run es = SOME (INR (SOME Reverted), es_f) ∧
    frame_result_matches tenv event_info am tx ret (INR (SOME Reverted)) es es_f
    ⇒
    vyper_evm_correspondence tenv event_info ret am tx es
Proof
  rw[frame_result_matches_def, vyper_evm_correspondence_def,
     outermost_result_matches_def] >>
  Cases_on `call_external am tx` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  Cases_on `e` >> gvs[] >>
  qexists_tac `es_f` >> simp[]
QED

(* For outermost calls (single context), run_call = run.
   This specializes vyper_frame_correct to transaction entry. *)
Theorem vyper_transaction_correct:
  ∀program pipeline dispatch_strategy runtime_bc
   am tx tenv ret ctxt rb es event_info deploy_bc.
    compile_vyper program pipeline dispatch_strategy
      = SOME (deploy_bc, runtime_bc) ∧
    es.contexts = [(ctxt, rb)] ∧
    call_state_rel program runtime_bc am tx tenv
      ctxt rb es.txParams ∧
    valid_vyper_call am tx tenv ctxt.msgParams.data ret
    ⇒
    ∃gas_needed.
      ctxt.msgParams.gasLimit ≥ gas_needed ⇒
      vyper_evm_correspondence tenv event_info ret am tx es
Proof
  rpt strip_tac
  (* Apply frame-level theorem *)
  \\ drule_all vyper_frame_correct
  \\ disch_then (qspec_then `event_info` strip_assume_tac)
  \\ qexists_tac `gas_needed`
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  (* For single context: run_call = run *)
  \\ `run_call es = run es` by
       (irule run_call_eq_run_single_context \\ simp[])
  (* frame_result_matches with LENGTH = 1 gives us INR result *)
  \\ gvs[frame_result_matches_def]
  >> gvs[vyper_evm_correspondence_def]
  >> BasicProvers.TOP_CASE_TAC
  >> gvs[outermost_result_matches_def]
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
    (!name efn. ctx.ctx_entry = SOME name /\
                lookup_function name ctx.ctx_functions = SOME efn ==>
                entry_fn_no_ret efn) /\
    codegen ctx fn_eom_map data_seg = SOME bytecode /\
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions /\
       step_inst fuel' ctx inst vs1 = OK vs2 ==>
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2)
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
  rpt strip_tac >>
  qsuff_tac `?gas_needed. !es.
    initial_ctx_rel ctx vs es /\
    (case es.contexts of
       [] => F
     | (ctxt,rb)::_ =>
       ctxt.msgParams.gasLimit >= gas_needed /\
       ctxt.msgParams.code = bytecode /\
       ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode) ==>
    (case run_context fuel ctx vs of
       OK _ => F
     | Halt vs' => ?es'. run es = SOME (INR NONE, es') /\ final_state_rel vs' es'
     | Abort Revert_abort vs' => ?es'. run es = SOME (INR (SOME Reverted), es') /\ final_state_rel vs' es'
     | Abort ExHalt_abort vs' => ?es' exc. run es = SOME (INR (SOME exc), es') /\ exc <> Reverted /\ final_state_rel vs' es'
     | IntRet _ _ => F
     | Error _ => T)`
  >- (strip_tac >> qexists `gas_needed` >> rpt strip_tac >>
      first_x_assum irule >>
      Cases_on `es.contexts` >> gvs[initial_evm_rel_def, initial_ctx_rel_def] >>
      PairCases_on `h` >> gvs[]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `fn_eom_map`, `data_seg`,
    `bytecode`, `spill_hwm`, `vs`] codegen_correct) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[]
QED

(* ===== Codegen Hypothesis Theorems ===== *)

(* Successful codegen implies the context was well-formed.
   codegen checks various structural properties (via generate_context_plan)
   before producing bytecode, so success implies the inputs met
   codegen_ready and ctx_wf. *)
Theorem codegen_implies_wf[local]:
  !ctx fn_eom_map data_seg bytecode.
    codegen ctx fn_eom_map data_seg = SOME bytecode ==>
    codegen_ready ctx /\ ctx_wf ctx
Proof
  cheat
QED

(* Successful codegen implies step_mem_safe.
   The codegen plan allocates spill slots with specific offsets;
   step_mem_safe holds because compiled instructions only access
   memory within the planned spill region. *)
Theorem codegen_implies_mem_safe[local]:
  !ctx fn_eom_map data_seg bytecode.
    codegen ctx fn_eom_map data_seg = SOME bytecode ==>
    ?spill_hwm.
      (!fn inst vs1 vs2 fuel'.
         MEM fn ctx.ctx_functions /\
         step_inst fuel' ctx inst vs1 = OK vs2 ==>
         step_mem_safe <| sa_fn_eom := 0;
                          sa_next_offset := spill_hwm;
                          sa_free_slots := [] |> vs1 vs2)
Proof
  cheat
QED

Theorem codegen_implies_entry_fn_no_ret[local]:
  !ctx fn_eom_map data_seg bytecode.
    codegen ctx fn_eom_map data_seg = SOME bytecode ==>
    (!name efn. ctx.ctx_entry = SOME name /\
                lookup_function name ctx.ctx_functions = SOME efn ==>
                entry_fn_no_ret efn)
Proof
  cheat
QED

Theorem compile_vyper_raw_well_formed:
  !selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    pipeline fn_eom_map bytecode.
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
    (!name efn. ctx'.ctx_entry = SOME name /\
                lookup_function name ctx'.ctx_functions = SOME efn ==>
                entry_fn_no_ret efn) /\
    ?spill_hwm.
      (!fn inst vs1 vs2 fuel'.
         MEM fn ctx'.ctx_functions /\
         step_inst fuel' ctx' inst vs1 = OK vs2 ==>
         step_mem_safe <| sa_fn_eom := 0;
                          sa_next_offset := spill_hwm;
                          sa_free_slots := [] |> vs1 vs2)
Proof
  rpt gen_tac
  \\ simp[pairTheory.UNCURRY]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ strip_tac
  \\ `codegen (pipeline (FST (run_lowering selectors ext_fns int_fns fb_fn
        dispatch bucket_count fn_meta_bytes dense_buckets entry_info
        entry_label))) fn_eom_map
       (SND (run_lowering selectors ext_fns int_fns fb_fn dispatch
        bucket_count fn_meta_bytes dense_buckets entry_info entry_label))
     = SOME bytecode` by (
      gvs[compile_vyper_raw_def, pairTheory.UNCURRY] >>
      CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> gvs[])
  \\ drule codegen_implies_wf \\ strip_tac \\ simp[]
  \\ drule codegen_implies_entry_fn_no_ret \\ strip_tac \\ simp[]
  \\ drule (SRULE [] codegen_implies_mem_safe)
  \\ strip_tac
  \\ qexists `spill_hwm` \\ gvs[]
QED

(* ===== Lowering Log Correspondence ===== *)

(* The lowering preserves log semantics: Venom events produced by
   run_context correspond to Vyper's logs via logs_correspond.
   This supplements vyper_to_venom_correct (which establishes
   external_call_result_rel covering returndata/accounts/transient
   but not logs).

   The log relationship requires event_info (mapping event names
   to hashes and indexed flags), which is only available at the
   e2e level. The lowering translates Vyper push_log into Venom
   LOG instructions, producing events with:
   - logger = tx.target (the contract address)
   - topics = [event_hash; indexed_val_1; ...]
   - data = ABI-encoded non-indexed values

   This is cheated at the same level as the Props theorems. *)
Theorem vyper_lowering_logs_correct[local]:
  !tenv event_info selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    vs am tx sel fn_lbl htz
    args dflts ret body mut nr.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx) am
      tx.function_name = SOME (mut, nr, args, dflts, ret, body) /\
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      vs.vs_call_ctx.cc_calldata /\
    MEM (sel, fn_lbl, htz) selectors /\
    selector_matches sel tx.function_name
      (vyper_to_abi_types tenv (MAP SND args)) /\
    vs.vs_inst_idx = 0
    ==>
    ?fuel.
      external_call_result_rel tenv ret
        (call_external am tx)
        (run_context fuel ctx vs) /\
      (case (call_external am tx, run_context fuel ctx vs) of
         ((INL v, am'), Halt ss') =>
           logs_correspond event_info tenv tx.target am'.logs ss'.vs_logs
       | _ => T)
Proof
  cheat
QED

(* Helper: expand let (x,y) = M in body  to  body[FST M/x, SND M/y] *)
fun expand_pair_let thm =
  thm |> SIMP_RULE bool_ss [LET_THM]
      |> CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV);

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

(* EVM REVERT preserves the rollback state.
   This is a basic EVM semantic property: the REVERT opcode
   causes execution to halt with Reverted status, and the
   rollback mechanism restores accounts and transient storage
   to their pre-call values.

   CAVEAT: set_original (used in proceed_create/CREATE opcode)
   modifies SND(LAST s.contexts).accounts for EIP-2200 gas metering.
   For single-frame execution, this means SND(HD s.contexts) can
   change during CREATE. This lemma is correct when no CREATE
   opcodes are executed, or when state_unchanged is weakened to
   compare s.rollback instead of SND(HD s.contexts).
   TODO: Verify state_unchanged definition is appropriate. *)
Theorem evm_revert_state_unchanged[local]:
  !es es'. run es = SOME (INR (SOME Reverted), es') /\
           ~NULL es.contexts
           ==>
           state_unchanged es es'
Proof
  cheat
QED

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
  rpt gen_tac
  \\ simp[pairTheory.UNCURRY]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ strip_tac
  \\ gvs[valid_function_call_def]
  (* Step 1: Apply lowering correctness *)
  \\ drule_all (expand_pair_let vyper_lowering_logs_correct)
  \\ disch_then (qspecl_then [`event_info`, `ext_fns`, `int_fns`, `fb_fn`,
       `dispatch`, `bucket_count`, `fn_meta_bytes`, `dense_buckets`,
       `entry_info`, `entry_label`] strip_assume_tac)
  (* Step 2: Apply codegen well-formedness *)
  \\ drule (expand_pair_let compile_vyper_raw_well_formed)
  \\ strip_tac
  (* Abbreviate ctx for readability *)
  \\ qmatch_asmsub_abbrev_tac `ctx_pass_correct pipeline _ _ ctx vs`
  (* Extract codegen from compile_vyper_raw *)
  \\ `codegen (pipeline ctx) fn_eom_map
       (SND (run_lowering selectors ext_fns int_fns fb_fn dispatch bucket_count
              fn_meta_bytes dense_buckets entry_info entry_label))
     = SOME bytecode` by (
      gvs[compile_vyper_raw_def, pairTheory.UNCURRY, Abbr `ctx`] >>
      CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> gvs[])
  (* Step 3: Unfold correspondence, case split on Vyper result *)
  \\ simp[vyper_evm_correspondence_def]
  \\ Cases_on `call_external am tx`
  \\ rename1 `call_external am tx = (vyp_res, am')`
  \\ Cases_on `vyp_res` \\ gvs[external_call_result_rel_def]
  >- ((* INL: success case *)
   Cases_on `run_context fuel ctx vs`
   \\ gvs[external_call_result_rel_def]
   (* Now: Halt ss', with returndata/accounts/transient from ss' *)
   \\ `terminates (run_context fuel ctx vs)` by simp[terminates_def]
   \\ drule_all e2e_venom_pipeline \\ strip_tac
   \\ Cases_on `run_context fuel' (pipeline ctx) vs`
   \\ gvs[observable_result_equiv_def]
   (* Now: Halt ss2' with observable_equiv ss' ss2' *)
   \\ drule_all (SRULE [] e2e_venom_to_evm)
   \\ disch_then $ qspecl_then [`vs`, `fuel'`] strip_assume_tac
   \\ qexists `gas_needed` \\ rpt strip_tac
   \\ first_x_assum (qspec_then `es` mp_tac)
   \\ simp[pairTheory.UNCURRY]
   \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
   \\ gvs[] \\ strip_tac
   (* Now: run es = SOME (INR NONE, es'), final_state_rel ss2' es' *)
   \\ qexists `es'` \\ rpt conj_tac
   >- simp[]
   >- ((* return_data_encodes *)
     simp[return_data_encodes_def]
     \\ gvs[final_state_rel_def, observable_equiv_def]
     \\ Cases_on `es'.contexts` \\ gvs[]
     \\ PairCases_on `h` \\ gvs[]
     \\ qexists `abi_val` \\ simp[])
   \\ (* state_effects_match *)
   simp[state_effects_match_def]
   \\ gvs[final_state_rel_def, observable_equiv_def]
   \\ Cases_on `es'.contexts` \\ gvs[]
   \\ PairCases_on `h` \\ gvs[])
  (* INR: exception cases *)
  \\ rename1 `call_external am tx = (INR exc, am')`
  \\ Cases_on `exc` \\ gvs[external_call_result_rel_def]
  \\ TRY (Cases_on `run_context fuel ctx vs` >>
          gvs[external_call_result_rel_def] >> NO_TAC)
  (* AssertException => Revert *)
  \\ Cases_on `run_context fuel ctx vs`
  \\ gvs[external_call_result_rel_def]
  \\ Cases_on `a` \\ gvs[external_call_result_rel_def]
  \\ `terminates (run_context fuel ctx vs)` by simp[terminates_def]
  \\ drule_all e2e_venom_pipeline \\ strip_tac
  \\ Cases_on `run_context fuel' (pipeline ctx) vs`
  \\ gvs[observable_result_equiv_def]
  \\ drule_all (SRULE [] e2e_venom_to_evm)
  \\ disch_then $ qspecl_then [`vs`, `fuel'`] strip_assume_tac
  \\ qexists `gas_needed` \\ rpt strip_tac
  \\ first_x_assum (qspec_then `es` mp_tac)
  \\ simp[pairTheory.UNCURRY]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ gvs[] \\ strip_tac
  \\ qexists `es'` \\ conj_tac >- simp[]
  \\ irule evm_revert_state_unchanged \\ simp[]
QED

(* ===== Concrete Pipeline Instances ===== *)

(* The O2 pipeline preserves observable semantics.
   Combines individual O2 pass correctness theorems into
   a single ctx_pass_correct statement. Analysis functions
   (make_ssa, ircf, ricf, dse, amap, live_at) are parameters. *)
Theorem o2_pipeline_ctx_pass_correct[local]:
  !ircf_global ricf_global threshold
    make_ssa ircf ricf dse_analysis amap live_at ctx vs.
    ctx_pass_correct
      (venom_pipeline ircf_global ricf_global threshold
        (o2_fn_passes make_ssa ircf ricf dse_analysis amap live_at))
      observable_equiv observable_equiv ctx vs
Proof
  cheat
QED

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
  rpt gen_tac
  \\ simp[pairTheory.UNCURRY]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ strip_tac
  \\ qsuff_tac `?gas_needed. !es.
       initial_evm_rel bytecode vs es /\ ~NULL es.contexts /\
       (FST (HD es.contexts)).msgParams.gasLimit >= gas_needed ==>
       vyper_evm_correspondence tenv event_info ret am tx es`
  >- simp[]
  \\ drule (expand_pair_let e2e_vyper_to_evm |> SRULE [])
  \\ disch_then (qspecl_then [`tenv`, `event_info`,
       `observable_equiv`, `observable_equiv`,
       `am`, `tx`, `vs`, `args`, `ret`] mp_tac)
  \\ simp[o2_pipeline_ctx_pass_correct]
QED

(* ===== Deploy Phase ===== *)

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
