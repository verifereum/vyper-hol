(*
 * End-to-End Vyper-to-EVM Correctness
 *
 * Composes three legs:
 *   1. vyper_to_venom_correct: call_external ~ run_context
 *   2. venom_pipeline_correct: run_context ~ run_context o pipeline
 *   3. codegen_correct: run_context ~ EVM run
 *
 * TOP-LEVEL:
 *   return_data_encodes    -- Vyper return value ~ EVM returndata
 *   log_entry_corresponds  -- single Vyper log ~ EVM event
 *   logs_correspond        -- Vyper logs ~ EVM events (LIST_REL)
 *   state_effects_match    -- Vyper side effects ~ EVM post-state
 *   state_unchanged        -- rollback state unchanged (for reverts)
 *   initial_evm_rel        -- EVM state initialized with bytecode
 *   valid_function_call    -- source function callable with given args
 *   compile_vyper          -- full compilation chain
 *   compile_vyper_well_formed -- compilation => codegen preconditions
 *   e2e_vyper_to_evm       -- Vyper source semantics ~ EVM execution
 *)

Theory e2eCorrectness
Ancestors
  vyperLoweringCorrect vfmExecution
  venomPipelineCorrect
  passSimulationDefs
  codegenCorrectness
  stateEquivProps
  venomExecSemantics
  vyperABI
  compileEnv
  venomInst

(* ===== E2E Result Predicates ===== *)

(* EVM returndata equals ABI encoding of Vyper return value.
   Bridges Vyper values to EVM bytes via the ABI encoding scheme. *)
Definition return_data_encodes_def:
  return_data_encodes tenv ret_type v es' <=>
    ?abi_val ctxt rb rest.
      es'.contexts = (ctxt, rb) :: rest /\
      vyper_to_abi tenv ret_type v = SOME abi_val /\
      ctxt.returnData =
        enc (vyper_to_abi_type tenv ret_type) abi_val
End

(* ===== Log Correspondence ===== *)

(* Extract non-indexed values from args based on flags
   (complement of indexed_values from compileEnvTheory). *)
Definition non_indexed_values_def:
  non_indexed_values [] [] = ([] : value list) /\
  non_indexed_values (T :: flags) (_ :: vals) =
    non_indexed_values flags vals /\
  non_indexed_values (F :: flags) (v :: vals) =
    v :: non_indexed_values flags vals /\
  non_indexed_values _ _ = []
End

(* Extract non-indexed types from arg types based on flags. *)
Definition non_indexed_types_def:
  non_indexed_types [] [] = ([] : type list) /\
  non_indexed_types (T :: flags) (_ :: ts) =
    non_indexed_types flags ts /\
  non_indexed_types (F :: flags) (t :: ts) =
    t :: non_indexed_types flags ts /\
  non_indexed_types _ _ = []
End

(* Single log entry correspondence. Relates a Vyper log (nsid, values)
   to an EVM event, given:
   - event_info: maps event name to (hash, indexed_flags, arg_types)
     (from EventDecl with indexed annotations, PR #252)
   - tenv: type environment for ABI encoding
   - addr: contract address (logger)

   EVM event structure:
   - ev.logger = contract address
   - ev.topics = [event_hash; val_to_w256(idx_val_1); ...]
   - ev.data = ABI-encode of non-indexed values as tuple

   Indexed args: each encoded as bytes32 via val_to_w256
   (sufficient for fixed-size types; dynamic types would need
   keccak256 -- deferred until dynamic indexed args are supported).
   Non-indexed args: ABI-encoded together as a tuple. *)
Definition log_entry_corresponds_def:
  log_entry_corresponds event_info tenv (addr : address)
    ((eid, vals) : log) (ev : event) <=>
    let event_name = nsid_to_string eid in
    case event_info event_name of
      NONE => F
    | SOME (event_hash, arg_types, indexed_flags) =>
        let idx_vals = indexed_values indexed_flags vals in
        let nidx_vals = non_indexed_values indexed_flags vals in
        let nidx_types = non_indexed_types indexed_flags arg_types in
          LENGTH indexed_flags = LENGTH vals /\
          LENGTH arg_types = LENGTH vals /\
          ev.logger = addr /\
          (* Topics: event selector hash + indexed values as bytes32 *)
          ev.topics = n2w event_hash :: MAP val_to_w256 idx_vals /\
          (* Data: ABI-encoded non-indexed values as tuple *)
          (?abi_vals.
             vyper_to_abi_list tenv nidx_types nidx_vals = SOME abi_vals /\
             ev.data = enc (Tuple (vyper_to_abi_types tenv nidx_types))
                           (ListV abi_vals))
End

(* Vyper logs correspond to EVM events (ordered, same-length).
   event_info maps event name -> SOME (hash, arg_types, indexed_flags)
   for declared events (from EventDecl with indexed flag). *)
Definition logs_correspond_def:
  logs_correspond event_info tenv (addr : address)
    (vyper_logs : log list) (evm_logs : event list) <=>
    LIST_REL (log_entry_corresponds event_info tenv addr)
      vyper_logs evm_logs
End

(* EVM post-state matches Vyper side effects:
   accounts, transient storage, and logs all correspond. *)
Definition state_effects_match_def:
  state_effects_match event_info (addr : address) tenv
    (am' : abstract_machine) es' <=>
    ?ctxt rb rest.
      es'.contexts = (ctxt, rb) :: rest /\
      rb.accounts = am'.accounts /\
      rb.tStorage = am'.tStorage /\
      logs_correspond event_info tenv addr am'.logs ctxt.logs
End

(* Rollback state unchanged: accounts and transient storage
   are the same before and after execution (used for reverts). *)
Definition state_unchanged_def:
  state_unchanged es es' <=>
    ~NULL es.contexts /\ ~NULL es'.contexts /\
    (let (ctxt, rb) = HD es.contexts in
     let (ctxt', rb') = HD es'.contexts in
       rb'.accounts = rb.accounts /\
       rb'.tStorage = rb.tStorage)
End

(* Full Vyper-EVM correspondence for a single external call.
   Packages the case split on call_external result:
   - Success: EVM halts, returndata + state effects match
   - Assert/revert: EVM reverts, rollback state unchanged
   - Error: T (could be F under well-formedness)
   - Break/Continue/Return: F (never escape call_external) *)
Definition vyper_evm_correspondence_def:
  vyper_evm_correspondence tenv event_info ret am tx es <=>
    (case call_external am tx of
       (INL v, am') =>
         ?es'.
           run es = SOME (INR NONE, es') /\
           return_data_encodes tenv ret v es' /\
           state_effects_match event_info tx.target tenv am' es'
     | (INR (AssertException _), _) =>
         ?es'. run es = SOME (INR (SOME Reverted), es') /\
               state_unchanged es es'
     | (INR (Error _), _) => T
     | (INR BreakException, _) => F
     | (INR ContinueException, _) => F
     | (INR (ReturnException _), _) => F)
End

(* ===== EVM State Predicates ===== *)

(* EVM execution state corresponds to initial Venom state,
   with compiled bytecode loaded. Combines the initial state
   correspondence (shared environment, memory, empty stack)
   with the bytecode loading condition.
   Calldata: EVM msgParams.data = Venom cc_calldata (selector+ABI args). *)
Definition initial_evm_rel_def:
  initial_evm_rel bytecode vs es <=>
    ~NULL es.contexts /\
    let (ctxt, rb) = HD es.contexts in
      rb.accounts = vs.vs_accounts /\
      rb.tStorage = vs.vs_transient /\
      ctxt.returnData = vs.vs_returndata /\
      ctxt.logs = vs.vs_logs /\
      ctxt.stack = [] /\
      (!i. read_byte i vs.vs_memory = read_byte i ctxt.memory) /\
      ctxt.msgParams.data = vs.vs_call_ctx.cc_calldata /\
      ctxt.pc = 0 /\
      ctxt.msgParams.code = bytecode /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
End

(* ===== Source Predicates ===== *)

(* Valid function call: source function exists in the abstract machine,
   calldata correctly ABI-encodes the arguments, and the selector
   table routes to the right function.

   Calldata is constrained via the tx (source args) and the EVM
   calldata bytes (in initial_evm_rel). The relation between
   tx.args and the ABI-encoded calldata is:
     calldata_encodes tenv name arg_types tx.args calldata_bytes

   No vs parameter needed -- calldata_encodes takes the byte list
   directly, and initial_evm_rel ensures EVM and Venom agree. *)
Definition valid_function_call_def:
  valid_function_call tenv am tx selectors calldata args ret <=>
    (?mut nr dflts body.
       lookup_exported_function
         (initial_evaluation_context am.sources am.layouts tx) am
         tx.function_name = SOME (mut, nr, args, dflts, ret, body)) /\
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      calldata /\
    (?sel fn_lbl htz.
       MEM (sel, fn_lbl, htz) selectors /\
       selector_matches sel tx.function_name
         (vyper_to_abi_types tenv (MAP SND args)))
End

(* ===== Full Compilation ===== *)

(* Full compilation: lowering + pass pipeline + codegen.
   Pipeline is a parameter -- instantiate for O2, O3, Os, etc. *)
Definition compile_vyper_def:
  compile_vyper selectors ext_fns int_fns fb_fn
                dispatch bucket_count fn_meta_bytes entry_label
                (pipeline : venom_context -> venom_context)
                fn_eom_map data_seg =
    let ctx = run_lowering selectors ext_fns int_fns fb_fn
                dispatch bucket_count fn_meta_bytes entry_label in
    let ctx' = pipeline ctx in
    codegen ctx' fn_eom_map data_seg
End

(* ===== Component Theorems ===== *)

(* Pipeline preserves Venom semantics.
   Follows from ctx_pass_correct -> pass_correct -> lift_result.
   lift_result preserves all observable state including returndata,
   accounts, transient, and logs (via execution_equiv). *)
Theorem e2e_venom_pipeline:
  !ctx pipeline fresh vs.
    ctx_pass_correct pipeline (state_equiv fresh) (execution_equiv fresh)
      ctx vs
    ==>
    !fuel. ?fuel'.
      result_equiv fresh
        (run_context fuel ctx vs)
        (run_context fuel' (pipeline ctx) vs)
Proof
  cheat
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
Theorem compile_vyper_well_formed:
  !selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes entry_label
    pipeline fn_eom_map data_seg bytecode fresh vs.
  let ctx = run_lowering selectors ext_fns int_fns fb_fn
              dispatch bucket_count fn_meta_bytes entry_label in
  let ctx' = pipeline ctx in
    compile_vyper selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
    ctx_pass_correct pipeline (state_equiv fresh) (execution_equiv fresh)
      ctx vs
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
   See e2e_vyper_to_evm_O2 for a concrete instance. *)
Theorem e2e_vyper_to_evm:
  !tenv event_info pipeline selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes entry_label
    fn_eom_map data_seg bytecode
    am tx vs fresh args ret.
  let ctx = run_lowering selectors ext_fns int_fns fb_fn
              dispatch bucket_count fn_meta_bytes entry_label in
    (* Compilation produces bytecode *)
    compile_vyper selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
    (* Source function exists, calldata valid, selector routes *)
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0 /\
    (* Pipeline preserves semantics (proved per-pipeline by
       composing individual pass correctness theorems) *)
    ctx_pass_correct pipeline (state_equiv fresh) (execution_equiv fresh)
      ctx vs
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
    dispatch bucket_count fn_meta_bytes entry_label
    ircf_global ricf_global threshold
    make_ssa ircf ricf dse_analysis amap live_at
    fn_eom_map data_seg bytecode
    am tx vs args ret.
  let pipeline = venom_pipeline ircf_global ricf_global threshold
        (o2_fn_passes make_ssa ircf ricf dse_analysis amap live_at) in
    compile_vyper selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
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
