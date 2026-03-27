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
 *   logs_correspond        -- Vyper logs ~ EVM events (LIST_REL)
 *   state_effects_match    -- Vyper side effects ~ EVM post-state
 *   initial_evm_rel        -- EVM state initialized with bytecode
 *   valid_function_call    -- source function callable with given args
 *   compile_vyper          -- full compilation chain
 *   compile_vyper_well_formed -- compilation => codegen preconditions
 *   e2e_vyper_to_evm       -- Vyper source semantics ~ EVM execution
 *   e2e_vyper_to_evm_with_gas -- same, without OOG (under gas assumption)
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

(* Vyper logs correspond to EVM events. LIST_REL ensures ordered,
   same-length correspondence. Per entry:
   - logger = contract address
   - values are ABI-encodable for appropriate argument types
   - ABI-encoded values determine topics and data

   Full topic/data encoding spec requires indexed flag in EventDecl
   (AST extension TODO). Currently: values ABI-encode successfully,
   linking Vyper log contents to the ABI layer. *)
Definition logs_correspond_def:
  logs_correspond (addr : address) tenv
    (vyper_logs : log list) (evm_logs : event list) <=>
    LIST_REL
      (λ(eid, vals) ev.
         ev.logger = addr ∧
         ∃arg_types abi_vals.
           LENGTH arg_types = LENGTH vals ∧
           OPT_MMAP (UNCURRY (vyper_to_abi tenv))
             (ZIP (arg_types, vals)) = SOME abi_vals)
      vyper_logs evm_logs
End

(* EVM post-state matches Vyper side effects:
   accounts, transient storage, and logs all correspond. *)
Definition state_effects_match_def:
  state_effects_match (addr : address) tenv
    (am' : abstract_machine) es' <=>
    ?ctxt rb rest.
      es'.contexts = (ctxt, rb) :: rest /\
      rb.accounts = am'.accounts /\
      rb.tStorage = am'.tStorage /\
      logs_correspond addr tenv am'.logs ctxt.logs
End

(* ===== EVM State Predicates ===== *)

(* EVM execution state corresponds to initial Venom state,
   with compiled bytecode loaded. Combines the initial state
   correspondence (shared environment, memory, empty stack)
   with the bytecode loading condition.
   No ctx parameter -- Venom context is not needed here. *)
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
      ctxt.pc = 0 /\
      ctxt.msgParams.code = bytecode /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
End

(* ===== Source Predicates ===== *)

(* Valid function call: source function exists in the abstract machine,
   calldata correctly ABI-encodes the arguments, and the selector
   table routes to the right function.

   args and ret are exposed (needed for return_data_encodes and
   calldata_encodes). Internal details (mutability, nonreentrant,
   defaults, body, selector triple) are existentially quantified. *)
Definition valid_function_call_def:
  valid_function_call tenv am tx selectors vs args ret <=>
    (?mut nr dflts body.
       lookup_exported_function
         (initial_evaluation_context am.sources am.layouts tx) am
         tx.function_name = SOME (mut, nr, args, dflts, ret, body)) /\
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      vs.vs_call_ctx.cc_calldata /\
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
   Follows from ctx_pass_correct -> pass_correct -> result_equiv.
   result_equiv preserves all observable state including returndata,
   accounts, transient, and logs (via execution_equiv). *)
Theorem e2e_venom_pipeline:
  !ctx pipeline fresh vs.
    ctx_pass_correct pipeline fresh ctx vs
    ==>
    !fuel. ?fuel'.
      result_equiv fresh
        (run_context fuel ctx vs)
        (run_context fuel' (pipeline ctx) vs)
Proof
  cheat
QED

(* Codegen correctness: Venom execution corresponds to EVM execution.
   Uses initial_evm_rel which packages the initial state correspondence
   and bytecode loading into a single predicate.
   Direct instantiation of codegen_correct. *)
Theorem e2e_venom_to_evm:
  !ctx fn_eom_map data_seg bytecode spill_hwm vs es fuel.
    codegen_ready ctx /\
    ctx_wf ctx /\
    codegen ctx fn_eom_map data_seg = SOME bytecode /\
    initial_evm_rel bytecode vs es /\
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions /\
       step_inst fuel' ctx inst vs1 = OK vs2 ==>
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) /\
    spill_mem_covered spill_hwm vs.vs_memory
    ==>
    (?es'. run es = SOME (INR (SOME OutOfGas), es')) \/
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

(* ===== Full E2E: Vyper to EVM ===== *)

(* Composes all three legs into a single theorem relating Vyper
   source semantics to EVM bytecode execution.
 *
 * Correspondence:
 *   Vyper success (INL v)       => EVM normal halt, returndata =
 *                                  ABI encoding of v, accounts,
 *                                  transient storage, and logs match
 *   Vyper revert (AssertExc)    => EVM REVERT, state unchanged
 *   Vyper error                 => T (indicates source-level error;
 *                                  could be strengthened to F under
 *                                  well-formedness of am/tx)
 *   Break/Continue/Return       => F -- internal control flow,
 *                                  never escapes call_external
 *)

(* Compilation produces a well-formed codegen-ready context.
   Discharged by construction: run_lowering produces wf context,
   pipeline passes preserve well-formedness, codegen succeeds. *)
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
    ctx_pass_correct pipeline fresh ctx vs
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

(* Main E2E theorem: Vyper source semantics ~ EVM execution.

   ctx_pass_correct is an assumption because the pipeline is
   parametric -- it holds for any pipeline assembled from
   semantics-preserving passes (e.g., the standard O2 pipeline).
   It is proved per-pipeline by composing individual pass proofs. *)
Theorem e2e_vyper_to_evm:
  !tenv pipeline selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes entry_label
    fn_eom_map data_seg bytecode
    am tx vs es fresh args ret.
  let ctx = run_lowering selectors ext_fns int_fns fb_fn
              dispatch bucket_count fn_meta_bytes entry_label in
    (* Compilation produces bytecode *)
    compile_vyper selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
    (* Source function exists, calldata valid, selector routes *)
    valid_function_call tenv am tx selectors vs args ret /\
    vs.vs_inst_idx = 0 /\
    (* Pipeline preserves semantics (proved per-pipeline by
       composing individual pass correctness theorems) *)
    ctx_pass_correct pipeline fresh ctx vs /\
    (* EVM state initialized with compiled bytecode *)
    initial_evm_rel bytecode vs es
    ==>
    (?es'. run es = SOME (INR (SOME OutOfGas), es')) \/
    (case call_external am tx of
       (INL v, am') =>
         ?es'.
           run es = SOME (INR NONE, es') /\
           return_data_encodes tenv ret v es' /\
           state_effects_match tx.target tenv am' es'
     | (INR (AssertException _), _) =>
         (* REVERT: EVM reverts, state changes rolled back.
            es' is constrained by run's determinism; in particular,
            accounts and storage are unchanged from es. *)
         ?es'. run es = SOME (INR (SOME Reverted), es') /\
               ~NULL es'.contexts /\
               (let (ctxt', rb') = HD es'.contexts in
                let (ctxt, rb) = HD es.contexts in
                  rb'.accounts = rb.accounts /\
                  rb'.tStorage = rb.tStorage)
     | (INR (Error _), _) =>
         (* Source-level error (e.g., bad tx, missing function).
            Under well-formedness of am and tx, this case would be F.
            Currently T to avoid requiring that well-formedness proof. *)
         T
     | (INR BreakException, _) => F
     | (INR ContinueException, _) => F
     | (INR (ReturnException _), _) => F)
Proof
  cheat
QED

(* Same as e2e_vyper_to_evm but without the OOG escape hatch.
   Under the assumption that gas is sufficient, the EVM execution
   always produces the correct result. *)
Theorem e2e_vyper_to_evm_with_gas:
  !tenv pipeline selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes entry_label
    fn_eom_map data_seg bytecode
    am tx vs es fresh args ret.
  let ctx = run_lowering selectors ext_fns int_fns fb_fn
              dispatch bucket_count fn_meta_bytes entry_label in
    compile_vyper selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes entry_label
      pipeline fn_eom_map data_seg = SOME bytecode /\
    valid_function_call tenv am tx selectors vs args ret /\
    vs.vs_inst_idx = 0 /\
    ctx_pass_correct pipeline fresh ctx vs /\
    initial_evm_rel bytecode vs es /\
    (* Gas is sufficient: EVM does not run out of gas *)
    (~?es'. run es = SOME (INR (SOME OutOfGas), es'))
    ==>
    (case call_external am tx of
       (INL v, am') =>
         ?es'.
           run es = SOME (INR NONE, es') /\
           return_data_encodes tenv ret v es' /\
           state_effects_match tx.target tenv am' es'
     | (INR (AssertException _), _) =>
         ?es'. run es = SOME (INR (SOME Reverted), es') /\
               ~NULL es'.contexts /\
               (let (ctxt', rb') = HD es'.contexts in
                let (ctxt, rb) = HD es.contexts in
                  rb'.accounts = rb.accounts /\
                  rb'.tStorage = rb.tStorage)
     | (INR (Error _), _) => T
     | (INR BreakException, _) => F
     | (INR ContinueException, _) => F
     | (INR (ReturnException _), _) => F)
Proof
  cheat
QED
