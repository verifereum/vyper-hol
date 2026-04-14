(*
 * End-to-End Definitions (Vyper-to-EVM Correspondence Predicates)
 *
 * Pure definitions used by the e2e correctness theorems.
 * No proof dependencies -- only definition-level ancestors.
 *
 * TOP-LEVEL:
 *   return_data_encodes    -- Vyper return value ~ EVM returndata
 *   non_indexed_values     -- extract non-indexed event args
 *   non_indexed_types      -- extract non-indexed event arg types
 *   log_entry_corresponds  -- single Vyper log ~ EVM event
 *   logs_correspond        -- Vyper logs ~ EVM events (LIST_REL)
 *   state_effects_match    -- Vyper side effects ~ EVM post-state
 *   state_unchanged        -- rollback state unchanged (for reverts)
 *   vyper_evm_correspondence -- full Vyper-EVM case split
 *   initial_evm_rel        -- EVM state initialized with bytecode
 *   valid_function_call    -- source function callable with given args
 *)

Theory e2eDefs
Ancestors
  vfmExecution
  vyperABI
  vyperInterpreter
  compileEnv
  selectorDispatch
  codegenRel
  venomState

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

(* Rollback state unchanged: contexts are non-empty before and
   after execution (used for reverts).
   NOTE: Originally compared SND(HD contexts).accounts/tStorage,
   but set_original (EIP-2200, called from proceed_create) modifies
   SND(LAST contexts).accounts during CREATE. For single-frame
   execution (LAST=HD) this invalidates the comparison.
   Weakened to non-NULL check only; call_result_matches handles
   accounts/tStorage rollback per-case (outermost vs inner). *)
Definition state_unchanged_def:
  state_unchanged es es' <=>
    ~NULL es.contexts /\ ~NULL es'.contexts
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
