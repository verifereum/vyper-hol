(*
 * Codegen End-to-End Correctness — Theorem Statements
 *
 * Composes venomToAsm and asmToBytecode to state: if Venom IR
 * execution halts/reverts, then EVM execution of the codegen output
 * (byte list) produces a corresponding result.
 *
 * TOP-LEVEL:
 *   codegen_correct    — whole-context correctness (run_context vs run)
 *   codegen_fn_correct — per-function correctness (run_blocks vs run)
 *
 * EVM Exception Classification
 * ============================
 * How each EVM exception is handled in the correctness argument:
 *
 * OutOfGas — undischargeable in general. Requires gas_sufficient
 *   hypothesis at the top-level entry point (call_vyper_contract).
 *   Only exception that needs an explicit disjunct in theorem statements.
 *
 * StackOverflow — discharged by asm_stack_bounded precondition.
 *   The compiler should reject programs where the stack model exceeds
 *   1024. NOTE: if this fires, the proper fix is depth-aware spilling
 *   (spill to memory when stack depth approaches limit), but that is
 *   an algorithmic change to the codegen, not yet implemented.
 *
 * StackUnderflow — discharged by construction (codegen stack model
 *   tracks height; well-formed plans never underflow).
 *
 * InvalidJumpDest — discharged by construction (label_offset_consistent,
 *   assemble_parse_correct ensure all jump targets are valid JUMPDESTs).
 *
 * Reverted — handled explicitly (separate case in theorem conclusion).
 *
 * WriteInStaticContext — when the call context is static, writes
 *   (SSTORE, LOG, CREATE, SELFDESTRUCT) are demoted to nops. This is
 *   defined as an allowed optimization: the Venom semantics can
 *   execute the write, but the EVM silently fails. The correctness
 *   theorem treats this as an exception disjunct (subsumed by SOME exc).
 *   TODO: formalize static-context demotion as a separate pass/property.
 *
 * OutOfBoundsRead — RETURNDATACOPY past returndata length. Should be
 *   discharged by construction: Venom ExHalt maps to this. The proof
 *   that Vyper lowering never generates OOB reads is a separate
 *   lowering correctness obligation. NOTE: if future Vyper versions
 *   expose raw returndata access to users, this may require a runtime
 *   bounds check instead.
 *
 * AddressCollision — CREATE-specific. Handled by a separate entry
 *   point (create_vyper_contract) that includes the collision check.
 *   TODO: define create_vyper_contract alongside call_vyper_contract.
 *
 * InvalidContractPrefix — CREATE code starts with 0xEF. Similar to
 *   AddressCollision: handled via create_vyper_contract.
 *
 * InvalidParameter, KZGProofError — precompile-internal failures.
 *   Contained within the CALL frame (returns 0 on stack). Never
 *   propagates to the calling contract's execution.
 *)

Theory codegenCorrectness
Ancestors
  asmToBytecodeProps venomToAsmProps codegen vfmExecution



(* ===== Initial State Correspondence ===== *)

(* At function entry: Venom state and EVM state agree on shared fields,
   EVM stack holds function arguments matching PARAM variables,
   all memory is shared (no spill slots allocated yet). *)
Definition initial_state_rel_def:
  initial_state_rel fn vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         (* Stack has function arguments matching PARAM variables.
            First param deepest, last param TOS. *)
         let params = get_params (HD fn.fn_blocks).bb_instructions in
         LENGTH params = LENGTH ctxt.stack ∧
         (∀i. i < LENGTH params ⇒
            FLOOKUP vs.vs_vars (HD (EL i params).inst_outputs) =
              SOME (EL i (REVERSE ctxt.stack))) ∧
         (* Environment must match.
            rb.accounts includes contract storage (per-account). *)
         rb.accounts = vs.vs_accounts ∧
         rb.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         (* Memory fully shared at function entry (no spills yet).
            read_byte zero-pads, so this handles different lengths. *)
         (∀i. read_byte i vs.vs_memory = read_byte i ctxt.memory) ∧
         (* EVM starts at pc = 0 *)
         ctxt.pc = 0
     | [] => F)
End

(* ===== Return Value Correspondence ===== *)

(* After execution: return data and side effects match. *)
Definition final_state_rel_def:
  final_state_rel vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         rb.accounts = vs.vs_accounts ∧
         rb.tStorage = vs.vs_transient
     | [] => F)
End

(* ===== Per-Function Codegen Correctness ===== *)

(* If codegen produces bytecode for a function, and the function
   halts/reverts in the Venom semantics, then EVM execution of
   the bytecode produces a corresponding result.

   Preconditions:
     - codegen_ready_fn: SSA, SUE, normalized CFG, valid opcodes
     - codegen succeeds (SOME bytecode)
     - initial states correspond (stack has args, shared state matches)
     - spill safety: Venom execution doesn't clobber spill region
     - spill coverage: initial memory covers spill high-water mark

   Gas: existential — there exists a gas bound such that with enough
   gas, EVM results correspond to Venom results. This proves the
   theorem is non-vacuous (the success case is always reachable).
   The gas bound depends on the Venom execution trace (each Venom
   step maps to finitely many EVM instructions with known gas costs).

   StackOverflow is excluded by asm_stack_bounded (codegen must
   produce stack-bounded asm). TODO: add explicit stack height check
   to codegen (return NONE if plan_max_height >= 1024).

   Spill safety: step_mem_safe for every Venom step. This is a
   property of the INPUT PROGRAM — the codegen can't establish it.
   For Vyper-generated code, the memory allocator ensures fn_eom is
   above all user allocations. For other frontends, must be assumed.

   Note: this theorem covers a single function. Multi-function
   contexts compose via the dispatch mechanism (selector table). *)
Theorem codegen_fn_correct:
  ∀fuel ctx fn fn_eom data_seg bytecode spill_hwm vs.
    codegen_ready_fn fn ∧
    codegen (ctx with ctx_functions := [fn])
            (FEMPTY |+ (fn.fn_name, fn_eom))
            data_seg = SOME bytecode ∧
    (∀inst vs1 vs2 fuel'.
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe <| sa_fn_eom := fn_eom;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) ∧
    spill_mem_covered spill_hwm vs.vs_memory ⇒
    ∃gas_needed.
      ∀es. initial_state_rel fn vs es ∧
           (case es.contexts of
              (ctxt, rb) :: _ =>
                ctxt.msgParams.gasLimit ≥ gas_needed ∧
                ctxt.msgParams.code = bytecode ∧
                ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
            | [] => F) ⇒
        (case run_blocks fuel ctx fn vs of
           Halt vs' =>
             ∃es'. run es = SOME (INR NONE, es') ∧
                   final_state_rel vs' es'
         | Abort Revert_abort vs' =>
             ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
                   final_state_rel vs' es'
         | Abort ExHalt_abort vs' =>
             ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                       exc ≠ Reverted ∧
                       final_state_rel vs' es'
         | OK _ => F
         | IntRet _ _ => T
         | Error _ => T)
Proof
  cheat
QED

(* ===== Whole-Context Codegen Correctness ===== *)

(* Initial state correspondence at context entry: Venom initial state
   and EVM execution state agree on environment, memory, calldata, etc.
   No function params on the EVM stack (entry starts with empty stack). *)
Definition initial_ctx_rel_def:
  initial_ctx_rel ctx vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         rb.accounts = vs.vs_accounts ∧
         rb.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         ctxt.stack = [] ∧
         (∀i. read_byte i vs.vs_memory = read_byte i ctxt.memory) ∧
         ctxt.pc = 0
     | [] => F)
End

(* Top-level codegen correctness: if a well-formed Venom context is
   compiled to bytecode, and run_context halts/reverts, then EVM
   execution of the bytecode produces a corresponding result.

   This composes codegen_fn_correct with run_context's dispatch to
   the entry function. *)
Theorem codegen_correct:
  ∀fuel ctx fn_eom_map data_seg bytecode spill_hwm vs.
    codegen_ready ctx ∧
    ctx_wf ctx ∧
    codegen ctx fn_eom_map data_seg = SOME bytecode ∧
    (∀fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions ∧
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) ∧
    spill_mem_covered spill_hwm vs.vs_memory ⇒
    ∃gas_needed.
      ∀es. initial_ctx_rel ctx vs es ∧
           (case es.contexts of
              (ctxt, rb) :: _ =>
                ctxt.msgParams.gasLimit ≥ gas_needed ∧
                ctxt.msgParams.code = bytecode ∧
                ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
            | [] => F) ⇒
        (case run_context fuel ctx vs of
           Halt vs' =>
             ∃es'. run es = SOME (INR NONE, es') ∧
                   final_state_rel vs' es'
         | Abort Revert_abort vs' =>
             ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
                   final_state_rel vs' es'
         | Abort ExHalt_abort vs' =>
             ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                       exc ≠ Reverted ∧
                       final_state_rel vs' es'
         | OK _ => F
         | IntRet _ _ => F
         | Error _ => T)
Proof
  cheat
QED
