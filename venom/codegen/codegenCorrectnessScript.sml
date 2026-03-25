(*
 * Codegen End-to-End Correctness — Theorem Statement
 *
 * Composes venomToAsm and asmToBytecode to state: if Venom IR
 * execution of a function halts/reverts, then EVM execution of the
 * codegen output (byte list) produces a corresponding result.
 *
 * This is the top-level theorem for the codegen pass.
 * Stated modulo gas.
 *
 * TOP-LEVEL:
 *   codegen_fn_correct — per-function codegen correctness
 *)

Theory codegenCorrectness
Ancestors
  asmToBytecodeProps venomToAsmProps codegen

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
         (* Environment must match *)
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
     - sufficient gas on EVM side
     - spill safety: Venom execution doesn't clobber spill region
     - spill coverage: initial memory covers spill high-water mark

   Gas: sufficient_gas es is necessary but not sufficient. The full
   proof requires gas for all steps. Exact formulation refined at
   proof time.

   Spill safety: step_mem_safe for every Venom step. This is a
   property of the INPUT PROGRAM — the codegen can't establish it.
   For Vyper-generated code, the memory allocator ensures fn_eom is
   above all user allocations. For other frontends, must be assumed.

   Note: this theorem covers a single function. Multi-function
   contexts compose via the dispatch mechanism (selector table). *)
Theorem codegen_fn_correct:
  ∀fuel ctx fn fn_eom data_seg bytecode spill_hwm vs es.
    codegen_ready_fn fn ∧
    codegen (ctx with ctx_functions := [fn])
            (FEMPTY |+ (fn.fn_name, fn_eom))
            data_seg = SOME bytecode ∧
    initial_state_rel fn vs es ∧
    sufficient_gas es ∧
    (* Spill safety: Venom execution doesn't clobber [fn_eom, spill_hwm) *)
    (∀inst vs1 vs2 fuel'.
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe <| sa_fn_eom := fn_eom;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) ∧
    (* MSIZE: initial memory covers spill high-water mark *)
    spill_mem_covered spill_hwm vs.vs_memory ∧
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.msgParams.code = bytecode ∧
         ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
     | [] => F) ⇒
    (* Halt: Venom halts ⇒ EVM halts with matching state *)
    (∀vs'. run_function fuel ctx fn vs = Halt vs' ⇒
       ∃es'. run es = SOME (INR NONE, es') ∧
             final_state_rel vs' es') ∧
    (* Revert: Venom reverts ⇒ EVM reverts with matching state *)
    (∀vs'. run_function fuel ctx fn vs = Abort Revert_abort vs' ⇒
       ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
             final_state_rel vs' es') ∧
    (* Exceptional halt: Venom aborts ⇒ EVM faults *)
    (∀vs'. run_function fuel ctx fn vs = Abort ExHalt_abort vs' ⇒
       ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                 exc ≠ Reverted ∧
                 final_state_rel vs' es')
Proof
  cheat
QED
