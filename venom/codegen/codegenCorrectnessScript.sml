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
   EVM stack holds function arguments matching PARAM instructions,
   memory below fn_eom is shared. *)
Definition initial_state_rel_def:
  initial_state_rel fn fn_eom vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         (* Environment must match *)
         rb.accounts = vs.vs_accounts ∧
         rb.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         (* Memory below fn_eom is shared *)
         (∀i. i < fn_eom ⇒
            read_byte i vs.vs_memory = read_byte i ctxt.memory) ∧
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
     - initial states correspond
     - sufficient gas on EVM side (abstracted as run terminating)

   Note: this theorem covers a single function. Multi-function
   contexts compose via the dispatch mechanism (selector table). *)
Theorem codegen_fn_correct:
  ∀fuel ctx fn fn_eom data_seg bytecode vs es.
    codegen_ready_fn fn ∧
    codegen (ctx with ctx_functions := [fn])
            (FEMPTY |+ (fn.fn_name, fn_eom))
            data_seg = SOME bytecode ∧
    initial_state_rel fn fn_eom vs es ∧
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
