(*
 * Codegen State Relations
 *
 * Defines the relations connecting Venom IR state, plan_state
 * (stack model abstraction), asm execution state, and EVM state.
 *
 * Three levels:
 *   1. plan_state_rel: plan_state accurately tracks the asm stack
 *   2. venom_asm_rel:  Venom variables ↔ asm stack (via plan_state)
 *   3. asm_evm_rel:    asm execution ↔ EVM bytecode execution
 *
 * TOP-LEVEL:
 *   plan_stack_rel    — ps_stack matches concrete stack
 *   plan_spill_rel    — ps_spilled matches memory contents
 *   venom_asm_rel     — full Venom ↔ asm state relation
 *   asm_evm_rel       — asm ↔ EVM bytecode state relation
 *   asm_pc_to_offset  — asm index → byte offset
 *)

Theory codegenRel
Ancestors
  asmSem stackPlanGen

(* ===== Operand Evaluation in Venom State ===== *)

(* Evaluate an operand to bytes32, given venom vars and label offsets.
   Labels resolve to byte offsets from assembly. *)
Definition operand_val_def:
  operand_val vs label_offsets (Var v) = FLOOKUP vs.vs_vars v ∧
  operand_val vs label_offsets (Lit w) = SOME w ∧
  operand_val vs label_offsets (Label l) =
    OPTION_MAP n2w (FLOOKUP label_offsets l)
End

(* ===== Plan State ↔ Concrete Stack ===== *)

(* ps_stack (LAST=TOS) matches asm stack (HD=TOS).
   Each operand in ps_stack evaluates to the corresponding stack entry. *)
Definition plan_stack_rel_def:
  plan_stack_rel label_offsets vs ps_stack asm_stack ⇔
    LENGTH ps_stack = LENGTH asm_stack ∧
    ∀i. i < LENGTH ps_stack ⇒
      let op = EL i (REVERSE ps_stack) in
      let val = EL i asm_stack in
      operand_val vs label_offsets op = SOME val
End

(* Each spilled operand's value is stored at its memory offset.
   Spill slots hold 32-byte big-endian values. *)
Definition plan_spill_rel_def:
  plan_spill_rel label_offsets vs ps_spilled asm_memory ⇔
    ∀op off.
      FLOOKUP ps_spilled op = SOME off ⇒
      ∃v. operand_val vs label_offsets op = SOME v ∧
          word_of_bytes T (0w:bytes32)
            (read_bytes off 32 asm_memory) = v
End

(* ===== Venom State ↔ Asm State ===== *)

(* Read byte with implicit zero-padding (EVM memory is zero-initialized) *)
Definition read_byte_def:
  read_byte i (mem : byte list) =
    if i < LENGTH mem then EL i mem else (0w : byte)
End

(* Memory below fn_eom is shared between Venom and asm.
   Memory at/above fn_eom is the spill region (asm-only).
   Uses zero-padded reads: unallocated memory is implicitly zero. *)
Definition memory_rel_def:
  memory_rel fn_eom venom_mem asm_mem ⇔
    ∀i. i < fn_eom ⇒
      read_byte i venom_mem = read_byte i asm_mem
End

(* Full Venom ↔ asm state relation.
   Parameterized by:
     label_offsets — from compute_label_offsets on the assembled program
     fn_eom       — function end-of-memory (spill region starts here)
     ps           — plan_state tracking the stack abstraction *)
Definition venom_asm_rel_def:
  venom_asm_rel label_offsets fn_eom ps vs as ⇔
    plan_stack_rel label_offsets vs ps.ps_stack as.as_stack ∧
    plan_spill_rel label_offsets vs ps.ps_spilled as.as_memory ∧
    memory_rel fn_eom vs.vs_memory as.as_memory ∧
    (* Shared mutable state *)
    as.as_accounts = vs.vs_accounts ∧
    as.as_transient = vs.vs_transient ∧
    as.as_returndata = vs.vs_returndata ∧
    as.as_logs = vs.vs_logs ∧
    (* Shared environment *)
    as.as_call_ctx = vs.vs_call_ctx ∧
    as.as_tx_ctx = vs.vs_tx_ctx ∧
    as.as_block_ctx = vs.vs_block_ctx ∧
    as.as_code = vs.vs_code ∧
    as.as_prev_hashes = vs.vs_prev_hashes
End

(* ===== Asm State ↔ EVM Bytecode State ===== *)

(* Asm instruction index → byte offset in assembled bytecode *)
Definition asm_pc_to_offset_def:
  asm_pc_to_offset prog pc =
    SUM (MAP asm_inst_size (TAKE pc prog))
End

(* EVM context matches asm_state.
   The only difference is how PC is tracked:
   asm uses instruction index, EVM uses byte offset. *)
Definition asm_evm_rel_def:
  asm_evm_rel prog as es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.stack = as.as_stack ∧
         ctxt.memory = as.as_memory ∧
         ctxt.pc = asm_pc_to_offset prog as.as_pc ∧
         ctxt.returnData = as.as_returndata ∧
         ctxt.logs = as.as_logs ∧
         rb.accounts = as.as_accounts ∧
         rb.tStorage = as.as_transient
     | [] => F)
End

(* ===== Result Correspondence ===== *)

(* asm_result corresponds to Venom exec_result *)
Definition asm_venom_result_rel_def:
  asm_venom_result_rel label_offsets fn_eom ps ar vr ⇔
    case (ar, vr) of
      (AsmHalt as, Halt vs) =>
        venom_asm_rel label_offsets fn_eom ps vs as
    | (AsmRevert as, Abort Revert_abort vs) =>
        venom_asm_rel label_offsets fn_eom ps vs as
    | (AsmFault as, Abort ExHalt_abort vs) =>
        venom_asm_rel label_offsets fn_eom ps vs as
    | _ => F
End

(* asm_result corresponds to EVM execution result.
   run returns SOME (INR result, es) on termination:
     INR NONE          = clean halt (STOP/RETURN)
     INR (SOME Reverted) = revert
     INR (SOME exc)    = exceptional halt (OOG, invalid, etc.)
   INL never appears in run output (OWHILE exits on INR). *)
Definition asm_evm_result_rel_def:
  asm_evm_result_rel prog ar er ⇔
    case (ar, er) of
      (AsmHalt as, SOME (INR NONE, es)) =>
        asm_evm_rel prog as es
    | (AsmRevert as, SOME (INR (SOME Reverted), es)) =>
        asm_evm_rel prog as es
    | (AsmFault as, SOME (INR (SOME exc), es)) =>
        exc ≠ Reverted ∧ asm_evm_rel prog as es
    | _ => F
End
