(*
 * Pointer Confinement Definitions
 *
 * Structural properties ensuring alloca pointer values don't affect
 * observable program behavior. Used as preconditions for passes that
 * change alloca layout (remove_unused, function_inliner, concretize).
 *
 * TOP-LEVEL:
 *   is_pointer_preserving_op — opcodes that propagate pointer derivation
 *   pointer_use_step         — one step of pointer-specific use chain
 *   pointer_derived_vars     — variables reachable from roots via
 *                              pointer-preserving def-use chains
 *   pointer_confined         — pointer vars only in mem address positions
 *   alloca_roots             — alloca output variables in a function
 *   alloca_pointer_confined  — pointer_confined specialized to alloca roots
 *
 * pointer_confined requires pointer-derived vars to only appear in
 * memory address positions (via iao_ofst from mem_write_ops/mem_read_ops)
 * or pointer-preserving operations (ADD/SUB/ASSIGN/PHI whose outputs
 * remain pointer-derived).
 *
 * pointer_derived_vars follows only pointer-preserving operations,
 * NOT all def-use chains. MLOAD output from a pointer address is DATA,
 * not a pointer — it can be freely used in any computation.
 *
 * Always true for Vyper-compiled code: alloca outputs are abstract
 * memory offsets used only for MSTORE/MLOAD/MCOPY via ADD.
 *)

Theory pointerConfinedDefs
Ancestors
  passSharedDefs memLocDefs

(* ===== Pointer-Preserving Operations ===== *)

(* Instructions that propagate pointer derivation: their output is
   pointer-derived if any input is. Other instructions (MLOAD, MUL, EQ, ...)
   consume pointer values but produce non-pointer results. *)
Definition is_pointer_preserving_op_def:
  is_pointer_preserving_op ADD = T /\
  is_pointer_preserving_op SUB = T /\
  is_pointer_preserving_op ASSIGN = T /\
  is_pointer_preserving_op PHI = T /\
  is_pointer_preserving_op _ = F
End

(* ===== Pointer-Derived Variables ===== *)

(* One step of pointer-specific use chain: collect outputs of
   pointer-preserving instructions that read a pointer-derived var.
   Unlike use_step (which follows ALL def-use), this only follows
   instructions that propagate pointer identity. *)
Definition pointer_use_step_def:
  pointer_use_step fn vars =
    FLAT (MAP (\bb.
      FLAT (MAP (\inst.
        if is_pointer_preserving_op inst.inst_opcode /\
           EXISTS (\op. case op of Var v => MEM v vars | _ => F)
                  inst.inst_operands
        then inst.inst_outputs
        else [])
        bb.bb_instructions))
      fn.fn_blocks)
End

(* Single step of pointer transitive closure: add newly reachable vars. *)
Definition pointer_use_step_step_def:
  pointer_use_step_step fn vars =
    let new_vars = FILTER (\v. ~MEM v vars) (pointer_use_step fn vars) in
    if new_vars = [] then NONE
    else SOME (vars ++ new_vars)
End

(* Compute transitive closure of pointer-preserving use chain.
   Iterates until fixpoint via OWHILE. *)
Definition pointer_use_vars_def:
  pointer_use_vars fn vars =
    case OWHILE ISL (\v. case pointer_use_step_step fn (OUTL v) of
                           NONE => INR (OUTL v)
                         | SOME vs => INL vs)
                (INL vars) of
      SOME (INR result) => result
    | _ => vars
End

(* Variables transitively reachable from roots via pointer-preserving
   def-use chains only. Root variables are typically alloca outputs.
   Unlike transitive_use_vars, this does NOT follow through MLOAD,
   MUL, EQ, etc. — those consume pointers but don't produce them. *)
Definition pointer_derived_vars_def:
  pointer_derived_vars fn (roots : string set) =
    set (pointer_use_vars fn (SET_TO_LIST roots))
End

(* ===== Pointer Confinement ===== *)

(* Pointer-derived variables are only used in safe positions:
   1. Memory address position (iao_ofst of mem_write_ops/mem_read_ops)
   2. Pointer-preserving operation with outputs still pointer-derived

   This ensures pointer values never reach control flow (JNZ condition),
   storage (SSTORE value), external calls (CALL gas/addr/val), or
   other observable positions.

   Key: checks operand POSITION, not just instruction type.
   MSTORE [addr, value] — pointer in addr (position 0) is fine,
   pointer in value (position 1) is rejected because it could be
   MLOAD'd back and escape through non-memory operations. *)
Definition pointer_confined_def:
  pointer_confined fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst v.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands /\
      v IN pv ==>
      (?ops. mem_write_ops inst = SOME ops /\ Var v = ops.iao_ofst) \/
      (?ops. mem_read_ops inst = SOME ops /\ Var v = ops.iao_ofst) \/
      (is_pointer_preserving_op inst.inst_opcode /\
        set inst.inst_outputs SUBSET pv)
End

(* ===== Alloca Roots ===== *)

(* The set of variables produced by ALLOCA instructions in a function. *)
Definition alloca_roots_def:
  alloca_roots fn =
    { out | ∃inst. MEM inst (fn_insts fn) ∧
                   inst.inst_opcode = ALLOCA ∧
                   inst_output inst = SOME out }
End

(* ===== Function-Level Pointer Confinement ===== *)

(* A function's alloca pointers are confined: no alloca-derived value
   reaches observable state (control flow, external calls, storage). *)
Definition alloca_pointer_confined_def:
  alloca_pointer_confined fn <=>
    pointer_confined fn (alloca_roots fn)
End
