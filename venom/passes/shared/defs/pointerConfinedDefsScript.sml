(*
 * Pointer Confinement Definitions
 *
 * Structural properties ensuring alloca pointer values don't affect
 * observable program behavior. Used as preconditions for passes that
 * change alloca layout (remove_unused, function_inliner, concretize).
 *
 * TOP-LEVEL:
 *   pointer_derived_vars    — variables reachable from roots via def-use
 *   pointer_confined        — pointer vars only in mem address positions
 *   alloca_roots            — alloca output variables in a function
 *   alloca_pointer_confined — pointer_confined specialized to alloca roots
 *
 * pointer_confined replaces the old alloca_safe_fn/sensitive_operands
 * approach. It's simpler and correct: instead of enumerating "sensitive"
 * operand positions per opcode, it requires pointer vars to only appear
 * in memory operations (where the pointer is an address) or ADD
 * (pointer arithmetic, output stays pointer-derived).
 *
 * Always true for Vyper-compiled code: alloca outputs are abstract
 * memory offsets used only for MSTORE/MLOAD/MCOPY via ADD.
 *)

Theory pointerConfinedDefs
Ancestors
  passSharedDefs memLocDefs

(* ===== Pointer-Derived Variables ===== *)

(* Variables transitively reachable from a set of root variables
   through def-use chains. Uses transitive_use_vars from passSharedDefs.
   Root variables are typically alloca outputs (FDOM amap or alloca_roots). *)
Definition pointer_derived_vars_def:
  pointer_derived_vars fn (roots : string set) =
    set (transitive_use_vars fn (SET_TO_LIST roots))
End

(* ===== Pointer Confinement ===== *)

(* Pointer-derived variables are only used as memory addresses.
   Every instruction that reads a pointer-derived var must be either:
   - a memory operation (has mem_write_ops or mem_read_ops), or
   - pointer arithmetic (ADD) whose output is also pointer-derived

   This ensures pointer values never affect control flow or
   observable scalar results.

   Without this, a program could compare two pointers:
     %cmp = EQ %ptr1, %ptr2
     JNZ %cmp, label
   The pointer values differ between original and transformed,
   so %cmp differs, and control flow diverges. *)
Definition pointer_confined_def:
  pointer_confined fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst v.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands /\
      v IN pv ==>
      mem_write_ops inst <> NONE \/
      mem_read_ops inst <> NONE \/
      inst.inst_opcode = ADD /\
        set inst.inst_outputs SUBSET pv
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
