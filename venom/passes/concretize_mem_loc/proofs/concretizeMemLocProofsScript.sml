(*
 * Concretize Memory Locations — Proofs
 *
 * Two parts:
 * 1. Allocator soundness: compute_alloc_map produces non-overlapping
 *    regions for simultaneously live allocations.
 * 2. Transform correctness: given a sound allocation map, the
 *    concretized program simulates the original under a memory
 *    remapping relation (not state_equiv, because memory layout differs).
 *
 * The transform replaces ALLOCA/PALLOCA/CALLOCA with ASSIGN of a
 * concrete offset. The original program
 * bump-allocates (each ALLOCA extends vs_memory), while the
 * concretized version pre-allocates all regions in a fixed layout.
 * So vs_memory genuinely differs between original and transformed.
 *
 * The simulation relation maps between the two memory layouts:
 * each allocation's region has the same CONTENTS, but may be at
 * a different absolute offset. Variables are partitioned into:
 *   - alloca outputs (in amap): hold different base offsets
 *   - pointer-derived vars (ADD outputs, etc.): hold derived addresses
 *     that differ by the same offset delta as their base alloca
 *   - scalar vars: hold identical values
 *
 * Key precondition: pointer_confined — pointer-derived variables
 * are only used as memory addresses (operands of memory operations
 * like MSTORE/MLOAD/MCOPY) or passed through ADD. They never
 * feed into comparisons, control flow, or other operations that
 * would observe the concrete address value. Without this, a pointer
 * comparison could diverge control flow between original and
 * transformed, making the theorem false.
 *
 * This is always true for Vyper-compiled Venom IR: alloca produces
 * abstract memory offsets used only for memory access.
 *
 * Framework: does NOT satisfy valid_state_rel (vs_memory and vs_allocas
 * differ). Proof is fully custom, not via block_sim_function.
 *)

Theory concretizeMemLocProofs
Ancestors
  concretizeMemLocDefs passSimulationProps venomWf

(* ===== Helpers ===== *)

(* Read a byte from memory, returning 0w for out-of-bounds.
   Matches EVM semantics: memory beyond current size reads as 0. *)
Definition mem_byte_at_def:
  mem_byte_at (mem : word8 list) i =
    if i < LENGTH mem then EL i mem else 0w
End

(* Find the inst_id for an alloca that produces variable v.
   Returns SOME inst_id if some alloca instruction produces [v].
   Post alloca_id removal: keyed by inst_id, not operand. *)
Definition fn_alloca_inst_id_of_var_def:
  fn_alloca_inst_id_of_var fn v =
    case FIND (\inst. is_alloca_op inst.inst_opcode /\
                      inst.inst_outputs = [v])
              (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)) of
      SOME inst => SOME inst.inst_id
    | NONE => NONE
End

(* Variables whose values may differ due to memory remapping.
   Includes alloca output vars (in FDOM amap) and all vars
   transitively derived from them (ADD of pointer
   with offset, etc.). Uses transitive_use_vars from passSharedDefs. *)
Definition pointer_derived_vars_def:
  pointer_derived_vars fn (amap : alloc_map) =
    set (transitive_use_vars fn (SET_TO_LIST (FDOM amap)))
End

(* ===== Pointer confinement ===== *)

(* Pointer-derived variables are only used as memory addresses.
   Every instruction that reads a pointer-derived var must be either:
   - a memory operation (has mem_write_ops or mem_read_ops), or
   - pointer arithmetic (ADD) whose output is also pointer-derived
   This ensures pointer values never affect control flow or
   observable scalar results.

   Without this, a program could compare two pointers:
     %cmp = EQ %ptr1, %ptr2  (unchanged by concretize_inst)
     JNZ %cmp, label
   The pointer values differ between original and transformed,
   so %cmp differs, and control flow diverges → theorem is FALSE.

   Always true for Vyper-compiled code: alloca outputs are abstract
   memory offsets used only for MSTORE/MLOAD/MCOPY via ADD. *)
Definition pointer_confined_def:
  pointer_confined fn (amap : alloc_map) <=>
    let pv = pointer_derived_vars fn amap in
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

(* ===== Memory remapping relation ===== *)

(* The original execution uses bump-allocation: each ALLOCA sets
   offset = LENGTH vs_memory, extends memory with zeroes, and records
   in vs_allocas.  The concretized execution replaces ALLOCA with
   ASSIGN of a concrete offset, so vs_allocas stays FEMPTY in s2 but
   s1.vs_allocas tracks all allocations.

   "Activated" = the alloca instruction has executed, meaning the
   inst_id is in s1.vs_allocas and s2 has the ASSIGN result.

   Initially (before any alloca executes), s1.vs_allocas = FEMPTY,
   so the activated clauses are vacuous and the relation reduces to
   s1 = s2 (all non-pointer-derived vars agree, no memory content
   constraints). *)
Definition mem_remap_equiv_def:
  mem_remap_equiv (amap : alloc_map) fn s1 s2 <=>
    (* 1. Non-pointer-derived variables agree *)
    (!v. v NOTIN FDOM amap /\
         v NOTIN pointer_derived_vars fn amap ==>
         lookup_var v s1 = lookup_var v s2) /\
    (* 2a. Activated alloca vars: s2 has concrete offset *)
    (!v addr aid.
       FLOOKUP amap v = SOME addr /\
       fn_alloca_inst_id_of_var fn v = SOME aid /\
       aid IN FDOM s1.vs_allocas ==>
       lookup_var v s2 = SOME addr) /\
    (* 2b. Non-activated alloca vars agree *)
    (!v. v IN FDOM amap ==>
       case fn_alloca_inst_id_of_var fn v of
         NONE => lookup_var v s1 = lookup_var v s2
       | SOME aid =>
           aid NOTIN FDOM s1.vs_allocas ==>
           lookup_var v s1 = lookup_var v s2) /\
    (* 3. Memory content for activated allocations *)
    (!aid orig_off sz.
       FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) ==>
       !v addr.
         FLOOKUP amap v = SOME addr /\
         fn_alloca_inst_id_of_var fn v = SOME aid ==>
         !i. i < sz ==>
           mem_byte_at s1.vs_memory (orig_off + i) =
           mem_byte_at s2.vs_memory (w2n addr + i)) /\
    (* 4. Scalar state fields agree *)
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs
End

(* ===== Allocator soundness ===== *)

Theorem allocate_with_livesets_non_overlapping:
  !global already to_alloc result.
    allocate_with_livesets global already to_alloc result = result' ==>
    !a1 a2 ls1 ls2 p1 p2 sz1 sz2.
      FLOOKUP result' a1 = SOME p1 /\
      FLOOKUP result' a2 = SOME p2 /\
      a1 <> a2 /\
      MEM (a1, ls1, sz1) (MAP (\(a,l,p,s). (a,l,s)) already ++
                           MAP (\(a,l,s). (a,l,s)) to_alloc) /\
      MEM (a2, ls2, sz2) (MAP (\(a,l,p,s). (a,l,s)) already ++
                           MAP (\(a,l,s). (a,l,s)) to_alloc) /\
      ls1 INTER ls2 <> {} ==>
      p1 + sz1 <= p2 \/ p2 + sz2 <= p1
Proof
  cheat
QED

(* ===== Transform correctness ===== *)

(* Preconditions:
   - venom_wf ctx: eliminates Error branches from step_inst.
   - ssa_form fn: fn_alloca_inst_id_of_var is unambiguous.
   - pointer_confined fn amap: pointer-derived vars only used as
     memory addresses, ensuring control flow is identical.

   Initial state: s1 = s2, s1.vs_allocas = FEMPTY.
   All clauses are vacuously satisfied or reduce to equality.

   Does not use block_sim_function — vs_memory and vs_allocas differ,
   violating valid_state_rel. Proof by custom induction on run_function.

   Key proof steps per instruction type:
   - ALLOCA→ASSIGN: sets different base offsets, extends s1 memory,
     updates s1.vs_allocas. Relation preserved: new region is zeroed
     in s1 (REPLICATE 0w) and in s2 (uninitialized = 0w by mem_byte_at).
   - ADD: exec_pure2 word_add. Output is
     pointer-derived, so allowed to differ.
   - Memory ops (MSTORE/MLOAD/MCOPY): read/write through remapped
     addresses. By pointer_confined, addresses are alloca-derived.
     By clause 3, memory content agrees at corresponding offsets.
   - All other instructions: unchanged. pointer_confined ensures
     operands are non-pointer-derived → agree → same result.
   - Terminators: unchanged, all operands are non-pointer → agree,
     so control flow is identical. *)
Theorem concretize_function_correct_proof:
  !amap fn fuel ctx s1 s2.
    venom_wf ctx /\ ssa_form fn /\
    pointer_confined fn amap /\
    mem_remap_equiv amap fn s1 s2 ==>
    lift_result
      (mem_remap_equiv amap fn)
      (mem_remap_equiv amap fn)
      (run_function fuel ctx fn s1)
      (run_function fuel ctx (concretize_function amap fn) s2)
Proof
  cheat
QED
