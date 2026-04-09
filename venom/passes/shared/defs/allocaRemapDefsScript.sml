(*
 * Alloca Remapping Definitions
 *
 * State relation for reasoning about execution under different alloca
 * layouts (same code, different concrete base addresses). Used by
 * concretize_mem_loc and as a building block for other passes that
 * change alloca structure.
 *
 * TOP-LEVEL:
 *   mem_byte_at           — safe memory byte access (0w for OOB)
 *   fn_alloca_id_of_var   — find alloca inst_id that produces a variable
 *   in_alloca_region        — address falls within an alloca region
 *   ptrs_in_alloca_bounds  — pointer-derived values within alloca regions
 *   alloca_mem_agrees       — memory at alloca regions corresponds
 *   alloca_remap_rel        — full state relation for remapping
 *
 * Design: alloca_remap_rel captures what must hold for execution under
 * pointer_confined to be insensitive to alloca base addresses:
 *   - Non-pointer vars agree (clause 1)
 *   - Alloca output vars hold remapped offsets (clause 2)
 *   - Memory at alloca regions corresponds (clause 3)
 *   - Memory OUTSIDE alloca regions is identical (clause 4)
 *   - Alloca regions don't overlap in either state (clause 5)
 *   - Alloca maps have same domain and sizes (clause 6)
 *   - Scalar state fields agree (clause 7)
 *)

Theory allocaRemapDefs
Ancestors
  venomState venomExecSemantics pointerConfinedDefs venomMemDefs

(* ===== Memory Byte Access ===== *)

(* Read a byte from memory, returning 0w for out-of-bounds.
   Matches EVM semantics: memory beyond current size reads as 0. *)
Definition mem_byte_at_def:
  mem_byte_at (mem : word8 list) i =
    if i < LENGTH mem then EL i mem else 0w
End

(* ===== Alloca Utilities ===== *)

(* Find the inst_id for an alloca that produces variable v.
   Returns SOME inst_id if some alloca instruction produces [v]. *)
Definition fn_alloca_id_of_var_def:
  fn_alloca_id_of_var fn v =
    case FIND (\inst. is_alloca_op inst.inst_opcode /\
                      inst.inst_outputs = [v])
              (fn_insts fn) of
      SOME inst => SOME inst.inst_id
    | NONE => NONE
End

(* Address falls within some alloca region in a state. *)
Definition in_alloca_region_def:
  in_alloca_region s i <=>
    ?aid off sz.
      FLOOKUP s.vs_allocas aid = SOME (off, sz) /\
      off <= i /\ i < off + sz
End

(* allocas_non_overlapping now comes from venomMemDefs *)

(* Every pointer-derived variable's runtime value falls within some
   alloca region. Required for memory operations through pointer
   addresses to be covered by alloca_mem_agrees.
   Analysis-independent — doesn't reference bp_result.
   bp_ptrs_bounded (from base_ptr analysis) implies pointer offsets
   are within alloca regions (though the exact bridge is indirect —
   bp_ptrs_bounded is per-access, this is per-variable). *)
Definition ptrs_in_alloca_bounds_def:
  ptrs_in_alloca_bounds fn (roots : string set) s <=>
    let pv = pointer_derived_vars fn roots in
    !v w. v IN pv /\ lookup_var v s = SOME w ==>
      in_alloca_region s (w2n w)
End

(* Memory access through pointer-derived variables stays within alloca
   bounds. For each instruction that reads or writes memory through a
   pointer (as identified by mem_read_ops/mem_write_ops), the address
   operand plus the access size fits within the alloca region containing
   that address.
   - For MLOAD/MSTORE (iao_size = SOME (Lit 32w)): addr + 32 <= off + sz
   - For MSTORE8 (iao_size = SOME (Lit 1w)): addr + 1 <= off + sz
   - For MCOPY/CODECOPY/etc. (iao_size = SOME size_op): addr + size <= off + sz
   True for Vyper: allocas are 32-byte aligned, all accesses fit. *)
Definition alloca_safe_access_def:
  alloca_safe_access fn (roots : string set) s <=>
    let pv = pointer_derived_vars fn roots in
    (* All alloca regions fit within memory (no expansion on access) *)
    (!aid off asz.
      FLOOKUP s.vs_allocas aid = SOME (off, asz) ==>
      off + asz <= LENGTH s.vs_memory) /\
    (* Memory accesses through pointer-derived vars stay within alloca *)
    (!bb inst ops v w sz_op sz_val aid off asz.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
      ops.iao_ofst = Var v /\ v IN pv /\
      lookup_var v s = SOME w /\
      FLOOKUP s.vs_allocas aid = SOME (off, asz) /\
      off <= w2n w /\ w2n w < off + asz /\
      ops.iao_max_size = SOME sz_op /\
      eval_operand sz_op s = SOME sz_val ==>
      w2n w + w2n sz_val <= off + asz)
End

(* Step-preservation oracle for alloca_safe_access and ptrs_in_alloca_bounds.
   alloca_safe_access clause 2 quantifies over ALL memory-accessing
   instructions in fn — including those with variable-sized operands
   (MCOPY, CALLDATACOPY, CALL/STATICCALL/DELEGATECALL etc.).
   When stepping instruction inst', if inst' outputs a variable sz_var
   that appears as a size operand of some other mem-accessing instruction
   inst, the new value of sz_var is unrelated to the old value, so the
   clause-2 bound cannot be transferred from pre-state to post-state
   without program-specific reasoning.
   True for Vyper: the compiler ensures all accesses through pointer-
   derived vars stay within alloca regions at every step.
   Not derivable from pointer_arith_in_region alone. *)
Definition step_preserves_safety_def:
  step_preserves_safety fn roots <=>
    !inst bb s v.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      step_inst_base inst s = OK v /\
      ~is_terminator inst.inst_opcode /\
      ~is_ext_call_op inst.inst_opcode /\
      alloca_safe_access fn roots s /\
      ptrs_in_alloca_bounds fn roots s ==>
      alloca_safe_access fn roots v /\
      ptrs_in_alloca_bounds fn roots v
End

(* ===== Pointer Arithmetic In-Region ===== *)

(* Every pointer-preserving instruction (ADD/SUB/ASSIGN/PHI) in fn
   produces output values that stay within the same alloca region as
   the pointer input operand. For ADD(ptr, k): if ptr is in region
   [off, off+asz), then ptr+k is also in [off, off+asz).
   True for Vyper: all pointer offsets are compile-time bounded within
   the alloca size (struct field offsets, array index * 32, etc.).
   This is needed because the displacement invariant (clause 2b) requires
   values to stay in their alloca region; otherwise, a value could "jump"
   to a different alloca region after remapping. *)
Definition pointer_arith_in_region_def:
  pointer_arith_in_region fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst s v out w_out inp w_in aid off asz.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      is_pointer_preserving_op inst.inst_opcode /\
      step_inst_base inst s = OK v /\
      inst.inst_outputs = [out] /\
      out IN pv /\
      lookup_var out v = SOME w_out /\
      MEM (Var inp) inst.inst_operands /\
      inp IN pv /\
      lookup_var inp s = SOME w_in /\
      FLOOKUP s.vs_allocas aid = SOME (off, asz) /\
      off <= w2n w_in /\ w2n w_in < off + asz ==>
      off <= w2n w_out /\ w2n w_out < off + asz
End

(* ===== Alloca Remap ===== *)

(* An alloca_remap maps instruction IDs to new base offsets. *)
Type alloca_remap = ``:(num, num) fmap``

(* Memory content at corresponding alloca regions agrees.
   For every activated alloca, each byte in the region agrees. *)
Definition alloca_mem_agrees_def:
  alloca_mem_agrees (remap : alloca_remap) s1 s2 <=>
    !aid orig_off sz new_off.
      FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
      FLOOKUP remap aid = SOME new_off ==>
      !i. i < sz ==>
        mem_byte_at s1.vs_memory (orig_off + i) =
        mem_byte_at s2.vs_memory (new_off + i)
End

(* ===== Full Remapping Relation ===== *)

(* Two states are related under alloca remapping.
   fn determines pointer_derived_vars; roots = alloca output variables;
   remap maps alloca inst_ids to new base offsets. *)
Definition alloca_remap_rel_def:
  alloca_remap_rel fn (roots : string set) (remap : alloca_remap) s1 s2 <=>
    let pv = pointer_derived_vars fn roots in
    (* 1. Non-pointer variables agree *)
    (!v. v NOTIN pv ==> lookup_var v s1 = lookup_var v s2) /\
    (* 2. Alloca output variables hold their respective offsets *)
    (!v aid orig_off sz new_off.
       v IN roots /\
       fn_alloca_id_of_var fn v = SOME aid /\
       FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
       FLOOKUP remap aid = SOME new_off ==>
       lookup_var v s1 = SOME (n2w orig_off) /\
       lookup_var v s2 = SOME (n2w new_off)) /\
    (* 2b. ALL pointer-derived variables have corresponding values:
       displacement from alloca base is the same in both states.
       Root vars satisfy this trivially (displacement 0, from clause 2).
       Derived vars (ADD/SUB of pointer + constant) are also constrained.
       The containment bounds (orig_off <= w2n w1, etc.) ensure the
       displacement word equation corresponds to natural-number subtraction
       and that the aid is the unique alloca containing the pointer value. *)
    (!v. v IN pv ==>
       lookup_var v s1 = NONE /\ lookup_var v s2 = NONE \/
       ?w1 w2 aid orig_off sz new_off.
         FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
         FLOOKUP remap aid = SOME new_off /\
         lookup_var v s1 = SOME w1 /\
         lookup_var v s2 = SOME w2 /\
         w1 - n2w orig_off = w2 - n2w new_off /\
         orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
         new_off <= w2n w2 /\ w2n w2 < new_off + sz /\
         orig_off + sz < dimword (:256) /\
         new_off + sz < dimword (:256)) /\
    (* 3. Memory content at alloca regions agrees *)
    alloca_mem_agrees remap s1 s2 /\
    (* 4. Memory OUTSIDE alloca regions (in BOTH states) is byte-identical.
       Two-sided: a position inside s2's alloca but outside s1's may
       differ, and vice versa. Required for non-pointer memory access
       (e.g. MLOAD [Lit 0x100w]) to produce the same result. *)
    (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
         mem_byte_at s1.vs_memory i = mem_byte_at s2.vs_memory i) /\
    (* 5. Alloca regions are non-overlapping in both states.
       Required for mstore within one region to not corrupt
       another region's correspondence. *)
    allocas_non_overlapping s1 /\
    allocas_non_overlapping s2 /\
    (* 6. Alloca maps: same domain, remap faithfully maps s1 IDs to s2 offsets *)
    FDOM s1.vs_allocas = FDOM s2.vs_allocas /\
    (!aid off1 sz new_off.
      FLOOKUP s1.vs_allocas aid = SOME (off1, sz) /\
      FLOOKUP remap aid = SOME new_off ==>
      FLOOKUP s2.vs_allocas aid = SOME (new_off, sz)) /\
    (* 7. Memory lengths agree (needed for MSIZE determinism) *)
    LENGTH s1.vs_memory = LENGTH s2.vs_memory /\
    (* 8. Scalar state fields agree *)
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_hashes = s2.vs_prev_hashes
End
