(*
 * Alloca Remapping Definitions
 *
 * State relation for reasoning about execution under different alloca
 * layouts. Used by passes that change alloca structure: remove_unused
 * (removes dead ALLOCAs), function_inliner (merges alloca spaces),
 * concretize_mem_loc (dynamic → static offsets).
 *
 * TOP-LEVEL:
 *   mem_byte_at           — safe memory byte access (0w for OOB)
 *   fn_alloca_id_of_var   — find alloca inst_id that produces a variable
 *   in_alloca_region        — address falls within an alloca region
 *   allocas_non_overlapping — alloca regions don't overlap in a state
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
  venomState pointerConfinedDefs

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

(* Alloca regions in a state are pairwise non-overlapping. *)
Definition allocas_non_overlapping_def:
  allocas_non_overlapping s <=>
    !aid1 aid2 off1 sz1 off2 sz2.
      FLOOKUP s.vs_allocas aid1 = SOME (off1, sz1) /\
      FLOOKUP s.vs_allocas aid2 = SOME (off2, sz2) /\
      aid1 <> aid2 ==>
      off1 + sz1 <= off2 \/ off2 + sz2 <= off1
End

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
    (* 6. Alloca maps have same domain and sizes *)
    FDOM s1.vs_allocas = FDOM s2.vs_allocas /\
    (!aid off1 sz1 off2 sz2.
      FLOOKUP s1.vs_allocas aid = SOME (off1, sz1) /\
      FLOOKUP s2.vs_allocas aid = SOME (off2, sz2) ==>
      sz1 = sz2) /\
    (* 7. Scalar state fields agree *)
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
