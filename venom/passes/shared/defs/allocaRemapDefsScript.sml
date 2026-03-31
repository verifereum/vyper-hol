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
 *   alloca_mem_agrees     — memory content at corresponding alloca
 *                           offsets agrees between two states
 *   alloca_remap_rel      — full state relation for remapping
 *
 * The key invariant: under pointer_confined, execution is insensitive
 * to concrete alloca base addresses. alloca_remap_rel captures what
 * must hold: non-pointer vars agree, pointer vars may differ (but
 * only in address positions), and memory content at corresponding
 * offsets is byte-identical.
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

(* Two states are related under alloca remapping when:
   1. Non-pointer-derived variables agree
   2. Alloca output variables hold remapped offsets
   3. Memory content at alloca regions agrees
   4. Alloca maps have same domain and compatible sizes
   5. Scalar state fields agree

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
    (* 4. Alloca maps have same domain and sizes *)
    FDOM s1.vs_allocas = FDOM s2.vs_allocas /\
    (!aid off1 sz1 off2 sz2.
      FLOOKUP s1.vs_allocas aid = SOME (off1, sz1) /\
      FLOOKUP s2.vs_allocas aid = SOME (off2, sz2) ==>
      sz1 = sz2) /\
    (* 5. Scalar state fields agree *)
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
