(* Memory-neutral administrative transport.  Operand and pointer transport use
   reserved_operand_ghost_frame and ptr_covers_frame from the imported theories;
   robust memory assertions transport by equality of vs_memory and t_mem. *)
Theory widenedAssignPtrIndexAdmin
Ancestors typedMemoryCopy bodyPtrBytestringBuiltinsExternalSlice
  decoderGhostFramePtr venomState freshWrites

Theorem widened_assign_admin_state_frame:
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
               vs_current_bb := t.vs_current_bb; vs_prev_bb := t.vs_prev_bb|> /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  typed_copy_state_frame sa off len s t
Proof
  strip_tac >> simp[typed_copy_state_frame_def] >>
  qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
  simp[NoAsms, typed_copy_frame_def]
QED
