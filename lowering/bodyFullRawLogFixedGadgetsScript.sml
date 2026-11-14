(* Fixed RawLog gadget publication boundary.  Keep the endpoint proofs in
   their owning theories; consumers join them with the data child. *)
Theory bodyFullRawLogFixedGadgets
Ancestors
  bodyFullRawLogFixedAlloc bodyFullRawLogFixedTail bodyFullRawLogFixedBoundary

(* Allocation supplies the scratch operand lookup, 32-byte coverage, old
   register/allocation preservation, and local/old-allocation separation.
   raw_log_fixed_scratch_post carries coverage and the allocation entry
   through the data child; expr_post preserves the old operand lookup and
   local_region_kept carries local separation.

   The suffix consumes expr_post and ghost_kept_at anchored before allocation,
   not at the data child's entry.  Composition must reanchor the scalar data
   post and retain the original compiler-id threshold for the final frame.
   These are composition obligations, not extra runtime premises. *)
