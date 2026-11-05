Theory bodyPtrIfExpNoCopy
Ancestors
  bodyPtrIfExpMemoryTransport bodyPtrPreds exprSimIfExp bodyPtrDefs context
  loweringPosts

(* Capacity is independent of interpretation, including in the no-copy arm. *)
Theorem ifexp_no_copy_capacity:
  !ce arm result op G s.
    same_memory_layout ce (lowered_value_type ce arm)
      (lowered_value_type ce result) /\
    ptr_buf_ok ce arm op G s ==>
    ptr_buf_ok ce result op G s
Proof
  rpt strip_tac >> gvs[same_memory_layout_def, ptr_buf_ok_def] >>
  metis_tac[]
QED

(* The actual-frame probe retains body_inv, expr_body_pre, the successful
   source evaluation/read, expr_post, ghost_inv and ghost_kept. Applying
   ptr_mem_ok_transport leaves two independent sufficient obligations:
   runtime source representation reinterprets as the result type in every
   memory, and val_store_size of the result fits the covered type buffer.
   Neither is supplied merely by the capacity theorem above. *)
