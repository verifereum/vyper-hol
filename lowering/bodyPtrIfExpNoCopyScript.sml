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

(* Actual lowered-type audit:
   - Ordinary expressions: lowered_value_type_def returns expr_type, so
     ptr_mem_ok_runtime_type applies without a semantic conversion.
   - StringL/BytesL: produced bound is LENGTH payload. The bytestring
     transport boundary needs typing at that bound as well as at the
     annotation. Successful evaluation must supply the payload typing.
   - AbiEncode: produced bound is abi_size_bound (+ method selector).
     Again it is bytestring transport, with produced-bound typing needed.
   - IntCall: source type is ce_func_return_type (nsid_to_string id).
     body_inv identifies that map with build_func_return_type tops.
     supported_internal_signature_return connects it to sig.ret_ty only
     with supported_function_decl and a matching env.fn_sigs lookup.
   Destination typing follows from ifexp_body_pre_read_typed. The existing
   memory_rhs_read_lowered_typed would supply source typing, but its
   supported_expr tops arm premise is not in expr_body_pre. A checked
   endpoint probe reduces exactly to that premise. Internal-call source
   non-wordness and aggregate robust interpretation remain unresolved.
   The unadmitted S1 bodySimIfExpWidened reference is itself HELD/cheated
   for a post_value_type interface; it is not a completed port template. *)
