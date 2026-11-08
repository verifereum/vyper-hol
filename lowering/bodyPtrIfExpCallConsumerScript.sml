Theory bodyPtrIfExpCallConsumer
Ancestors bodyPtrIfExpCallAlignment bodyPtrIfExpNoCopyAlignment
  bodyPtrDefs exprLowering vyperAST exprSimHypsDefs vyperTypeSystem

Theorem ptr_buf_ok_bytes_cong:
  type_memory_bytes ce (lowered_value_type ce e) =
    type_memory_bytes ce (lowered_value_type ce e') ==>
  (ptr_buf_ok ce e op G s <=> ptr_buf_ok ce e' op G s)
Proof
  simp[ptr_buf_ok_def]
QED

(* Literal return-tag alignment is not required by the IfExp consumers. *)
