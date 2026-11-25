Theory bodyForcedStorageFrameMods
Ancestors
  vyperStorageTrace

Theorem bop_forced_storage_frame:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result]
QED
