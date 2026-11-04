(* The observation log does not affect evaluation and retains every prefix. *)
Theory vyperStorageTrace
Ancestors
  vyperState vyperCallOutcome vyperCreate vyperInterpreter

Definition storage_trace_frame_def:
  storage_trace_frame (f : evaluation_state -> 'a evaluation_result) <=>
    !st observations.
      f (st with storage_trace := observations) =
      case f (st with storage_trace := []) of
        (res,st') =>
          (res,st' with storage_trace := observations ++ st'.storage_trace)
End

Theorem evaluate_storage_trace_frame:
  (!cx s. storage_trace_frame (eval_stmt cx s)) /\
  (!cx ss. storage_trace_frame (eval_stmts cx ss)) /\
  (!cx it. storage_trace_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. storage_trace_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. storage_trace_frame (eval_expr cx e)) /\
  (!cx es. storage_trace_frame (eval_exprs cx es)) /\
  (!cx t. storage_trace_frame (eval_base_place cx t)) /\
  (!cx t. storage_trace_frame (eval_target_place cx t)) /\
  (!cx t v. storage_trace_frame (assign_tuple_targets cx t v)) /\
  (!cx ts vs. storage_trace_frame (assign_tuple_target_list cx ts vs)) /\
  (!cx es. storage_trace_frame (eval_expr_results cx es))
Proof
  rpt conj_tac >> rw[storage_trace_frame_def]
QED

Theorem storage_trace_frame_prefix:
  storage_trace_frame f /\ f st = (res,st') ==>
  ?observations. st'.storage_trace = st.storage_trace ++ observations
Proof
  rw[storage_trace_frame_def]
QED

Theorem storage_trace_frame_erasure:
  storage_trace_frame f ==>
  FST (f st) = FST (f (erase_storage_trace st)) /\
  erase_storage_trace (SND (f st)) =
    erase_storage_trace (SND (f (erase_storage_trace st)))
Proof
  rw[storage_trace_frame_def, erase_storage_trace_def]
QED
