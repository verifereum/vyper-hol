Theory bodyPtrIfExpCopyInputs
Ancestors
  bodyPtrDefs venomExecSemantics venomState

(* Buffer capacity is independent of the value's semantic encoding. *)
Theorem ptr_buf_ok_read_covers:
  !cenv e op G tn s w n.
    ptr_buf_ok cenv e op G s /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    0 < n /\ n <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
    ?p. op = Var p /\ ptr_covers G tn p s n
Proof
  rpt strip_tac >>
  fs[ptr_buf_ok_def] >>
  gvs[ptr_covers_def, eval_operand_def] >>
  qexistsl [`w`, `b`, `sz`] >> simp[]
QED
