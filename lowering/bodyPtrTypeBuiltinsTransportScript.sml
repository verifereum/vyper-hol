(* Saved operand coverage across evaluation of a later operand.
   These boundaries preserve coverage only, not memory representation. *)
Theory bodyPtrTypeBuiltinsTransport
Ancestors
  bodyPtrDefs

Theorem ptr_buf_ok_transport:
  !cenv e op G s G' s'.
    ptr_buf_ok cenv e op G s /\
    eval_operand op s' = eval_operand op s /\
    (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) ==>
    ptr_buf_ok cenv e op G' s'
Proof
  rw[ptr_buf_ok_def] >> metis_tac[]
QED

Theorem ptr_buf_ok_ghost_kept:
  !cenv e op G0 s0 es sa tn0 G tn s.
    ptr_buf_ok cenv e op G0 s0 /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    eval_operand op s = eval_operand op s0 ==>
    ptr_buf_ok cenv e op G s
Proof
  rpt strip_tac >> irule ptr_buf_ok_transport >>
  qexistsl_tac [`G0`, `s0`] >> simp[] >>
  gvs[ghost_kept_def] >> metis_tac[]
QED
