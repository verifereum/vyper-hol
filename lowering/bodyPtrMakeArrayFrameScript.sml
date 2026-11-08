(* Variable-level framing across aggregate child evaluation. *)
Theory bodyPtrMakeArrayFrame
Ancestors
  bodyPtrDefs loweringPosts venomExecSemantics venomState

Theorem child_old_variable_preserved:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
  lookup_var x s = SOME w /\
  FLOOKUP G x = FLOOKUP G0 x /\
  op_taint tn (Var x) = op_taint tn0 (Var x)
Proof
  simp[vv_post_def, ghost_kept_def] >> metis_tac[]
QED

Theorem child_old_buffer_preserved:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME w /\
  ptr_buf_ok cenv e0 (Var x) G0 s0 ==>
  ptr_buf_ok cenv e0 (Var x) G s
Proof
  strip_tac >> drule_all child_old_variable_preserved >> strip_tac >>
  gvs[ptr_buf_ok_def, eval_operand_def] >> metis_tac[]
QED
