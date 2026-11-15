(* Snapshot branch interface for effect-free external-call operands. *)
Theory exprExtRequestSnapshotProbe
Ancestors
  exprLowering loweringPosts exprExtRequestShape compileEnv list

Theorem extrequest_snapshot_nonmutating:
  (!ce e. ~expr_has_effect e ==> ~expr_can_mutate ce e) /\
  (!ce es. ~EXISTS expr_has_effect es ==> ~exprs_can_mutate ce es) /\
  (!ce d. (case d of NONE => T | SOME e => ~expr_has_effect e) ==> ~opt_expr_can_mutate ce d) /\
  (!ce kes. ~EXISTS (expr_has_effect o SND) kes ==>
     ~named_exprs_can_mutate ce kes)
Proof
  ho_match_mp_tac expr_can_mutate_ind >>
  simp[expr_can_mutate_def] >> metis_tac[]
QED

Theorem extrequest_snapshot_nonword_no_copy:
  ~is_word_type (vv_type vv) ==>
  compile_snapshot_vv ce F vv s = (vv,s)
Proof
  simp[compile_snapshot_vv_def, comp_return_def]
QED

Theorem extrequest_snapshot_word:
  is_word_type (vv_type vv) /\ unwrap_value ce vv s = (op,t) ==>
  compile_snapshot_vv ce copy vv s = (StackValue (vv_type vv) op,t)
Proof
  simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def]
QED

Theorem extrequest_snapshot_tail_no_copy:
  EVERY (\e. ~expr_has_effect e) (xs ++ kws) ==>
  ~exprs_can_mutate ce (xs ++ kws)
Proof
  strip_tac >> irule (cj 2 extrequest_snapshot_nonmutating) >>
  gvs[EVERY_MEM, EXISTS_MEM]
QED

Theorem extrequest_snapshot_body_no_copy:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip sig opts) (a::rest) d) es ==>
  ~exprs_can_mutate ce rest
Proof
  strip_tac >> drule extrequest_body_typed >> simp[] >>
  metis_tac[extrequest_snapshot_tail_no_copy, APPEND_NIL]
QED
