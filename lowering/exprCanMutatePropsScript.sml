(* Compiler mutation exclusion for effect-free expressions. *)
Theory exprCanMutateProps
Ancestors
  exprLowering loweringPosts supportedExprTraverse list

Theorem extrequest_snapshot_nonmutating:
  (!ce e. ~expr_has_effect e ==> ~expr_can_mutate ce e) /\
  (!ce es. ~EXISTS expr_has_effect es ==> ~exprs_can_mutate ce es) /\
  (!ce d. (case d of NONE => T | SOME e => ~expr_has_effect e) ==>
     ~opt_expr_can_mutate ce d) /\
  (!ce kes. ~EXISTS (expr_has_effect o SND) kes ==>
     ~named_exprs_can_mutate ce kes)
Proof
  ho_match_mp_tac expr_can_mutate_ind >>
  simp[expr_can_mutate_def] >> metis_tac[]
QED
