(* Source-only machine frame for a supported, nonmutating target walk. *)
Theory targetPureWalkSource
Ancestors
  targetPureWalkCallees vyperReadOnlyTargetCallFree vyperEvalFrame
  stmtLowering exprLowering vyperTypeCallGraph rich_list
  vyperMachineFrame vyperCallOutcomeFrame vyperState list pair
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = Parse.hide "body";

Theorem walk_frame_trans[local]:
  machine_frame (s with logs := t.logs) t /\
  machine_frame (t with logs := u.logs) u ==>
  machine_frame (s with logs := u.logs) u
Proof
  simp[machine_frame_def]
QED

Theorem walk_frame_machine[local]:
  state_rel_frame machine_frame f ==>
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) f
Proof
  simp[state_rel_frame_def, machine_frame_def]
QED

Theorem walk_exprs_nonmutating[local]:
  !es cenv. ~exprs_can_mutate cenv es <=>
    EVERY (\e. ~expr_can_mutate cenv e) es
Proof
  Induct >> simp[expr_can_mutate_def]
QED

Theorem walk_named_nonmutating[local]:
  !kes cenv. named_exprs_can_mutate cenv kes =
    exprs_can_mutate cenv (MAP SND kes)
Proof
  Induct >> simp[expr_can_mutate_def, FORALL_PROD]
QED
