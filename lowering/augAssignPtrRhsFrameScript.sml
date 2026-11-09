(* Project the existing same-endpoint frame, without enriching RHS provenance. *)
Theory augAssignPtrRhsFrame
Ancestors bodyPtrDefs ptrDiscipline finite_map

Theorem ghost_kept_old_operand:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa x ==>
  FLOOKUP G x = FLOOKUP G0 x /\
  op_taint tn (Var x) = op_taint tn0 (Var x)
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_clean_old_operand:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa x /\
  FLOOKUP G0 x = NONE /\ op_taint tn0 (Var x) = {} ==>
  FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}
Proof
  metis_tac[ghost_kept_old_operand]
QED
