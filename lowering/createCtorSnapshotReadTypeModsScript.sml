(* The physical type of a value read at a constructor snapshot. *)
Theory createCtorSnapshotReadTypeMods
Ancestors createCtorMaterializePhysicalMods vyperState

Theorem ctor_snapshot_read_physical_type_mods:
  expr_body_pre_mods mods ce cx env e st /\ ~is_word_type (lowered_value_type ce e) /\
  eval_expr cx e st = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) ==>
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  irule ctor_physical_bound_read_type_mods >>
  goal_assum (drule_at Any) >>
  simp[bind_def]
QED
