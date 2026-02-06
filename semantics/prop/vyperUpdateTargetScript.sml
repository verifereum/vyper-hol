Theory vyperUpdateTarget

Ancestors
  vyperInterpreter vyperLookup vyperAssignTarget

Definition update_target_def:
  update_target cx st av ao = SND (assign_target cx av ao st)
End

Definition valid_target_def:
  valid_target cx st av ao = ISL (FST (assign_target cx av ao st))
End

Theorem update_target_scoped_var_replace:
  ∀cx st n v.
    var_in_scope st n ⇒
    update_target cx st (BaseTargetV (ScopedVar n) []) (Replace v) =
    update_scoped_var st n v
Proof
  rw[update_target_def] >>
  imp_res_tac assign_target_scoped_var_replace >>
  pop_assum (qspecl_then [`v`, `cx`] strip_assume_tac) >>
  simp[]
QED

Theorem update_target_scoped_var_update:
  ∀cx st n bop v1 v2 v.
    evaluate_binop bop v1 v2 = INL v ∧
    lookup_scoped_var st n = SOME v1 ⇒
    update_target cx st (BaseTargetV (ScopedVar n) []) (Update bop v2) =
    update_scoped_var st n v
Proof
  cheat
QED

Theorem valid_target_scoped_var:
  ∀cx st n ao. var_in_scope st n ⇔ valid_target cx st (BaseTargetV (ScopedVar n) []) ao
Proof
  cheat
QED

Theorem update_target_preserves_toplevel_name_targets:
  ∀cx st av ao n.
    (* we may need assumption: valid_target cx st av ao *)
    lookup_toplevel_name_target cx (update_target cx st av ao) n = lookup_toplevel_name_target cx st n
Proof
  cheat
QED

Theorem update_target_preserves_name_targets:
  ∀cx st av ao n.
    (* we may need assumption: valid_target cx st av ao *)
    lookup_name_target cx (update_target cx st av ao) n = lookup_name_target cx st n
Proof
  cheat
QED

Theorem name_lookup_after_update_target_replace:
  ∀cx st n av v.
    valid_lookups cx st ∧
    lookup_name_target cx st n = SOME av ⇒
    lookup_name cx (update_target cx st av (Replace v)) n = SOME v
Proof
  cheat
QED

Theorem name_lookup_after_update_target_update:
  ∀cx st n bop av v1 v2 v.
    valid_lookups cx st ∧
    lookup_name cx st n = SOME v1 ∧
    lookup_name_target cx st n = SOME av ∧
    evaluate_binop bop v1 v2 = INL v ⇒
    lookup_name cx (update_target cx st av (Update bop v2)) n = SOME v
Proof
  cheat
QED

Theorem update_target_preserves_valid_lookups:
  ∀cx st av ao.
    valid_lookups cx st ⇒
    valid_lookups cx (update_target cx st av ao)
Proof
  cheat
QED

Theorem update_target_preserves_var_in_scope:
  ∀cx st av ao n v.
    var_in_scope st n ⇒
    var_in_scope (update_target cx st av ao) n
Proof
  cheat
QED
