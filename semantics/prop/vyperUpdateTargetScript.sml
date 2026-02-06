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
    update_target cx st (BaseTargetV (ScopedVar n) []) (Replace v) =
    update_scoped_var cx st v
Proof
  cheat
QED
