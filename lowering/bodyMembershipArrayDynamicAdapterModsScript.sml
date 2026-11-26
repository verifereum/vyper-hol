(* Bounded membership uses the two extra loop registers in its load slot. *)
Theory bodyMembershipArrayDynamicAdapterMods
Ancestors
  exprLowering compileEnv venomState

Theorem dynamic_loop_bound_some_offset_adapter:
  Var ("%" ++ toString (sl.cs_next_var + 4 + 2 +
    (if 0 < word_scale loc then 1 else 0) +
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))) =
  Var ("%" ++ toString (sl.cs_next_var + 4 +
    (if IS_SOME (SOME (cap:num)) then 2 else 0) +
    (if 0 < word_scale loc then 1 else 0) +
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))
Proof
  simp[]
QED
