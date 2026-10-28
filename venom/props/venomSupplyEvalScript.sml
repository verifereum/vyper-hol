(* Symbolic identity laws for supply checks during certified evaluation. *)
Theory venomSupplyEval
Ancestors venomFnScheduleRunner list
Libs cv_transLib

val () = cv_auto_trans list_subset_def;

Theorem list_subset_refl[compute]:
  list_subset xs xs
Proof
  simp[list_subset_def, EVERY_MEM]
QED

Theorem ir_supply_extends_refl[compute]:
  ir_supply_extends supply supply
Proof
  simp[ir_supply_extends_def, list_subset_refl]
QED

Theorem list_subset_append:
  !prefix suffix ys.
    list_subset (prefix ++ suffix) ys =
      (list_subset prefix ys /\ list_subset suffix ys)
Proof
  simp[list_subset_def, EVERY_APPEND]
QED
