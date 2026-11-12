(* Constant installation updates exactly the immutable metadata. *)
Theory vyperConstantsStorageFrame
Ancestors
  vyperInterpreter vyperState

Theorem evaluate_module_constants_trace_machine_frame:
  !mods cx am addr am' obs.
    evaluate_module_constants_trace cx am addr mods = (SOME am',obs) ==>
    am' = (am with immutables := am'.immutables)
Proof
  Induct >- simp[evaluate_module_constants_trace_def] >>
  PairCases >> rpt gen_tac >>
  simp[evaluate_module_constants_trace_def] >>
  pairarg_tac >> Cases_on `result` >> simp[] >>
  pairarg_tac >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >>
  simp[merge_constants_def, abstract_machine_component_equality]
QED

Theorem evaluate_all_constants_machine_frame:
  evaluate_all_constants cx am addr mods = SOME am' ==>
  am' = (am with immutables := am'.immutables)
Proof
  simp[evaluate_all_constants_def, evaluate_module_constants_def] >>
  Cases_on `evaluate_module_constants_trace cx am addr (constants_order mods)` >>
  simp[] >> strip_tac >>
  metis_tac[evaluate_module_constants_trace_machine_frame]
QED
