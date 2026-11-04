(* Interface probes, not a counterexample to expression simulation. *)
Theory abiMetadataDescentProbe
Ancestors
  compileEnv vyperValue retAbiPlanProps finite_map list

Theorem metadata_namespace_alias_probe:
  nsid_to_string (NONE,"0.X") = nsid_to_string (SOME 0,"X")
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

(* A finite successful type cannot traverse the self dependency hidden by
   two aliases with equal field declarations. *)
Theorem metadata_alias_cycle_probe:
  let env = FEMPTY |+
      ((NONE,"0.X"), StructArgs [("next",StructT (SOME 0,"X"))]) |+
      ((SOME 0,"X"), StructArgs [("next",StructT (SOME 0,"X"))]) in
  evaluate_type env (StructT (NONE,"0.X")) = NONE
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

(* Unused aliases can be removed together; the field being evaluated no
   longer needs either compiler/semantic ancestor name. *)
Theorem metadata_alias_acyclic_probe:
  let env = FEMPTY |+
      ((NONE,"0.X"), StructArgs [("value",BaseT (UintT 256))]) |+
      ((SOME 0,"X"), StructArgs [("value",BaseT (UintT 256))]) in
  evaluate_type env (StructT (NONE,"0.X")) =
    SOME (StructTV [("value",BaseTV (UintT 256))]) /\
  evaluate_types (env \\ (NONE,"0.X")) [BaseT (UintT 256)] [] =
  evaluate_types (env \\ (NONE,"0.X") \\ (SOME 0,"X"))
    [BaseT (UintT 256)] []
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED
