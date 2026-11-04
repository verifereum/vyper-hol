Theory loadElimKeyInterfaceProbes
Ancestors
  loadElimKeyRead memAliasDefs

(* Rejection of the proposed inference from nonundefined/nonalias to resolved
   regions. This is NOT a counterexample to the frozen pass theorem. Distinct
   allocas are declared disjoint before the unknown-offset branch is tested. *)
Theorem le_unknown_offset_nonalias_probe:
  wf_alias_sets FEMPTY /\
  (<| ml_offset := NONE; ml_size := SOME 32;
      ml_alloca := SOME (Allocation 1); ml_volatile := F |> <> ml_undefined) /\
  ~ma_may_alias FEMPTY
    <| ml_offset := NONE; ml_size := SOME 32;
       ml_alloca := SOME (Allocation 1); ml_volatile := F |>
    <| ml_offset := SOME 0; ml_size := SOME 32;
       ml_alloca := SOME (Allocation 2); ml_volatile := F |> /\
  memloc_runtime_region
    <| ml_offset := NONE; ml_size := SOME 32;
       ml_alloca := SOME (Allocation 1); ml_volatile := F |> s = NONE
Proof
  EVAL_TAC >> simp[]
QED
