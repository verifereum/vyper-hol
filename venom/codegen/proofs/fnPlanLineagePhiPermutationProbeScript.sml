Theory fnPlanLineagePhiPermutationProbe
Ancestors
  fnPlanLineagePhiLoopProbe

(* Change only the order of the three header PHIs. *)
Definition phi_permutation_loop_def:
  phi_permutation_loop order = phi_collision_loop with fn_blocks :=
    MAP (\bb. if bb.bb_label = "header" then
      bb with bb_instructions :=
        MAP (\i. EL i temporal_collision_phis) order ++
        [mk_inst 7 JNZ [Lit 1w;Label "left";Label "right"] []]
      else bb) phi_collision_loop.fn_blocks
End

Definition phi_permutation_flags_def:
  phi_permutation_flags order =
    [canonical_param_prefix (phi_permutation_loop order);
     wf_function (phi_permutation_loop order);
     fn_inst_wf (phi_permutation_loop order);
     ssa_form (phi_permutation_loop order);
     def_dominates_uses (phi_permutation_loop order);
     single_use_form (phi_permutation_loop order);
     cfg_is_normalized (cfg_analyze (phi_permutation_loop order)) (phi_permutation_loop order);
     block_entries_ready (cfg_analyze (phi_permutation_loop order)) (phi_permutation_loop order);
     phi_operands_ready (phi_permutation_loop order);
     EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions) (phi_permutation_loop order).fn_blocks]
End

Theorem phi_permutation_flags_table:
  MAP phi_permutation_flags
    [[0;1;2];[0;2;1];[1;0;2];[1;2;0];[2;0;1];[2;1;0]] =
    REPLICATE 6 [T;T;T;T;T;T;T;T;F;T]
Proof
  EVAL_TAC >> simp[]
QED

Definition phi_permutation_lives_def:
  phi_permutation_lives order =
    MAP (live_vars_at (liveness_analyze (phi_permutation_loop order)) "header") [0;1;2;3]
End

Theorem phi_permutation_lives_table:
  MAP phi_permutation_lives
    [[0;1;2];[0;2;1];[1;0;2];[1;2;0];[2;0;1];[2;1;0]] =
    [[["a2";"b2";"c2";"a1";"x2";"a0";"b0";"c0"];
      ["x0";"a2";"b2";"c2";"a1";"x2"];["x0";"a2";"b2";"c2"];["x0";"x2"]];
     [["a1";"a2";"b2";"c2";"a0";"b0";"c0"];
      ["x0";"a1";"a2";"b2";"c2"];["x0";"x2";"a1"];["x0";"x2"]];
     [["a2";"b2";"c2";"a0";"b0";"c0";"a1";"x2";"x0"];
      ["a2";"b2";"c2";"a0";"b0";"c0"];["x0";"a2";"b2";"c2"];["x0";"x2"]];
     [["a0";"b0";"c0";"a2";"b2";"c2";"a1";"x2";"x0"];
      ["a0";"b0";"c0";"a2";"b2";"c2"];["x2";"a0";"b0";"c0"];["x0";"x2"]];
     [["a1";"a0";"b0";"c0";"a2";"b2";"c2"];
      ["x2";"a1";"a0";"b0";"c0"];["x0";"x2";"a1"];["x0";"x2"]];
     [["a0";"b0";"c0";"a1";"x0";"a2";"b2";"c2"];
      ["x2";"a0";"b0";"c0";"a1";"x0"];["x2";"a0";"b0";"c0"];["x0";"x2"]]]
Proof
  EVAL_TAC
QED

(* All six orders fail exactly phi_operands_ready.  Even [0,2,1],
   whose entry liveness has neither x0 nor x2, has both names live after
   the prefix.  Thus no ready permutation calls for the conditional
   backedge input_vars_from probe.  This finite rejection is not a
   universal alias-exclusion theorem or a frozen-task counterexample. *)
