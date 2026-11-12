(* Contract diagnostic only: this does not refute target_walk_frame.
   The existing module witness uses NONE-mode source outcomes, whereas
   stmt_state_rel requires SOME-mode outcomes. No choice of compiler,
   context, function or initial Venom state can repair that mismatch for
   this exact source state. In particular target_sim is vacuous here. *)
Theory targetPureWalkContractProbe
Ancestors
  targetPureWalkModuleProbe targetPlaceSimDefs exprLoweringProps
  loweringStateRelDefs

Theorem module_probe_no_related_initial_state:
  !ctx func cenv s0.
    ~stmt_state_rel ctx func cenv module_probe_cx module_probe_state s0
Proof
  simp[stmt_state_rel_def, state_rel_def, module_probe_state_def,
       vyperStateTheory.empty_state_def]
QED

(* This is the universally quantified target_sim itself, not a single run.
   It holds only because its initial-state premise is impossible. Thus it
   cannot complete a full-antecedent counterexample for this witness. *)
Theorem module_probe_vacuous_target_sim:
  !ctx func cenv env.
    target_sim ctx func cenv module_probe_cx env
      module_probe_target module_probe_state
Proof
  simp[target_sim_def, module_probe_no_related_initial_state]
QED
