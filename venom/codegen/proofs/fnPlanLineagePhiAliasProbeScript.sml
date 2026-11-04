Theory fnPlanLineagePhiAliasProbe
Ancestors
  fnPlanLineagePhiSlots stackPlanGen livenessDefs venomWf

Definition alias_phi0_def:
  alias_phi0 = mk_inst 0 PHI
    [Label "entry"; Var "a"; Label "back"; Var "b"] ["x"]
End

Definition alias_phi1_def:
  alias_phi1 = mk_inst 1 PHI
    [Label "entry"; Var "c"; Label "back"; Var "x"] ["y"]
End

Theorem alias_readiness_local:
  phi_uses_disjoint [alias_phi0; alias_phi1] /\
  EVERY (\phi. EVERY (\v. ~MEM v ([]:string list)) (inst_uses phi))
    [alias_phi0; alias_phi1] /\
  MEM "x" (inst_uses alias_phi1) /\ MEM "x" alias_phi0.inst_outputs /\
  liveness_transfer [] alias_phi1 [] = ["c";"x"]
Proof
  EVAL_TAC
QED

(* With slot 0 on top, renaming it to x supplies an equal query hit on
   both edges, even though it shadows a different incoming slot below. *)
Theorem alias_first_stage:
  generate_phi_plan alias_phi0 ["c";"x"] F
    ((init_plan_state 0) with ps_stack := [Var "c"; Var "a"]) =
    ([SOPoke 0 (Var "x")],
     (init_plan_state 0) with ps_stack := [Var "c"; Var "x"]) /\
  generate_phi_plan alias_phi0 ["c";"x"] F
    ((init_plan_state 0) with ps_stack := [Var "x"; Var "b"]) =
    ([SOPoke 0 (Var "x")],
     (init_plan_state 0) with ps_stack := [Var "x"; Var "x"])
Proof
  EVAL_TAC
QED

Theorem alias_second_stage:
  FST (generate_phi_plan alias_phi1 [] F
    ((init_plan_state 0) with ps_stack := [Var "c"; Var "x"])) =
  FST (generate_phi_plan alias_phi1 [] F
    ((init_plan_state 0) with ps_stack := [Var "x"; Var "x"])) /\
  (SND (generate_phi_plan alias_phi1 [] F
    ((init_plan_state 0) with ps_stack := [Var "c"; Var "x"]))).ps_stack = [Var "c"] /\
  (SND (generate_phi_plan alias_phi1 [] F
    ((init_plan_state 0) with ps_stack := [Var "x"; Var "x"]))).ps_stack = [Var "x"]
Proof
  EVAL_TAC
QED

Definition self_phi_def:
  self_phi = mk_inst 2 PHI
    [Label "entry"; Var "a"; Label "back"; Var "x"] ["x"]
End

Theorem self_phi_dead_stage:
  phi_uses_disjoint [self_phi] /\
  generate_phi_plan self_phi [] F
    ((init_plan_state 0) with ps_stack := [Var "a"]) =
  generate_phi_plan self_phi [] F
    ((init_plan_state 0) with ps_stack := [Var "x"])
Proof
  EVAL_TAC
QED

Theorem self_phi_live_rejected_by_ready_clause:
  ~EVERY (\v. ~MEM v ["x"]) (inst_uses self_phi) /\
  ~phi_uses_disjoint [self_phi; alias_phi1]
Proof
  EVAL_TAC
QED

Theorem alias_entry_slots:
  liveness_transfer [] alias_phi0
    (liveness_transfer [] alias_phi1 []) = ["c";"a";"b"] /\
  input_vars_from "entry" [alias_phi0;alias_phi1] ["c";"a";"b"] = ["c";"a"] /\
  input_vars_from "back" [alias_phi0;alias_phi1] ["c";"a";"b"] = ["x";"b"]
Proof
  EVAL_TAC
QED

(* First-entry witness dependency report (no global theorem claimed).

   Existing reusable material found:
   - dominatorProofs.exists_pred_not_dominated: wf_function fn,
     entry_block fn = SOME eb, cfg_reachable_of (cfg_analyze fn) lbl,
     lbl <> eb.bb_label imply a reachable CFG predecessor p with
     ~dominates (dom_analyze (cfg_analyze fn) fn) lbl p.
     This is already the analyzed-dominance first-entry boundary; do not
     duplicate it. It is NOT yet expressed using venomWf.fn_dominates.
   - removeUnusedSsaProofs has LOCAL rtc_to_fn_path, is_fn_path_prefix,
     is_fn_path_init, is_fn_path_last_edge, ssa_unique_output_block.
     Their existing statements/proofs are reuse candidates for exporting
     an appropriately shared boundary, not additional local duplicates.
   - fn_dominates_def quantifies exactly is_fn_path from fn_entry_label.
     def_available_at_def supplies a defining instruction in a block
     fn_dominating the endpoint. ssa_form gives flattened output uniqueness.
   - livenessAnalysisProps.live_vars_at_uses and live_vars_at_propagate
     require wf_function, analyzed DFS-pre membership, lookup and bounds.
     The latter additionally requires absence from the preceding inst_defs.

   Proposed bridge/witness interfaces (UNPROVED):
   1. wf_function fn /\ entry_block fn = SOME eb /\
      cfg_reachable_of (cfg_analyze fn) lbl /\ lbl <> eb.bb_label ==>
      ?p. MEM p (cfg_preds_of (cfg_analyze fn) lbl) /\
          cfg_reachable_of (cfg_analyze fn) p /\ ~fn_dominates fn lbl p.
      Prefer a bridge from analyzed dominates to fn_dominates if one can
      be exported; alternatively reuse existing generic path lemmas.
   2. ssa_form fn /\ MEM bb fn.fn_blocks /\ MEM pb fn.fn_blocks /\
      ~fn_dominates fn bb.bb_label pb.bb_label /\
      def_available_at fn pb NONE v ==>
      EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions.
      This follows by unique definition BLOCK, not merely instruction;
      no premise asserting fresh dynamic names is required.
   3. codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
      cfg_reachable_of (cfg_analyze fn) lbl /\
      i < LENGTH (collect_phis bb.bb_instructions) ==>
      ?v. MEM v (inst_uses (EL i (collect_phis bb.bb_instructions))) /\
          MEM v (live_vars_at (liveness_analyze fn) lbl 0).
      Entry has no PHIs by block_entries_ready. For non-entry use (1),
      named-edge coverage in phi_edge_uses_wf, then (2), uses-at-i and
      backward propagation with no kills. Need collect_phis/EL-prefix
      alignment and reachable-to-DFS-pre bridge. Finally disjoint PHI
      operand classes connect this witness to its exact op_map index.

   Temporal outcome of checked local stages:
   alias_phi0's output x is a later PHI input, yet pairwise incoming sets
   remain disjoint and all incoming names are dead after the prefix. The
   entry live list [c,a,b] yields slots [1,0]. Renaming top slot 0 to x
   shadows slot 1 for BOTH edges, so the second PHI hits equal depths and
   emits equal operations. After deleting its dead output, the remaining
   bottom cell is c on entry, x on back. Thus an invariant demanding that
   PHI prefix completion gives identical whole suffixes is too strong;
   it must be able to retire edge-dependent dead slots into residuals.
   These are locally permitted alias clauses/stages, NOT certification of
   a complete ready function or a counterexample to the frozen theorem.

   The self-PHI check allows a loop-carried self input when its output is
   dead. If x is live after the prefix the incoming-dead readiness clause
   rejects it; if a later PHI reads x the incoming-disjoint clause rejects
   that combination. Equal entry query positions alone do not capture the
   reason for these temporal restrictions.

   Candidate temporal certificate: an ordered sequence of slots each either
   an unresolved edge-realized class, a common renamed operand, or a retired
   dead cell. A PHI may query a common renamed slot rather than its original
   class. Track equal predicate vectors over all non-retired physical slots,
   and require a shielding hit before unrestricted residuals; explicitly
   prove retirement/deletion preserves future query shielding. No assertion
   of spill alignment, window bounds or global preservation follows here.
*)
