Theory o1MakeSsaTreeBoundary
Ancestors
  o1SourceUnitCheck makeSsaCurrentDefs venomWf dominatorAnalysisProps
  cfgAnalysisProps list

(* These are adequacy diagnostics, not a universal tree certificate. *)
Definition tree_probe_stops_def:
  tree_probe_stops = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []] |>;
    <| bb_label := "dead"; bb_instructions := [mk_inst 1 STOP [] []] |>]
End

Definition tree_probe_cycle_def:
  tree_probe_cycle = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []] |>;
    <| bb_label := "dead1"; bb_instructions := [mk_inst 1 JMP [Label "dead2"] []] |>;
    <| bb_label := "dead2"; bb_instructions := [mk_inst 2 JMP [Label "dead1"] []] |>]
End

Theorem tree_probe_stops_wf:
  wf_function tree_probe_stops
Proof
  EVAL_TAC
QED

Theorem tree_probe_cycle_wf:
  wf_function tree_probe_cycle
Proof
  EVAL_TAC
QED

Theorem tree_probe_stops_tree:
  current_dom_tree tree_probe_stops = DNode "entry" []
Proof
  EVAL_TAC
QED

Theorem tree_probe_cycle_tree:
  current_dom_tree tree_probe_cycle = DNode "entry" []
Proof
  EVAL_TAC
QED

Theorem tree_probe_cycle_idoms:
  MAP (idom_of (dom_analyze (cfg_analyze tree_probe_cycle) tree_probe_cycle))
    ["entry";"dead1";"dead2"] = [NONE;SOME "dead2";SOME "dead2"]
Proof
  EVAL_TAC
QED

Definition tree_probe_chain_def:
  tree_probe_chain = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "live"] []] |>;
    <| bb_label := "live"; bb_instructions := [mk_inst 1 STOP [] []] |>;
    <| bb_label := "dead"; bb_instructions := [mk_inst 2 STOP [] []] |>]
End

Theorem tree_probe_chain_wf:
  wf_function tree_probe_chain
Proof
  EVAL_TAC
QED

Theorem tree_probe_chain_tree:
  current_dom_tree tree_probe_chain =
    DNode "entry" [DNode "live" [DNode "dead" []]]
Proof
  EVAL_TAC
QED

Theorem tree_probe_chain_reachability:
  MAP (cfg_reachable_of (cfg_analyze tree_probe_chain))
    ["entry";"live";"dead"] = [T;T;F]
Proof
  EVAL_TAC
QED

(* A tree can include an unreachable label; it is not legitimate to use
   tree membership as a reachability premise at a later analysis theorem. *)
Theorem tree_probe_has_unreachable_tree_label:
  wf_function tree_probe_chain /\
  MEM "dead" (dom_tree_postorder (current_dom_tree tree_probe_chain)) /\
  ~cfg_reachable_of (cfg_analyze tree_probe_chain) "dead"
Proof
  simp[tree_probe_chain_wf, tree_probe_chain_tree, dom_tree_postorder_def] >>
  EVAL_TAC
QED

Theorem tree_probe_postorders:
  dom_tree_postorder (current_dom_tree tree_probe_stops) = ["entry"] /\
  dom_tree_postorder (current_dom_tree tree_probe_cycle) = ["entry"] /\
  dom_tree_postorder (current_dom_tree tree_probe_chain) = ["dead";"live";"entry"]
Proof
  simp[tree_probe_stops_tree, tree_probe_cycle_tree, tree_probe_chain_tree,
       dom_tree_postorder_def]
QED

(* Interface audit for the future universal adapter:
   - dominated_iff_idom needs wf_function and membership of BOTH labels.
   - idom_is_immediate additionally needs reachability of the CHILD.
   - idom_exists needs a reachable non-entry label.
   - dominates_reachable transports reachability backwards from a reachable
     dominated node, not forwards to every dominated_of child.
   Thus reachable-child ancestor chains can use the exported dominance
   theorems, but arbitrary tree-child edges cannot. In the disconnected
   cycle the raw idom graph even contains the self-edge dead2 -> dead2;
   it is not traversed from entry in this fixture. Global tree distinctness
   still needs a rooted functional-parent argument, not global idom rank.
   No universal coverage/distinctness conclusion is inferred from these
   diagnostic computations. *)
