Theory loadElimJoinPlacementAudit
Ancestors
  loadElimJoinPlacement loadElimOccurrenceCoverage loadElimSolverProvenance
  loadElimSingletonCurrentness loadElimPhiCapture cfgAnalysisProps
  finite_map

(* A finite path need not contain the backward walk's result. This is a
   graph-only interface test, NOT a counterexample to pass correctness. *)
Definition le_entry_escape_cfg_def:
  le_entry_escape_cfg =
    <|cfg_succs := FEMPTY;
      cfg_preds := FEMPTY |+ ("entry", ["outside"]);
      cfg_reachable := FEMPTY; cfg_dfs_post := []; cfg_dfs_pre := []|>
End

Theorem le_entry_escape_graph_probe:
  le_pred_path le_entry_escape_cfg ["entry"] /\
  find_join_block le_entry_escape_cfg {} "entry" = "outside" /\
  ~MEM (find_join_block le_entry_escape_cfg {} "entry") ["entry"] /\
  cfg_preds_of le_entry_escape_cfg "entry" = ["outside"]
Proof
  EVAL_TAC
QED

(* C1.P.4.2.2: entry-boundary and semantic-interface audit.

   Existing route interface (no second execution trace is needed):
   le_occ_prefix_route gives a nonempty is_fn_path, HD = s0.current_bb,
   LAST = s.current_bb from le_occ_prefix, wf_function, fn_inst_wf and
   fn_entry_label fn = SOME s0.current_bb.
   le_occ_route records only PhiOcc labels. The start rule contributes a
   singleton label; next contributes no label; block appends next.label.
   The block rule's successful active terminator gives fn_cfg_edge via
   le_active_terminator_edge. cfg_analyze_preserves_bb_succs and
   cfg_edge_symmetry_uncond convert that edge into predecessor membership.

   Candidate graph bridge (NOT YET PROVED):
     wf_function fn /\ is_fn_path fn xs ==>
       le_pred_path (cfg_analyze fn) xs.
   This uses fn_cfg_edge_def, member-block successor correctness, and
   unconditional edge symmetry. Combined with le_occ_prefix_route and
   le_find_join_path_escape it leaves EXACTLY
       ?p. cfg_preds_of (cfg_analyze fn) s0.vs_current_bb = [p]
   if the computed join is absent from the reached route.

   Structural-premise check:
   venomWf.wf_function_def (513--520) requires distinct labels, an entry,
   well-formed blocks, closed successors and distinct instruction IDs.
   It does NOT require that the entry has no predecessors.
   wf_ssa_def (624--625) is unique output definitions plus dominated uses;
   its def_dominates_uses rule is vacuous on literal-only instructions.
   No frozen premise states fn_entry_no_preds. The separate make-SSA
   fn_entry_no_preds predicate cannot silently be imported as a premise.
   The checked graph probe above exhibits the graph-level escape case;
   it deliberately makes NO claim about a computed load-analysis action.

   Analysis can potentially exclude the escape for MULTIVALUE consumers,
   but graph placement alone cannot. le_analyze_multivalue_origin gives
   exact propagation to index zero within a block (with the fixpoint,
   DFS reachability, lookup and instruction-index bound premises).
   le_analyze_entry_join rewrites this point to df_joined_val. At the
   function entry the latter joins SOME FEMPTY with predecessor values;
   le_empty_join_no_lookup's proof is the relevant empty-lookup argument.
   However le_analyze_selected_predecessor and le_analyze_selected_exit
   provide ONLY subset inclusion, not preservation of the whole multivalue
   list along the unique-predecessor chain. A singleton exit may be a
   subset of a multivalued accumulated boundary. Thus the existing source
   does not yet discharge entry escape by backwards multivalue transport.
   A suitable next interface must either certify no-multivalue for the
   whole backwards singleton chain to entry (including accumulated old
   boundaries), or select a genuine splitting join from solver provenance.
   Neither property is asserted as proved by this audit.

   Incoming snapshot mapping and remaining semantic boundaries:
   For a reached PhiOcc bb u p, le_occ_valid gives lookup_block and
   eval_phis u bb.instructions = OK p. The immediately preceding StepOcc
   of a block transition gives the incoming CFG edge. Its post-state is u;
   step_inst sets u.prev_bb to the source label on that transition.
   These discharge capture's edge membership/prev_bb only after a
   transition-specific control-flow theorem; the start PhiOcc has no
   preceding transition and must be kept separate.
   le_compute_phi_action_selected supplies a static boundary SOME [Var v]
   for that predecessor, not lookup_var v u = SOME w.
   le_occ_prefix_singleton_current currently applies at an ACTIVE ordinary
   instruction's df_at point, not df_boundary or a completed block exit.
   Its additional premises are configured ctx, built DFG, empty BP queries,
   analyzed aliases, entry-aligned initial state, solver fixpoint, and DFG
   soundness at every StepOcc pre-state. They are not optional assumptions
   available merely from compute_phi_action.
   Candidate selected-boundary signature (NOT YET PROVED), under all the
   shared context/fixpoint/DFG hypotheses of singleton_current above:
     le_occ_prefix C fn s0 es i s /\
     is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
     ~u.vs_halted /\
     FLOOKUP (unwrap_load_lattice
       (df_boundary NONE (load_analyze ctx fn) s.vs_current_bb)) key =
       SOME [Var v] ==>
     le_key_read ctx.lctx_addr_space key u = lookup_var v u.
   This is selected-boundary currentness at a completed terminator,
   using boundary absorption,
   nonempty/support singleton selection, and an exit-point extension of
   the existing currentness theorem. The output should directly relate
   lookup_var v u to le_key_read space key u in the PRE-PHI snapshot.
   Capture in the transformed batch also requires successful transformed
   eval_phis, action-output distinctness and predecessor distinctness.
   Finally captured-output persistence and key-read persistence to the
   consumer are separate unresolved obligations; original PhiOcc p is
   not the transformed state to which le_compute_phi_action_capture applies.
*)
