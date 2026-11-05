Theory loadElimJoinPlacementAudit
Ancestors
  loadElimJoinPlacement loadElimOccurrenceCoverage loadElimSolverProvenance
  loadElimSingletonCurrentness loadElimPhiCapture cfgAnalysisProps
  loadElimPhiProbes loadElimJoinProps loadElimDefs cfgDefs dfAnalyzeDefs finite_map

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

   Graph bridge (subsequently proved as le_fn_path_pred_path):
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

(* Isolated update tests: arbitrary old boundaries are intentionally NOT
   claimed reachable from init_df_state. They test the algebraic interface. *)
Theorem le_audit_entry_injection:
  df_joined_val Forward NONE load_join load_edge_transfer ctx
    (SOME ("entry", SOME FEMPTY)) le_entry_escape_cfg st "entry" =
      SOME FEMPTY
Proof
  simp[df_joined_val_def] >>
  Cases_on `df_boundary NONE st "outside"` >>
  simp[load_edge_transfer_def, le_entry_escape_cfg_def,
       cfg_preds_of_def, fmap_lookup_list_def, load_join_def,
       load_join_raw_def, FUN_FMAP_EMPTY, FLOOKUP_UPDATE]
QED

Theorem le_audit_old_boundary_accumulation:
  df_boundary NONE
    (df_process_block Forward NONE load_join load_transfer load_edge_transfer
      ctx NONE le_entry_escape_cfg [] "entry"
      <| ds_inst := FEMPTY; ds_boundary := FEMPTY |++
          [("outside", diamond_values [Var "y"]);
           ("entry", diamond_values [Var "x"])] |>) "entry" =
    diamond_values [Var "x"; Var "y"]
Proof
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF]
QED

Theorem le_audit_entry_resets_old_boundary:
  df_boundary NONE
    (df_process_block Forward NONE load_join load_transfer load_edge_transfer
      ctx (SOME ("entry", SOME FEMPTY)) le_entry_escape_cfg [] "entry"
      <| ds_inst := FEMPTY; ds_boundary := FEMPTY |++
          [("outside", diamond_values [Var "y"]);
           ("entry", diamond_values [Var "x"])] |>) "entry" = SOME FEMPTY
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY] >> EVAL_TAC
QED

(* C1.P.4.2.3.3: accumulated-boundary diagnostic.

   Exact implementation equations (dfAnalyzeDefs):
   init_df_state initializes every label boundary to NONE; df_analyze then
   updates only entry to SOME FEMPTY. df_process_block computes joined via
   predecessor boundaries (load_edge_transfer is identity), folds instructions,
   and replaces boundary b by load_join (old boundary b) (fresh exit b).
   An equal result leaves the state unchanged. No instruction values are
   populated until AFTER worklist convergence; df_populate_inst does not
   change boundaries. load_analyze supplies precisely this Forward solver.
   le_solver_entry_init / le_solver_iterate_supported validate the actual
   initial state and reachable solver states for finite-support invariants;
   those invariants do not express the operand-origin relation needed here.

   Checked tests, reusing existing tests rather than duplicating them:
   * entry_backedge_analysis_probe: actual entry with a backedge and SLOAD
     has empty index-zero input and no generated PHI actions. Its singleton
     load output does not turn the entry input into a multivalue fact.
   * diamond_step2_probe through diamond_step8_probe: actual worklist runs
     the join and its unique-predecessor successor with [y] first, then
     revisits the join after the other arm, obtaining [y;x]. The old y
     survives accumulation; the successor is subsequently updated to [y;x].
     diamond_load_input_probe / diamond_actions_exact_probe certify the
     resulting multivalue consumer and the chosen join.
   * loop_step2_probe / loop_header_stable_probe: the loop header's load
     always overwrites with [x], although its input later joins [a] and [x].
     Thus accumulated header exits remain [x], not the header input union.
     loop_iteration_probe and loop_analysis_probe certify actual convergence.
   * le_audit_old_boundary_accumulation above: an ARBITRARY old [x] and
     fresh unique-predecessor exit [y] yield [x;y]. This is deliberately not
     a reachable-state claim. It refutes the unconditional local rule
     'multivalue boundary implies multivalue fresh exit'. Entry injection
     and resetting the old boundary are tested separately above.

   Candidate induction interface (PROPOSAL, NOT A PROVED INVARIANT):
   For each fixed key, classify a whole static block fold, for ALL inputs,
   as either (1) always overwriting with the SAME singleton [op], (2) always
   deleting the key, or (3) preserving exactly its input lookup. This is
   stronger than the existing per-execution retain/delete/generate disjunction:
   the classification must be independent of solver state. All transfer
   branches in load_transfer are syntactic, so the last overwrite/deletion
   determines the class. NONE input must remain a separate case, because
   unwrap NONE is empty, and even identity instructions wrap the result.

   Needed two-time solver fact: if a later boundary has a key, each earlier
   SOME boundary has that key, and every earlier operand belongs to the
   later list. Old NONE contributes no operands; after a key disappears
   from SOME it cannot return, because load_join intersects key domains.
   For a preserving single-predecessor block b with predecessor p, collect
   the operands contributed at every processing of b. Whenever the CURRENT
   boundary p contains the key, each such contribution is contained in it,
   using the two-time fact. Initially b is NONE (or empty at entry).
   At the final fixpoint, a retained key at b forces the fresh exit and p
   to contain the key (and p <> NONE on reached nonempty blocks). Hence
   set(boundary b[key]) SUBSET set(boundary p[key]). This is the REVERSE
   inclusion missing from the existing absorption interfaces. A constant
   singleton block instead has only that singleton throughout all updates.

   Proposed placement use: trace two DISTINCT operands back along the
   unique-predecessor chain. Constant/deleting blocks cannot carry both;
   preserving blocks pass both backwards by the reverse inclusion above.
   Entry input is always empty, even with a backedge; a constant entry
   exit is at most singleton. Therefore the backwards chain cannot escape
   through entry while carrying both operands. Existing finite-route
   placement then puts find_join_block on the reached route. This argument
   must use distinct operands, NOT merely list length > 1 unless the
   solver's no-duplicate invariant has been established.

   Missing certification: the static uniform-fold classification and the
   two-time/collected-contributions relation have NOT been proved. The
   existing le_solver_inv support/rank invariant does not imply either.
   In particular absorption alone cannot establish the reverse inclusion,
   as the arbitrary-old-boundary computation demonstrates. A strategist
   must authorize a suitable reachable-iteration interface before semantic
   integration. None of these tests is a full-premise counterexample to
   the frozen correctness theorem. No second runtime history is proposed.
*)
