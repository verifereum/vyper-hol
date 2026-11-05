Theory loadElimBackwardSelectionAudit
Ancestors
  loadElimDefs loadElimKeyShapeInvariant loadElimNonempty
  loadElimSupportHelpers loadElimGeneratedSupport loadElimConvergence
  loadElimPopulation loadElimSolverProvenance loadElimLastWriter
  venomEffects venomInst finite_map list

(* PHI output changes are deliberately invisible to this transfer. This
   fact is a proof-interface audit, not a claim of semantic persistence. *)
Theorem le_configured_phi_transfer:
  le_configured_context ctx /\ inst.inst_opcode = PHI ==>
  load_transfer ctx inst ll = SOME (unwrap_load_lattice ll)
Proof
  simp[le_configured_context_def] >> strip_tac >> gvs[] >>
  simp[load_transfer_def, memory_config_def, storage_config_def,
       transient_config_def, dload_config_def, calldataload_config_def,
       write_effects_def, empty_effects_def]
QED

Theorem le_distinct_singleton_selection:
  ALL_DISTINCT ws /\ ws <> [] /\ (!x. MEM x ws ==> MEM x [v]) ==>
  ws = [v]
Proof
  Cases_on `ws` >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `t` >> gvs[] >> metis_tac[]
QED

(* Backward-selection audit (semantic bridge NOT yet proved).

   Branch                 Certified syntactic boundary
   load generation        le_transfer_generates_lookup: singleton [Var out]
   store generation       same boundary: singleton [raw value operand]
   retained load/store    le_transfer_lookup_origin: exact old list, or singleton
   effect barrier         load_transfer clears to FEMPTY (store-enabled space)
   block-entry PHI batch  le_configured_phi_transfer: preserves all bindings

   At joins, le_analyze_selected_predecessor / selected_exit only give
   membership inclusion. le_analyze_lists_nonempty supplies nonemptiness;
   le_analyze_boundary_supported and le_analyze_point_supported supply
   ALL_DISTINCT via le_lattice_supported_def. Together with
   le_distinct_singleton_selection these justify singleton list equality.
   Actual-path population is not missing: le_analyze_boundary_some and
   le_analyze_at_some apply on cfg_dfs_pre, and le_occ_prefix_route supplies
   a CFG path for the actual occurrence trace. Old-boundary accumulation
   is handled only syntactically by le_analyze_boundary_absorbs and the
   supported/nonempty invariants; it does not prove semantic persistence.

   Remaining exact proof-interface obligations:
   1. For a reached ordinary load with analysis lookup SOME [Var v], show
      a preceding writing member of that SAME occurrence prefix. The
      le_frame_use_last_writer consumer cannot be applied directly: v is
      the replacement witness, not necessarily an original operand!
      le_occ_prefix_last_writer applies once this writer existence is
      supplied. A possible sufficient STATIC bridge is def_on_all_paths
      fn bb (SOME i) v for singleton witnesses, using the lookup at i and
      wf_ssa/wf_function. Do not claim this for multi-valued alternatives.
   2. Given such a writer, rule out a later change of v between selected
      generation and use, or select a refreshed generation. Static SSA
      identity does not order visits. If v is the load's own output, that
      step refreshes its key. If v is a store's raw operand, its distinct
      defining instruction need not refresh memory facts at all.
   3. LK_Op (Var a): a is an original address operand only before DFG
      normalization. Need a def/use bridge for variables returned by
      normalize_operand, followed by the same no-intervening-definition
      argument for a. Semantic generation alone does not transport a.
   4. LK_Loc: the original wrapper empty-BP/absolute-key theorems can
      exclude this branch under their proved premises. For generalized
      arbitrary BP contexts, allocation interpretation persistence is an
      additional obligation and is NOT certified by this audit.

   Hard loop: entry -> header(PHI v) -> use -> generation -> backedge.
   A fact depending on the PHI result cannot simply be transported over
   header: analysis PHI transfer is identity while runtime writes v.
   If entry has no such fact, meet excludes it at header, even if the
   backedge has it. Establishing this exclusion in general requires a
   static cut/provenance lemma: all paths into v's defining block must
   lack the dependent fact unless a generation exists before that
   definition. SSA operand dominance should exclude that generation,
   except a defining load itself (which refreshes). This static cut lemma
   is currently missing. The same issue applies to changing addresses.
   This is an unproved bridge, NOT a checked task counterexample.
*)
