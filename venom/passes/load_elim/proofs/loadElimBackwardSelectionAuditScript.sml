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

(* Definition-cut interface audit (C1.P.3.3.3).

   These are CANDIDATES, not proved facts. The shared solver premise below
   means exactly the is_fixpoint premise of le_occ_prefix_singleton_generation;
   contexts additionally satisfy le_configured_context ctx.

   Value cut candidate, for a reachable defining instruction:
     wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
     MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
     MEM v (EL n bb.bb_instructions).inst_outputs /\
     MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\ <solver premise>
     ==>
     FLOOKUP (unwrap_load_lattice
       (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key <>
       SOME [Var v].
   For a PHI this must also hold at block index zero, before the batch.
   The candidate is stronger than writer availability: it speaks about a
   STATIC point, independently of which dynamic visit reaches that point.

   Missing static path boundary:
   Backward singleton selection must be iterated over an arbitrary finite
   is_fn_path from entry to this point, returning a generation in a previous
   block or in TAKE n bb.bb_instructions. No successful execution of that
   path is needed or justified. le_occ_prefix_singleton_generation cannot
   supply this theorem: it requires successful steps/PHI evaluation.
   def_on_all_paths is precisely the available static interface for raw
   store operands, but not yet for analysis witnesses.

   Branch audit for a path ending at the FIRST visit to the defining block:
   - Load generation of Var v writes v. ssa_form_output_unique identifies
     its static instruction with the definition. It cannot be on the strict
     prefix to that definition (requires occurrence/index uniqueness too).
   - Store generation of Var v uses Var v as a raw operand, not normalized.
     def_dominates_uses -> def_available_at supplies dominance and same-block
     strict ordering. A path prefix to a store before the first definition
     would contradict this availability, using SSA output uniqueness.
   - PHI definition: cut at index zero, not between individual PHIs.
     No PHI generates a binding; le_configured_phi_transfer preserves it.
     Static uniqueness separates any generating load from a PHI definition.
     Ordinary store operands are subject to dominance as above, even when
     v's definition is a PHI. No sequential PHI-value argument is valid.
   - Ordinary definition: cut immediately before its instruction; a defining
     load then refreshes its own singleton. Other definitions do not refresh
     the fact, so their pre-point exclusion is necessary.
   - Later visits: once the STATIC cut is proved, apply it at each matching
     defining instruction/PHI block occurrence. Writer availability alone
     does not establish this reuse. Persistence still needs a suffix chosen
     after the most recent refresh and the local semantic transfer lemmas.

   Address audit:
   normalize_operand_eval_proof (dfgCorrectnessProof) has exact interface
     dfg_assigns_sound dfg s ==>
     eval_operand (normalize_operand dfg visited op) s = eval_operand op s.
   This discharges generation-time address agreement in
   le_empty_read_key_address / le_empty_write_key_address. It also permits
   transform-time comparison of normalized values. le_chain_valid_eval is
   an existing weaker, chain-local alternative; do not duplicate either.
   It does NOT prove equality between different states. In particular,
   even dfg_assigns_sound at both endpoints only relates each normalized
   address to its raw address at THAT endpoint. A cross-state normalized
   key transport lemma still needs operand persistence (or an independent
   semantic reason for raw-address equality).

   Address cut candidate replaces the last line of the value candidate by
     FLOOKUP (unwrap_load_lattice
       (df_at NONE (load_analyze ctx fn) bb.bb_label n)) (LK_Op (Var v)) = NONE.
   This needs backward KEY-presence provenance, not merely singleton-value
   provenance: generators of this key may carry DIFFERENT value lists on
   different incoming paths. At a generator Var v is normalize_operand's
   result, not necessarily an original operand. The missing static bridge
   is normalization-chain def/use availability for the built DFG; semantic
   normalization equality alone does not supply that syntactic bridge.
   For LK_Op (Lit w), evaluation is state-independent; LK_Op (Label l)
   cannot give a successful word address. For LK_Loc, see correction below.

   Correction to the older LK_Loc paragraph above: empty BP does NOT exclude
   all LK_Loc keys. A literal address can produce an absolute fixed location.
   le_step_preserves_analyze_empty uses fn_inst_wf, le_step_preserves,
   bp_assigns_stable and initial dfg_assigns_sound to obtain empty original
   BP queries; no-ALLOCA preservation handles later rebuilt BP analyses.
   le_analyze_absolute_keys then restricts retained LK_Loc keys to
   le_absolute_key: ml_alloca = NONE, fixed bounded offset, fixed word size.
   le_absolute_location_address already proves address persistence for this
   remaining branch. What is excluded is allocation-relative LK_Loc, not
   LK_Loc itself. No normalized-variable dominance is required for absolute
   locations. This is a proof-interface correction, not task falsehood.
*)
