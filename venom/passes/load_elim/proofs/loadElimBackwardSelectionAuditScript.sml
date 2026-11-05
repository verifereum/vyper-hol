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

(* Cut-to-suffix refresh audit (C1.P.3.3.10, supersedes missing-cut claims
   above). This is a statement proposal and interface inventory, NOT a
   semantic currentness theorem. Checked source signatures:

   loadElimDefinitionCuts:
     le_ordinary_definition_value_cut / le_phi_definition_value_cut exclude
     SOME [Var v] at index n / 0 respectively. Key counterparts give NONE
     for LK_Op (Var v), additionally requiring the built DFG.
   loadElimActualGeneration:
     le_analyze_singleton_step: singleton at SUC n implies same singleton
       at n OR le_transfer_generates at EL n.
     le_analyze_singleton_predecessor / le_analyze_singleton_exit: equality
       to the selected predecessor boundary / its full-block exit.
     le_analyze_phi_prefix_lookup: equality of unwrapped maps at index 0
       and phi_prefix_length.
     le_occ_prefix_singleton_generation: ONLY a MEM StepOcc generator;
       it supplies neither a last generator nor an uninterrupted suffix.
   loadElimOccurrence:
     le_occ_prefix_valid: EVERY (le_occ_valid C fn) es.
     le_occ_prefix_chain: le_occ_chain s0 es s.
     le_occ_prefix_suffix_lookup: for pre ++ e::suffix, no writes to v in
       suffix implies lookup_var v s = lookup_var v (le_occ_post e).
   loadElimOccurrenceCoverage.le_occ_prefix_route supplies an entry path;
   loadElimActualGeneration.le_occ_prefix_dfs supplies DFS membership for
   reached active points. Static reachability follows from the route via
   scfg_path_member_reachable, not from the occurrence number.

   Dependency caution: ActualGeneration imports THIS theory, and
   DefinitionCuts imports StaticGeneration, which imports ActualGeneration.
   Do not add either as an Ancestor here (cycle). This audit cites their
   source signatures only. Future checked suffix lemmas belong downstream
   of DefinitionCuts in a separate helper theory.

   Exact syntactic suffix proposal (no new history relation required):
   Under le_occ_prefix C fn s0 es i s, wf_function fn, fn_inst_wf fn,
   wf_ssa fn, le_configured_context ctx, entry label at s0, built DFG,
   the exact is_fixpoint premise of le_ordinary_definition_value_cut, and
     FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
       s.vs_current_bb s.vs_inst_idx)) key = SOME [op],
   prove existence of pre, bb, n, fuel, u, t, suffix with
     es = pre ++ StepOcc bb n fuel u t :: suffix /\
     le_transfer_generates ctx (EL n bb.bb_instructions) key op /\
     EVERY (\e. case e of
       StepOcc qb qn qfuel qu qt =>
         FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
           qb.bb_label qn)) key = SOME [op] /\
         FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
           qb.bb_label (SUC qn))) key = SOME [op] /\
         ~le_transfer_generates ctx (EL qn qb.bb_instructions) key op
     | PhiOcc qb qu qt =>
         FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
           qb.bb_label 0)) key = SOME [op]) suffix.
   Also require the singleton at generator index SUC n. This cannot be
   inferred from the generator signature alone: reachability and the
   successful step are what connect df_at n and df_at (SUC n).
   This is a stronger provenance statement than the existing MEM theorem.
   Prove it by backwards selection on the occurrence-prefix derivation,
   stopping at the FIRST generator met backwards, not by taking the last
   arbitrary generator returned from a static path. Selected boundary/exit
   equality stitches terminators to the next PHI batch; the terminator's
   SUC qn is the solver exit, not the next runtime state's index.

   Consequences of the proposed suffix, NOT yet proved:
   - If op = Var v then EVERY (\e. v NOTIN le_occ_writes e) suffix.
     For ordinary StepOcc use le_occ_valid_def to obtain qn bounds and
     lookup_block membership/label. Non-PHI active instructions need the
     wf block PHI-prefix exclusion. Apply ordinary value cut at qn.
     For PhiOcc, membership in le_phi_outputs gives a PHI di and its output;
     apply PHI value cut at zero, once for any output, using snapshot
     semantics. No ordering of individual PHI writes is used.
   - If key = LK_Op (Var a) then
       a NOTIN (EL n bb.bb_instructions).inst_outputs /\
       EVERY (\e. a NOTIN le_occ_writes e) suffix.
     The suffix follows from key presence and the two key cuts. At the
     generator itself use le_generator_key_variable_available and the
     strict same-block availability exclusion at its own index; this is
     distinct from applying the pre-generation key cut (which may be NONE
     there). le_occ_prefix_suffix_lookup then transports lookup_var a
     from the generator post-state. A Var witness is transported likewise.
     Literal witnesses need no writer. Label witnesses cannot be produced
     by configured valid stores/loads returning words; do not assume
     arbitrary Label evaluations are state-independent.

   Branch table for subsequent semantic induction:
     generating load   le_generating_load_key gives post-state key-read =
                       lookup_var out, with its explicit address and
                       no-self-address conditions to discharge.
     generating store  le_generating_store_key gives post-state key-read =
                       eval_operand raw value in post-state.
     retained load     no writes to witness/address on suffix; use read/
                       output semantics, not only transfer-list equality.
     retained store    le_retained_memory_key_read, storage_key_read,
                       transient_key_read require retained invalidation
                       membership, empty BP, wf aliases, absolute-key
                       shape, write-key address and explicit transport.
     barrier/call      in mutable spaces, clearing makes continued singleton
                       impossible unless this step regenerates it (select
                       that later refresh). In immutable spaces, analyze
                       actual effects with le_key_read operational lemmas;
                       do not infer all-space clearing from opcode CALL.
     PHI batch         suffix singleton at entry rules out witness/address
                       outputs. Other PHI outputs preserve selected operands
                       and all memory reads, by simultaneous evaluation.
     block transition  selected predecessor/exit equality bridges solver
                       points; index changes leave operand/read meaning
                       unchanged, not control fields. No same-block visit
                       uniqueness is needed.
     LK_Op (Lit w)     key address is state-independent.
     LK_Op (Label l)   a successful word-address generation is impossible;
                       establish this from configured instruction semantics.
     absolute LK_Loc   le_absolute_location_address gives fixed address.
                       Empty BP does NOT exclude this case.

   Loss/recreation: a singleton can disappear, or change to a different
   list, and later reappear. The selected suffix must start AFTER the last
   such recreation. Presence alone suffices for key-writer exclusion but
   not for value-list equality; use singleton selection for the witness.
   Equal list values do not certify non-clobbering: the transfer branch
   must still supply invalidation membership or generation. A store which
   rewrites the same singleton is a refresh, not a retention proof.

   Remaining semantic boundary: after the syntactic suffix/no-writer lemma,
   assemble one-step retained-key-read preservation with successful
   step_inst and the concrete load_transfer branch, maintaining
     le_key_read ctx.lctx_addr_space key (le_occ_after e) =
     eval_operand op (le_occ_after e)
   along that suffix (loadElimDefs.load_context has lctx_addr_space,
   distinct from its lctx_config selector).
   Semantic generation and retained-store lemmas expose sufficient local
   premises but no theorem currently discharges all these premises from
   arbitrary suffix steps. In particular origin equality alone does not
   expose retained invalidation membership. Keep .4 blocked until the
   strategist schedules these two interfaces. No theorem here asserts
   currentness, convergence, or frozen-target correctness.
*)
