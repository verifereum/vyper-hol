Theory loadElimLatticeSoundHelpers
Ancestors
  loadElimDefs finite_map pred_set list

Definition le_lattice_holds_def:
  (le_lattice_holds P NONE <=> F) /\
  (le_lattice_holds P (SOME m) <=>
    !k vs. FLOOKUP m k = SOME vs ==> ?v. MEM v vs /\ P k v)
End

Theorem le_lattice_holds_empty[simp]:
  le_lattice_holds P (SOME FEMPTY)
Proof
  simp[le_lattice_holds_def]
QED

Theorem load_join_raw_lookup:
  FLOOKUP (load_join_raw a b) k = SOME vs ==>
  ?xs ys. FLOOKUP a k = SOME xs /\ FLOOKUP b k = SOME ys /\
    vs = operand_list_union xs ys
Proof
  simp[load_join_raw_def, FLOOKUP_FUN_FMAP] >>
  Cases_on `FLOOKUP a k` >> Cases_on `FLOOKUP b k` >>
  gvs[FLOOKUP_DEF, AllCaseEqs()]
QED

Theorem mem_operand_list_union[simp]:
  MEM v (operand_list_union xs ys) <=> MEM v xs \/ MEM v ys
Proof
  simp[operand_list_union_def, MEM_FILTER] >> metis_tac[]
QED

Theorem le_lattice_holds_join_left:
  le_lattice_holds P a ==> le_lattice_holds P (load_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[le_lattice_holds_def, load_join_def] >> rpt strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_lattice_holds_join_right:
  le_lattice_holds P b ==> le_lattice_holds P (load_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[le_lattice_holds_def, load_join_def] >> rpt strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_lattice_holds_singleton:
  le_lattice_holds P ll /\
  FLOOKUP (unwrap_load_lattice ll) k = SOME [v] ==> P k v
Proof
  Cases_on `ll` >> simp[le_lattice_holds_def, unwrap_load_lattice_def] >>
  metis_tac[MEM]
QED

Theorem le_lattice_holds_every_witness:
  le_lattice_holds P ll /\
  FLOOKUP (unwrap_load_lattice ll) k = SOME vs /\ EVERY Q vs ==>
  ?v. P k v /\ Q v
Proof
  Cases_on `ll` >> simp[le_lattice_holds_def, unwrap_load_lattice_def] >>
  metis_tac[EVERY_MEM]
QED

Theorem le_lattice_holds_transport:
  le_lattice_holds P ll /\ (!k v. P k v ==> Q k v) ==>
  le_lattice_holds Q ll
Proof
  Cases_on `ll` >> simp[le_lattice_holds_def] >> metis_tac[]
QED

Theorem le_lattice_holds_restrict:
  le_lattice_holds P (SOME m) ==>
  le_lattice_holds P (SOME (DRESTRICT m keys))
Proof
  simp[le_lattice_holds_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem le_lattice_holds_update_singleton:
  le_lattice_holds P (SOME m) /\ P k v ==>
  le_lattice_holds P (SOME (m |+ (k,[v])))
Proof
  simp[le_lattice_holds_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[MEM]
QED

(* A state-indexed semantic transport instance.  The two equalities are
   obligations of the operational boundary, not consequences of SSA syntax. *)
Theorem le_lattice_read_transport:
  le_lattice_holds
    (\k v. ?w. read k s = SOME w /\ eval_operand v s = SOME w) ll /\
  (!k. read k t = read k s) /\
  (!v. eval_operand v t = eval_operand v s) ==>
  le_lattice_holds
    (\k v. ?w. read k t = SOME w /\ eval_operand v t = SOME w) ll
Proof
  strip_tac >> irule le_lattice_holds_transport >>
  first_assum (irule_at Any) >> simp[]
QED

(* Semantic-contract audit (C1.3.3.3.2).

   Specification, NOT additional axioms or proved history-soundness claims.
   All formulas below are remaining obligations unless explicitly identified
   as an existing theorem.  The final theorem and frozen relations are intact.

   Concrete read/key interface:
     R(space,k,s) : bytes32 option
     LK_Op op: require eval_operand op s = SOME a; use address w2n a.
     LK_Loc ml: require memloc_runtime_region ml s = SOME (a,n),
       n = addr_space_word_scale space, and a < dimword(:256).
       This uses the existing shared runtime-region resolver; do not invent
       an independent interpretation of alloca-relative locations.
     Memory: SOME (mload a s).
     Storage: SOME (sload (n2w a) s).
     Transient: SOME (tload (n2w a) s).
     Calldata/Data: SOME (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP a bytes ++ REPLICATE 32 0w))), using respectively
       s.vs_call_ctx.cc_calldata and s.vs_data_section.
     Undefined key resolution gives NONE, not an arbitrary word.
   P(space,s,k,v) means exists w. R(space,k,s) = SOME w and
                                     eval_operand v s = SOME w.
   This is a proposed interface; address conversion, bounds and agreement
   with bp_get_read_location/write_location still require proofs.

   Boundary tests against the actual definitions:
   * Selected predecessor: le_lattice_holds_join_left/right retain one
     witness in the SAME state.  Iterating the appropriate join lemma can
     handle any selected incoming edge.  It does not transport to a new
     state; le_lattice_read_transport proves the elementary equality-based
     transport instance and exposes its two required preservation facts.
   * PHIs: eval_phis reads all inputs in the pre-PHI state and writes outputs
     in the result (venomExecSemantics:1604-1632). load_transfer does NOT
     invalidate keys or witnesses for PHI outputs; load_edge_transfer is
     identity. Thus unconditional post-PHI validity of P is not justified.
     On a backedge a raw Var p witness can denote the OLD value of a
     loop-carried PHI p; after entry p denotes its NEW value. An LK_Op (Var p)
     can similarly change address. wf_ssa includes availability at incoming
     edge endpoints, not an equality between those two dynamic values.
     Existing eval_phis_flookup_not_phi_output supplies preservation ONLY
     with the explicit no-output condition. This is an invariant-interface
     obstruction, not a verified counterexample to the frozen theorem.
   * Load insertion: transfer updates k to [Var out]. Need successful read
     agreement at k and eval_operand (Var out) post = SOME read_value, PLUS
     preservation of every retained key/witness (possibly out itself on a
     later iteration). Syntax of SSA alone does not discharge that last
     condition. Malformed operand/output load shapes retain the old map;
     fn_inst_wf is needed to exclude them on reached successful reads.
   * Store insertion: transfer first calls load_invalidate, then records the
     RAW val_op. Need eval_operand val_op post = eval_operand val_op pre and
     read-after-write at the resolved key. For each restricted retained key
     need non-alias => concrete read unchanged, and witness evaluation
     unchanged. Undefined write location clears the map; the subsequent
     singleton update still needs valid read-key resolution. Malformed store
     operands clear all facts. Restriction/update algebra is already proved.
   * Barrier: write_effects membership clears all facts (trivially sound).
     Otherwise the transfer retains the map. Need preservation of reads,
     key resolution and usable witnesses, not just absence of memory writes.
     Read-only rounds skip ALL barriers; calldata/data-section preservation
     must therefore be proved across ALL instructions including INVOKE.
     merge_callee_state restores these caller fields by record construction,
     but this alone is not the full INVOKE congruence theorem.
   * Unchanged instructions: may still redefine a recorded operand during
     loop re-execution. They require the same epoch-sensitive persistence
     argument as PHIs, even when their effect set is empty.

   Exact residual contracts (schematic space/read interface as specified):
   1. Key agreement: for every reached successful load/store at address a,
      R(space, computed_key, s) = SOME (concrete_read space a s).
      Requires normalization chain-validity, BP soundness and bounds; for
      LK_Loc additionally runtime alloca identity in the current epoch.
   2. Non-alias preservation: for every successful write s -> t and retained
      key k, valid runtime regions and the actual ma_may_alias filter imply
      R(space,k,t) = R(space,k,s). Must cover MSTORE8, copies and calls by
      clearing or sound alias disjointness, not merely MSTORE.
   3. Witness persistence: for each reached prefix and selected lattice
      witness v, eval_operand v t = eval_operand v s until its consumer,
      OR supply an epoch-indexed replacement. The universal version is
      unsupported; no theorem with that assertion has been added here.
   4. Parallel-PHI snapshot contract: incoming witnesses are evaluated in
      s_edge, before eval_phis. Each action selected by resolve_phi must
      capture that incoming value into its fresh output in t. Require key
      resolution/read agreement from s_edge to the eventual eliminated load
      and no redefinition of that fresh output on that segment.
      find_join_block's single-predecessor walk and origin membership alone
      do not establish this contract or exclude an intervening definition.

   History encoding decision:
     Do NOT use le_lattice_holds (P space current_state) for every df_at.
     A history must retain the current incoming-edge pre-PHI snapshot and
     definition epochs for raw Var witnesses AND LK_Op address variables.
     eval_phis starts new epochs for its outputs in one parallel event;
     successful ordinary instructions refresh epochs for their outputs.
     A selected multi-value consumer uses the inserted PHI snapshot, not
     evaluation of every raw operand in the current state. Singleton
     consumers need a separate proof that their unique alternative's epoch
     is current (or its value unchanged). This is the missing substantive
     theorem, not supplied by the algebraic interpretation above.

   Solver/population obligations:
     df_process_block joins OLD boundary with newly folded boundary; it does
     not overwrite the old value. Prove finite reachable operand/key universe,
     idempotence/absorption of ordered operand_list_union on reachable maps,
     a bounded strictly increasing measure when a process changes state,
     preservation of its invariant, and wl_deps_complete. These are the
     premises of existing df_analyze_fixpoint_forward, not consequences of
     wf_function alone. Establish the absorption consequence that computed
     stable output admits witnesses from a newly folded selected history.
     df_populate_inst performs a separate fold using stable boundaries, and
     FUNIONs per-block inst maps. Prove disjoint block-label/index domains,
     df_at equals the corresponding prefix fold, and ds_boundary unchanged.
     The entry joined value includes SOME FEMPTY, which annihilates any
     backedge facts at entry. This supplies the initial-history base, not
     post-PHI persistence at arbitrary other loop headers. Unreached NONE
     must never be treated as sound on a reached original history.

   Proposed decomposition for strategist review:
     A. Solver finite-universe/order/termination and population boundaries.
     B. Epoch-indexed original SSA execution availability/persistence lemma,
        with distinct pre-PHI and post-PHI phases.
     C. Concrete key/read and alias-filter soundness using existing BP and
        memory-pass runtime-region machinery (no duplicated resolver).
     D. Singleton witness-currentness and selected-edge generated-PHI capture
        and join-to-consumer persistence, before full history induction.
     None of A-D is certified by this audit. In particular, further progress
     needs a designed epoch/phase invariant, not more concrete IR examples.
*)
