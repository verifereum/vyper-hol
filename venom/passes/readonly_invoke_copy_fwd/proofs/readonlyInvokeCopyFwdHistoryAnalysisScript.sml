(* Checked boundary for the fixed-analysis audit.  Unknown INVOKE writes
   prevent any intervening call, independently of runtime BP soundness. *)
Theory readonlyInvokeCopyFwdHistoryAnalysis
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdProtectionLifetime
  memAliasProps memAliasDefs venomEffects basePtrDefs memLocDefs venomInst
  readonlyInvokeCopyFwdPlan invokeCopyFwdCommonDefs list

Theorem ricf_event_no_intervening_invoke:
  ricf_event_ok e bb /\ wf_alias_sets e.rfe_ctx.icf_aliases /\
  (bp_get_read_location e.rfe_ctx.icf_bp
    (ricf_event_copy e bb) AddrSp_Memory).ml_size <> SOME 0 /\
  ricf_selected_position e bb j /\ e.rfe_index < k /\ k < j ==>
  (EL k bb.bb_instructions).inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >>
  `Eff_MEMORY IN write_effects (EL k bb.bb_instructions).inst_opcode` by
    simp[write_effects_def, all_effects_def] >>
  `~ma_may_alias e.rfe_ctx.icf_aliases
    (bp_get_read_location e.rfe_ctx.icf_bp (ricf_event_copy e bb) AddrSp_Memory)
    (bp_get_write_location e.rfe_ctx.icf_bp
      (EL k bb.bb_instructions) AddrSp_Memory)` by
    (irule ricf_event_intervening_alias_exclusion >> metis_tac[]) >>
  gvs[ma_may_alias_iff, bp_get_write_location_def,
      is_raw_fmp_opcode_def, may_overlap_def, ml_undefined_def]
QED

(* Only DFG is rebuilt: well-formed alias sets come from the original fn,
   and opcode preservation suffices to transport this call exclusion. *)
Theorem ricf_located_event_no_intervening_source_invoke:
  ricf_located_event (icf_build_ctx fm fs rma fn) fn log
    round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  (bp_get_read_location e.rfe_ctx.icf_bp
    (ricf_event_copy e current) AddrSp_Memory).ml_size <> SOME 0 /\
  ricf_selected_position e current j /\ e.rfe_index < k /\ k < j /\
  k < LENGTH (EL b fn.fn_blocks).bb_instructions ==>
  (EL k (EL b fn.fn_blocks).bb_instructions).inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule ricf_block_edit_EL >> strip_tac >>
  `wf_alias_sets e.rfe_ctx.icf_aliases` by
    simp[icf_build_ctx_def, memory_alias_analyze_def, ma_analyze_wf] >>
  `(EL k current.bb_instructions).inst_opcode = INVOKE` by
    (first_x_assum (qspec_then `k` mp_tac) >> simp[ricf_inst_edit_def]) >>
  metis_tac[ricf_event_no_intervening_invoke]
QED

(* FIXED-ANALYSIS INTERFACE AUDIT (C1.16.8.2)

   The checked call boundary above is syntactic, not a conditional runtime
   alias assumption.  For a nonempty copy, no INVOKE whatsoever can lie
   strictly between its position and any selected use.  In particular an
   unselected call passing the source at a mutable position is impossible
   there.  INVOKE has all write effects and bp_get_write_location returns
   ml_undefined.  ma_may_alias_iff and may_overlap make that location alias
   every nonempty source.  Volatility does not circumvent this test.
   The source theorem transports only opcode identity, never call operands
   or acceptance.  A previous selected call before a later selected call
   is likewise excluded.  Multiple readonly positions in ONE call remain
   possible.  Later calls after the last selected use are NOT excluded.

   Located-event fields: icf_build_ctx computes CFG, dominators, BP and
   memory_alias_analyze on the ORIGINAL fn.  Each logged round replaces
   only icf_dfg by dfg_build_function round; the validation block current
   is the prefix-edited round block.  ma_analyze_wf produces alias-set
   well-formedness without any runtime BP premise.  ricf_block_edit_EL
   preserves INVOKE opcodes but not operands; MCOPY may have become NOP.
   Hence erased original MCOPYs cannot be aligned with validation writes
   by equality.  ricf_located_event_source_write_exclusion instead treats
   their original mem_write_ops, without needing fixed BP soundness.

   The alternative semantic alias route is still NOT established:
   ma_may_alias_sound additionally requires allocas_non_overlapping,
   memloc_within_alloca for BOTH locations and two runtime-region equations.
   bp_segment_from_ops_runtime_region requires bp_ptr_sound, a fixed
   location and evaluated address; its existential natural address also
   needs alignment with the actual w2n address (avoid word wrap ambiguity).
   bp_analyze_fixpoint/invariant prove iteration contracts, not soundness
   at arbitrary frame_reachable states.  bp_process_block_sound processes
   a block starting from a sound input BP, needs fresh tracked outputs,
   alloca freshness and PHI conditions, and yields the PROCESSED BP.  It
   does not supply soundness of original bp_analyze at an interior state
   after edits or under recursion.  No such new invariant is assumed here.

   Sufficient remaining direct route: source provenance exclusion comes
   from HistorySource; selected-call descendant write exclusion comes
   from readonly_call_reachable_no_write (paired histories).  Convert
   these to byte disjointness using occurrence positive-key inversion,
   live-site natural geometry, access_ok_write_site_bounds, and the
   absolute-low-address/revert cases of access_ok.  No general BP theorem
   is needed for the intervening-call case just checked.

   READ/DEAD-READ is separate: source reads are not forbidden.  Ordinary
   reads must avoid dead destination sites, while relocated reads use
   cross agreement.  Classify original destination uses, including copies
   erased in earlier rounds, into selected INVOKEs, assignments and the
   copy itself, using original-use/history closure.  Then combine
   access_ok_read_site_bounds with positive occurrence-site geometry.
   IRCF's saved/planned destination reader proofs illustrate this route
   but their ircf_fwd_ok/block_plan hypotheses are not RICF producers.
   This audit certifies neither the final byte exclusion nor lifecycle.
*)
