(* Literal sizes in original full-allocation copies survive validation edits.
   This is a size calculation only, not runtime soundness of fixed BP. *)
Theory readonlyInvokeCopyFwdHistorySize
Ancestors
  readonlyInvokeCopyFwdHistoryAnalysis readonlyInvokeCopyFwdProtectionOrigin
  readonlyMemoryArgsProps venomState readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdPlan list

Theorem ricf_located_event_read_size:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;src;szop] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ eval_operand szop s = SOME z ==>
  szop = Lit z /\
  (bp_get_read_location e.rfe_ctx.icf_bp
    (ricf_event_copy e current) AddrSp_Memory).ml_size = SOME (w2n z)
Proof
  strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule ricf_event_copy_shape >> strip_tac >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
  `e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions` by
    metis_tac[ricf_block_edit_EL] >>
  `(EL e.rfe_index (EL b fn.fn_blocks).bb_instructions).inst_opcode = MCOPY` by
    metis_tac[ricf_event_copy_def] >>
  gvs[ricf_event_copy_def] >>
  drule_all ricf_source_alloca_witnesses >> strip_tac >>
  gvs[eval_operand_def] >>
  Cases_on `EL e.rfe_index (EL b fn.fn_blocks).bb_instructions` >>
  gvs[] >>
  simp[basePtrDefsTheory.bp_get_read_location_def,
       venomInstTheory.is_raw_fmp_opcode_def,
       venomEffectsTheory.read_effects_def,
       memLocDefsTheory.mem_read_ops_def,
       basePtrDefsTheory.bp_segment_from_ops_def] >>
  rpt (CASE_TAC >> simp[])
QED

(* Positivity discharges the fixed-analysis size guard; no BP runtime
   interpretation is needed for the original-source call boundary. *)
Theorem ricf_located_event_positive_no_intervening_source_invoke:
  ricf_located_event (icf_build_ctx fm fs rma fn) fn log
    round b es prefix e current /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;src;szop] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ eval_operand szop s = SOME z /\ 0 < w2n z /\
  ricf_selected_position e current j /\ e.rfe_index < k /\ k < j /\
  k < LENGTH (EL b fn.fn_blocks).bb_instructions ==>
  (EL k (EL b fn.fn_blocks).bb_instructions).inst_opcode <> INVOKE
Proof
  strip_tac >>
  drule_all ricf_located_event_read_size >> strip_tac >>
  `(bp_get_read_location e.rfe_ctx.icf_bp
      (ricf_event_copy e current) AddrSp_Memory).ml_size <> SOME 0` by
    (strip_tac >> gvs[]) >>
  drule_all ricf_located_event_no_intervening_source_invoke >> simp[]
QED

(* Zero-size consumers reuse the exact equation in
   ricf_located_event_read_size (which has no positivity premise).
   Substituting w2n z = 0 makes k < w2n z false and makes
   off <= p /\ p < off + w2n z false, by arithmetic simplification.
   Thus no extra pass-specific empty-range lemma is needed.  This does
   not assert call exclusion, operand availability, or successful stepping
   for zero-size copies. *)
