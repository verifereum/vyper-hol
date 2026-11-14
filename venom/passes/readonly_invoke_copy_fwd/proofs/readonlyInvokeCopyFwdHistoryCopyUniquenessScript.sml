(* Destination uniqueness is static: the DFG of a round still sees a
   conflicting copy even if an earlier event in that round has NOPed it. *)
Theory readonlyInvokeCopyFwdHistoryCopyUniqueness
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdHistoryUses
  readonlyInvokeCopyFwdHistoryReadExceptions
  readonlyInvokeCopyFwdHistoryClosure readonlyInvokeCopyFwdProtectionSelected
  readonlyInvokeCopyFwdPlan internalReturnCopyFwdPlan invokeCopyFwdCommonDefs
  dfgAnalysisProps venomWf venomWfProps venomInst list pred_set
  invokeCopyFwdMemoryUses memLocDefs occurrenceOrigin

Theorem ricf_located_event_surviving_destination_use:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  old.inst_opcode = MCOPY /\ 0 < LENGTH old.inst_operands /\
  EL 0 old.inst_operands = Var v /\
  ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v /\
  (EL i (EL cb round.fn_blocks).bb_instructions).inst_opcode = MCOPY ==>
  old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id
Proof
  strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule_all ricf_function_trace_edit >> strip_tac >>
  `cb < LENGTH round.fn_blocks /\
   i < LENGTH (EL cb round.fn_blocks).bb_instructions /\
   EL i (EL cb round.fn_blocks).bb_instructions = old` by
    (fs[ricf_function_edit_def, ricf_block_edit_def, LIST_REL_EL_EQN] >>
     metis_tac[ricf_inst_edit_def]) >>
  `MEM old (fn_insts round)` by
    (simp[fn_insts_def] >> irule fmp_fn_insts_blocks_intro >>
     qexists_tac `EL cb round.fn_blocks` >> metis_tac[EL_MEM]) >>
  `ircf_alias round (icf_assign_root (dfg_build_function round) {} dst) v` by
    (fs[icf_collect_aliases_ircf_alias, EXTENSION] >> metis_tac[]) >>
  `(ricf_event_copy e current).inst_operands = [Var dst;src;sz]` by metis_tac[] >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  drule_all ricf_event_alias_use_accepted >>
  gvs[icf_is_assign_output_use_def]
QED

(* A strict earlier-round witness.  This avoids interpreting an arbitrary
   prior-erasure witness as an ordering fact about runtime activations. *)
Theorem ricf_located_event_earlier_erasure:
  ricf_located_event ctx0 original log round b es prefix e current /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  old.inst_opcode = MCOPY /\
  (EL i (EL cb round.fn_blocks).bb_instructions).inst_opcode <> MCOPY ==>
  ?pre earlier es' prefix' f current'.
    LENGTH pre < LENGTH log /\
    ricf_located_event ctx0 original pre earlier cb es' prefix' f current' /\
    f.rfe_index = i
Proof
  simp[ricf_located_event_def] >> rpt strip_tac >>
  drule_all ricf_logged_function_trace_prefix >> strip_tac >>
  `ricf_logged_erasure pre cb i old` by
    (irule ricf_logged_function_trace_erasure >>
     qexistsl_tac [`ctx0`,`original`,`round`] >> gvs[]) >>
  drule_all ricf_logged_erasure_located_event >> strip_tac >>
  qexists_tac `pre` >> simp[] >>
  qexistsl_tac [`round'`,`es'`,`prefix'`,`e'`,`current'`] >>
  gvs[ricf_located_event_def] >> metis_tac[]
QED

Theorem ricf_located_event_destination_alloca_of:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] ==>
  ?amount. ircf_alloca_of original
    (icf_assign_root (dfg_build_function original) {} dst) amount
Proof
  strip_tac >> drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
  `MEM di (fn_insts original)` by metis_tac[dfg_build_function_correct] >>
  `inst_wf di` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  `?amount. di.inst_operands = [Lit amount]` by
    (gvs[icf_is_alloca_def, inst_wf_def] >>
     Cases_on `di.inst_operands` >> gvs[LENGTH_EQ_NUM_compute] >>
     Cases_on `h` >> gvs[]) >>
  qexists_tac `amount` >> irule ircf_alloca_of_dfg >>
  simp[icf_matches_alloca_size_def]
QED

Theorem ricf_located_event_destination_unique:
  !ctx0 original log round b es prefix e current dst src sz cb i old v.
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  old.inst_opcode = MCOPY /\ 0 < LENGTH old.inst_operands /\
  EL 0 old.inst_operands = Var v /\
  ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v ==>
  old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id
Proof
  measureInduct_on `LENGTH log` >> rpt strip_tac >>
  Cases_on `(EL i (EL cb round.fn_blocks).bb_instructions).inst_opcode = MCOPY`
  >- (irule ricf_located_event_surviving_destination_use >> metis_tac[]) >>
  `b < LENGTH original.fn_blocks /\
   ricf_block_edit (EL b original.fn_blocks) current` by
    (irule ricf_located_event_source_block >> metis_tac[]) >>
  `e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
   (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY` by
    (drule ricf_block_edit_EL >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >>
     gvs[ricf_event_copy_def] >> metis_tac[ricf_inst_edit_def]) >>
  drule_all ricf_located_event_earlier_erasure >> strip_tac >>
  `?d ss zz. (ricf_event_copy f (EL cb original.fn_blocks)).inst_operands =
    [Var d;ss;zz]` by metis_tac[ricf_located_event_source_descriptor] >>
  `ricf_event_copy f (EL cb original.fn_blocks) = old` by
    gvs[ricf_event_copy_def] >>
  `d = v` by gvs[] >>
  `?amount. ircf_alloca_of original
    (icf_assign_root (dfg_build_function original) {} dst) amount` by
    (irule ricf_located_event_destination_alloca_of >> metis_tac[]) >>
  `?amount'. ircf_alloca_of original
    (icf_assign_root (dfg_build_function original) {} d) amount'` by
    (irule ricf_located_event_destination_alloca_of >> metis_tac[]) >>
  `icf_assign_root (dfg_build_function original) {} d =
   icf_assign_root (dfg_build_function original) {} dst` by
    (irule ircf_alloca_aliases_separate >>
     metis_tac[ircf_assign_root_alias]) >>
  first_x_assum (qspec_then `pre` mp_tac) >> simp[] >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`b`,`e.rfe_index`,`dst`] mp_tac) >>
  simp[GSYM ricf_event_copy_def] >>
  metis_tac[ircf_assign_root_alias]
QED

(* The original write-use consumer has no prior-erasure alternative. *)
Theorem ricf_located_event_original_write_unique:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  occurrence_syntax_origin original a H /\ MEM ai (fn_insts original) /\
  ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [icf_assign_root (dfg_build_function original) {} dst] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  mem_write_ops old = SOME ops ==>
  op_prov H ops.iao_ofst <> SOME (a,ai.inst_id) \/
  (old.inst_opcode = MCOPY /\
   old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id)
Proof
  strip_tac >>
  Cases_on `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` >> simp[] >>
  `old.inst_opcode = MCOPY` by
    (drule_all ricf_located_event_original_address_use >> metis_tac[]) >>
  `0 < LENGTH old.inst_operands /\ EL 0 old.inst_operands = ops.iao_ofst` by
    gvs[mem_write_ops_def, AllCaseEqs()] >>
  `?v. ops.iao_ofst = Var v /\
    ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v` by
    (irule ricf_located_event_destination_occurrence_operand >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  irule ricf_located_event_destination_unique >> metis_tac[]
QED
