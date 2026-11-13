(* Actual selected payloads determine the rewritten argument values. *)
Theory readonlyInvokeCopyFwdExecutionCallValues
Ancestors
  readonlyInvokeCopyFwdExecutionCallArgs readonlyInvokeCopyFwdExecutionCallMap
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryVisitAccess readonlyInvokeCopyFwdProtectionOrigin
  readonlyInvokeCopyFwdHistoryClosure
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdRel
  invokeCopyFwdCommonDefs internalReturnCopyFwdPlan
  occurrenceGeometry occurrenceOrigin o1LowerDloadOccurrence o1LowerDloadRelocationKernel
  fnFrameStepsRevertForward allocaRemapSSA ptrDiscipline
  venomWf venomInst list finite_map pred_set words

Theorem ricf_call_origin_copy_block[local]:
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) ==>
  MEM p.rpe_block p.rpe_fn.fn_blocks /\
  p.rpe_event.rfe_index < LENGTH p.rpe_block.bb_instructions /\
  (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY
Proof
  strip_tac >> fs[ricf_history_origin_def] >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule ricf_event_copy_shape >> strip_tac >>
  `LENGTH (EL b p.rpe_fn.fn_blocks).bb_instructions =
   LENGTH current.bb_instructions` by
    metis_tac[ricf_block_edit_EL] >>
  simp[EL_MEM] >> metis_tac[]
QED

(* The current numeric argument key identifies the original destination
   alias, including when the payload was obtained from chosen support. *)
Theorem ricf_call_current_payload_operand_origin:
  ricf_history_origin vs C ctx0 log p ostk OPG OG OT /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  p.rpe_fn = fn /\ p.rpe_owner = a /\
  occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\ 0 < p.rpe_size /\
  op_prov G op = SOME (p.rpe_db,p.rpe_size) ==>
  ?round b es prefix current dst sv sz dv.
    ricf_located_event ctx0 fn log round b es prefix p.rpe_event current /\
    p.rpe_block = EL b fn.fn_blocks /\
    (ricf_event_copy p.rpe_event p.rpe_block).inst_operands =
      [Var dst;Var sv;Lit sz] /\
    op = Var dv /\ ircf_alias fn
      (icf_assign_root (dfg_build_function fn) {} dst) dv
Proof
  strip_tac >>
  qpat_assum `ricf_history_origin vs C ctx0 log p ostk OPG OG OT`
    (mp_then Any mp_tac ricf_history_origin_original_allocas) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  rename1 `(ricf_event_copy p.rpe_event p.rpe_block).inst_operands =
    [Var dst;Var sv;Lit sz]` >>
  `?round b es prefix current.
    ricf_located_event ctx0 fn log round b es prefix p.rpe_event current /\
    p.rpe_block = EL b fn.fn_blocks` by
    (fs[ricf_history_origin_def] >> metis_tac[]) >>
  `MEM da (fn_insts fn) /\
   da.inst_outputs = [icf_assign_root (dfg_build_function fn) {} dst]` by metis_tac[] >>
  `op_prov H op = SOME (a,da.inst_id)` by
    (irule occurrence_geometry_op_positive_key >>
     fs[occurrence_annotation_ok_def] >> metis_tac[]) >>
  `?dv. op = Var dv /\ ircf_alias fn
    (icf_assign_root (dfg_build_function fn) {} dst) dv` by
    (irule ricf_located_event_destination_occurrence_operand >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`round`,`b`,`es`,`prefix`,`current`,`dst`,`sv`,`sz`,`dv`] >> simp[]
QED

Theorem ricf_call_phase_allocas[local]:
  ricf_phase_entry vs C ctx0 log stk PG G tn fn s a U B (p,[]) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn /\
  (ricf_event_copy p.rpe_event p.rpe_block).inst_operands =
    [Var dst;Var sv;Lit sz] ==>
  ?da sa.
    p.rpe_dst = (p.rpe_owner,da.inst_id) /\
    p.rpe_src = (p.rpe_owner,sa.inst_id) /\
    MEM da (fn_insts p.rpe_fn) /\ da.inst_opcode = ALLOCA /\
    da.inst_outputs = [icf_assign_root (dfg_build_function p.rpe_fn) {} dst] /\
    da.inst_operands = [Lit sz] /\
    MEM sa (fn_insts p.rpe_fn) /\ sa.inst_opcode = ALLOCA /\
    sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit sz]
Proof
  strip_tac >>
  `?ostk OPG OG OT. ricf_history_origin vs C ctx0 log p ostk OPG OG OT` by
    (fs[ricf_phase_entry_def, ricf_history_cursor_def] >> metis_tac[]) >>
  drule_all ricf_history_origin_original_allocas >> strip_tac >> gvs[] >>
  drule_all ricf_call_origin_copy_block >> strip_tac >>
  `dfg_get_def (dfg_build_function p.rpe_fn)
    (icf_assign_root (dfg_build_function p.rpe_fn) {} dst) = SOME da` by
    (irule dfg_build_function_ssa_def >> simp[]) >>
  `di = da` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  rule_assum_tac (PURE_REWRITE_RULE [ricf_event_copy_def]) >>
  drule_all ricf_source_alloca_witnesses >> strip_tac >> gvs[] >>
  `da = da'` by (irule ssa_unique_output >> metis_tac[MEM]) >>
  `sa = sa'` by (irule ssa_unique_output >> metis_tac[MEM]) >>
  qexistsl_tac [`da'`,`sa'`] >> simp[]
QED

Theorem ricf_call_positive_payload_argument:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  MEM (p,[]) certificates /\ MEM p ps /\
  EVERY (\q. MEM (q,[]) certificates) ps /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_natural_geometry lo a U B stk s /\
  inst.inst_opcode = INVOKE /\ MEM (Var dv) inst.inst_operands /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME p.rpe_block /\
  p.rpe_event.rfe_index <= s.vs_inst_idx /\
  (ricf_event_copy p.rpe_event p.rpe_block).inst_operands =
    [Var dst;Var sv;Lit sz] /\
  ircf_alias fn (icf_assign_root (dfg_build_function fn) {} dst) dv ==>
  eval_operand (Var dv) s = SOME (n2w p.rpe_db) /\
  eval_operand (Var sv) t = SOME (n2w p.rpe_sb) /\
  op_prov G (Var dv) = SOME (p.rpe_db,p.rpe_size) /\
  ricf_opaque_value_agree
    (FOLDR (\q m.
      m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps)
    (op_prov G (Var dv)) {} (n2w p.rpe_db) (n2w p.rpe_sb)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `?ctxP logP. ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[])` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def,
        EVERY_MEM] >> metis_tac[]) >>
  `p.rpe_fn = fn /\ p.rpe_owner = a /\
   FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
   FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\ 0 < p.rpe_size` by
    (fs[ricf_phase_entry_def] >> metis_tac[ricf_history_cursor_owner_function]) >>
  `ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
   ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
   ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn` by metis_tac[] >>
  drule_all ricf_call_phase_allocas >> strip_tac >>
  `p.rpe_event.rfe_index < LENGTH p.rpe_block.bb_instructions /\
   (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY` by
    (fs[ricf_phase_entry_def, ricf_history_cursor_def] >>
     metis_tac[ricf_call_origin_copy_block]) >>
  `MEM da (fn_insts fn) /\
   da.inst_outputs = [icf_assign_root (dfg_build_function fn) {} dst] /\
   MEM sa (fn_insts fn)` by metis_tac[] >>
  drule_all ricf_call_earlier_copy_values >> strip_tac >>
  `db = p.rpe_db /\ sb = p.rpe_sb /\ w2n sz = p.rpe_size` by
    metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  `eval_operand (Var sv) t = SOME (n2w p.rpe_sb)` by
    (irule ricf_call_source_alloca_target_value >> metis_tac[]) >>
  `FLOOKUP (FOLDR (\q m.
    m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps)
      (p.rpe_db,p.rpe_size) = SOME (p.rpe_db,p.rpe_sb,p.rpe_size)` by
    (irule ricf_call_selected_payload_lookup >> metis_tac[]) >>
  `FLOOKUP G dv = SOME (p.rpe_db,p.rpe_size)` by metis_tac[] >>
  simp[op_prov_def] >>
  qpat_assum `FLOOKUP (FOLDR _ sites ps) (p.rpe_db,p.rpe_size) =
    SOME (p.rpe_db,p.rpe_sb,p.rpe_size)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[ricf_opaque_value_agree_def, ricf_value_agree_def, ld_value_agree_def,
    FLOOKUP_DEF, WORD_ADD_SUB2] >> metis_tac[]
QED
