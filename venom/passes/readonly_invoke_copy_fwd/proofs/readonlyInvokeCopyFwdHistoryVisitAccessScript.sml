(* Actual current-owner visits cannot execute their activating copy again. *)
Theory readonlyInvokeCopyFwdHistoryVisitAccess
Ancestors
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryExclusion
  readonlyInvokeCopyFwdHistoryOwnerAccess venomInstProps ptrDisciplineControl
  venomWfProps list finite_map readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdProtectionOrigin venomExecProofs contextCodegenRel venomWf venomInst
  readonlyInvokeCopyFwdHistoryReadExceptions readonlyInvokeCopyFwdOccurrenceAlias
  readonlyInvokeCopyFwdTraceOrigin invokeCopyFwdCommonDefs internalReturnCopyFwdPlan
  ptrDiscipline occurrenceGeometry o1LowerDloadOccurrence

Theorem ricf_visit_prefix_owner_function:
  !C root RPG RG RT rs pre PG G tn fn s.
    ricf_visit_prefix C root RPG RG RT rs pre PG G tn fn s ==>
    (if pre = [] then fn else (LAST pre).cf_fn) = root
Proof
  ho_match_mp_tac ricf_visit_prefix_ind >>
  rpt conj_tac >> rpt gen_tac >> simp[] >> strip_tac >>
  gvs[listTheory.LAST_DEF] >>
  Cases_on `pre` >> gvs[listTheory.LAST_DEF]
QED

Theorem ricf_history_cursor_owner_function:
  ricf_history_cursor vs C ctx0 log p [] PG G tn fn s ==>
  fn = p.rpe_fn
Proof
  simp[ricf_history_cursor_def] >> rpt strip_tac >>
  drule ricf_visit_prefix_owner_function >> simp[]
QED

Theorem ricf_history_cursor_owner_position:
  ricf_history_cursor vs C ctx0 log p [] PG G tn fn s /\
  active_inst fn inst s /\ wf_function p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) ==>
  fn = p.rpe_fn /\ p.rpe_event.rfe_index < s.vs_inst_idx /\
  s.vs_inst_idx < LENGTH p.rpe_block.bb_instructions /\
  inst = EL s.vs_inst_idx p.rpe_block.bb_instructions
Proof
  strip_tac >>
  drule ricf_history_cursor_owner_function >> strip_tac >>
  drule ricf_history_cursor_no_reentry >> strip_tac >>
  fs[ricf_history_cursor_def, ricf_history_origin_def] >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  `~is_terminator (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode` by
    (`ricf_event_ok p.rpe_event current` by metis_tac[ricf_event_ok_def] >>
     drule ricf_event_copy_shape >> fs[is_terminator_def]) >>
  fs[ricf_source_copy_payload_def] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  fs[active_inst_def] >>
  `bb = p.rpe_block` by
    (`MEM p.rpe_block p.rpe_fn.fn_blocks` by metis_tac[EL_MEM] >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) p.rpe_fn.fn_blocks)` by
       fs[wf_function_def, fn_labels_def] >>
     `lookup_block p.rpe_before.vs_current_bb p.rpe_fn.fn_blocks = SOME bb` by
       metis_tac[venomExecProofsTheory.MEM_lookup_block] >>
     `lookup_block p.rpe_before.vs_current_bb p.rpe_fn.fn_blocks = SOME p.rpe_block` by
       metis_tac[venomExecProofsTheory.MEM_lookup_block] >> fs[]) >>
  gvs[]
QED

Theorem ricf_history_cursor_owner_copy_distinct:
  ricf_history_cursor vs C ctx0 log p [] PG G tn fn s /\
  active_inst fn inst s /\ wf_function p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) ==>
  inst.inst_id <> (ricf_event_copy p.rpe_event p.rpe_block).inst_id
Proof
  strip_tac >> drule_all ricf_history_cursor_owner_position >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) p.rpe_block.bb_instructions)` by
    (fs[ricf_history_cursor_def, ricf_history_origin_def] >>
     drule_all ricf_located_event_source_block >> strip_tac >>
     fs[wf_function_def, fn_inst_ids_distinct_def] >>
     qspecl_then [`\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
       `p.rpe_fn.fn_blocks`, `EL b p.rpe_fn.fn_blocks`] mp_tac
       all_distinct_flat_map_member >> simp[EL_MEM]) >>
  `p.rpe_event.rfe_index < LENGTH p.rpe_block.bb_instructions` by decide_tac >>
  `s.vs_inst_idx <> p.rpe_event.rfe_index` by decide_tac >>
  fs[ricf_event_copy_def] >>
  metis_tac[ALL_DISTINCT_EL_IMP, EL_MAP, LENGTH_MAP]
QED

Theorem ricf_history_origin_original_allocas:
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn ==>
  ?dst sv sz da sa di.
    (ricf_event_copy p.rpe_event p.rpe_block).inst_operands = [Var dst;Var sv;Lit sz] /\
    dfg_get_def (dfg_build_function p.rpe_fn)
      (icf_assign_root (dfg_build_function p.rpe_fn) {} dst) = SOME di /\
    icf_is_alloca di /\
    MEM da (fn_insts p.rpe_fn) /\ da.inst_opcode = ALLOCA /\
    da.inst_outputs = [icf_assign_root (dfg_build_function p.rpe_fn) {} dst] /\
    MEM sa (fn_insts p.rpe_fn) /\ sa.inst_opcode = ALLOCA /\
    sa.inst_outputs = [sv] /\
    p.rpe_dst = (p.rpe_owner,da.inst_id) /\
    p.rpe_src = (p.rpe_owner,sa.inst_id)
Proof
  strip_tac >> fs[ricf_history_origin_def] >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `MEM p.rpe_block p.rpe_fn.fn_blocks` by metis_tac[EL_MEM] >>
  `p.rpe_event.rfe_index < LENGTH p.rpe_block.bb_instructions` by
    (drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_block_edit_def] >> metis_tac[LIST_REL_LENGTH]) >>
  `(ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY` by
    (drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> metis_tac[]) >>
  qpat_assum `p.rpe_block = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  rule_assum_tac (PURE_REWRITE_RULE [ricf_event_copy_def]) >>
  drule_all ricf_source_alloca_witnesses >> strip_tac >>
  fs[ricf_source_copy_payload_def] >>
  `FLOOKUP H dst = SOME (p.rpe_owner,da.inst_id)` by
    (irule occurrence_alias_reachable_operand >>
     simp[] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     gvs[ircf_alias_refl]) >>
  `FLOOKUP H sv = SOME (p.rpe_owner,sa.inst_id)` by
    (irule occurrence_alias_reachable_operand >>
     simp[] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     gvs[ircf_alias_refl]) >>
  fs[op_prov_def] >> pure_rewrite_tac[ricf_event_copy_def] >> metis_tac[]
QED

(* Only the current owner's visit is covered: the cursor has empty prefix. *)
Theorem ricf_history_cursor_owner_write_ranges:
  ricf_history_cursor vs C ctx0 log p [] PG G tn fn s /\
  active_inst fn inst s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  wf_function p.rpe_fn /\ ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn /\
  occurrence_syntax_origin fn p.rpe_owner H /\
  occurrence_annotation_ok n p.rpe_owner U B HP H stk PG G s /\
  occurrence_natural_geometry lo p.rpe_owner U B stk s /\
  FLOOKUP B p.rpe_dst = SOME (db,z) /\
  FLOOKUP B p.rpe_src = SOME (sb,z) /\ 0 < z /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s ==>
  !off len k.
    MEM (off,len) (source_memory_write_ranges inst s) /\ k < z ==>
    ~(off <= db+k /\ db+k < off+len) /\
    ~(off <= sb+k /\ sb+k < off+len)
Proof
  strip_tac >>
  drule_all ricf_history_cursor_owner_position >> strip_tac >>
  drule_all ricf_history_cursor_owner_copy_distinct >> strip_tac >>
  `fn_inst_ids_distinct p.rpe_fn` by fs[wf_function_def] >>
  `occurrence_env_ok B (p.rpe_owner::MAP (\u. u.of_owner) U) H G` by
    fs[occurrence_annotation_ok_def] >>
  fs[ricf_history_cursor_def] >>
  drule_all ricf_history_origin_original_allocas >> strip_tac >>
  fs[ricf_history_origin_def] >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  gvs[] >>
  `!off len k. MEM (off,len) (source_memory_write_ranges
      (EL s.vs_inst_idx (EL b p.rpe_fn.fn_blocks).bb_instructions) s) /\ k < z ==>
    ~(off <= db+k /\ db+k < off+len)` by
    (metis_tac[ricf_located_event_destination_ranges]) >>
  `!off len k. MEM (off,len) (source_memory_write_ranges
      (EL s.vs_inst_idx (EL b p.rpe_fn.fn_blocks).bb_instructions) s) /\ k < z ==>
    ~(off <= sb+k /\ sb+k < off+len)` by
    (`p.rpe_event.rfe_index <= s.vs_inst_idx` by decide_tac >>
     metis_tac[ricf_located_event_source_write_range_exclusion]) >>
  metis_tac[arithmeticTheory.ADD_SYM]
QED
