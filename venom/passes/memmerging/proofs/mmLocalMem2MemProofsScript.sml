(* Local memmerging phase: Mem2Mem prefix execution. *)
Theory mmLocalMem2MemProofs
Ancestors
  venomFnInstsProofs venomInst memoryReadRel
  mmSupplyWfProofs mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner allocaRemapSSA o1MakeSsaCfg makeSsaCurrentWfSsa
  cfgWf venomWf stateEquiv rich_list mmTransform mmScan mmCopy list sorting
  simplifyCfgPhiSemantics simplifyCfgFixupStatic basePtrProofs mmTraceProofs frameViewMemory dftCommutation
  regularMemorySim rangeAnalysisProofs dftIndexedExec removeUnusedProofs analysisSimProofsBase
  mmLocalStructureProofs
  mmLocalCaptureProofs
  mmLocalPendingProofs
  mmLocalReplayProofs
  venomTransformStructureProps venomWriteReplayProps venomExecutionReplayProps irSupplyFreshProps
Libs
  wordsLib finite_mapLib stepInstBaseLib

Definition mm_local_nonmemory_frame_def:
  mm_local_nonmemory_frame s =
    stateFrame$state_frame (s with <|vs_memory := []; vs_inst_idx := 0|>)
End

Definition mm_local_cut_def:
  mm_local_cut is gs H n excluded pc t <=>
    t.vs_inst_idx = pc /\
    mm_local_nonmemory_frame (H n) = mm_local_nonmemory_frame t /\
    (!v. v NOTIN excluded ==> lookup_var v (H n) = lookup_var v t) /\
    mm_local_pending (mm_local_write_capture is H n)
      (mm_local_pending_indices is gs n) (H n) t /\
    t.vs_memory =
      (FOLDL (\st q. if MEM q (mm_local_pending_indices is gs n) then st else
        case mm_local_write_capture is H n q of NONE => st
        | SOME (d,bs) => write_memory_with_expansion d bs st)
        (H (mm_local_epoch_start is gs n))
        (MAP (\q. mm_local_epoch_start is gs n + q)
          (COUNT_LIST (n - mm_local_epoch_start is gs n)))).vs_memory
End

Theorem mm_local_nonmemory_frame_updates[simp]:
  mm_local_nonmemory_frame (s with vs_inst_idx := pc) = mm_local_nonmemory_frame s /\
  mm_local_nonmemory_frame (s with vs_memory := mem) = mm_local_nonmemory_frame s /\
  mm_local_nonmemory_frame (update_var v w s) = mm_local_nonmemory_frame s /\
  mm_local_nonmemory_frame (write_memory_with_expansion d bs s) = mm_local_nonmemory_frame s
Proof
  simp[mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.update_var_def, venomStateTheory.write_memory_with_expansion_def]
QED

Theorem mm_local_nop_capture_suc[local]:
  ((EL n is).inst_opcode = NOP \/ (EL n is).inst_opcode = MLOAD) ==>
  mm_local_write_capture is H (SUC n) = mm_local_write_capture is H n
Proof
  strip_tac >> rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `j` >>
  (Cases_on `j = n` >- simp[mm_local_write_capture_def]) >>
  `j < SUC n <=> j < n` by decide_tac >> simp[mm_local_write_capture_def]
QED

Theorem mm_local_nop_pending_suc[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ ((EL n is).inst_opcode = NOP \/ (EL n is).inst_opcode = MLOAD) ==>
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n
Proof
  strip_tac >>
  `!g. MEM g gs ==> rep_of_group is g <> SOME ((EL n is).inst_id,g)` by
    (rpt strip_tac >> drule_all mm_local_canonical_rep_write >> simp[]) >>
  simp[NoAsms, mm_local_pending_indices_def, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, FILTER_APPEND] >>
  `~((EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES})` by simp[] >>
  simp[] >> rewrite_tac[rich_listTheory.FILTER_EQ] >>
  qx_gen_tac `j` >> simp[MEM_COUNT_LIST] >> strip_tac >>
  eq_tac >> strip_tac >> gvs[]
  >- (qexistsl [`g`,`r`] >> simp[] >> decide_tac) >>
  `r <> n` by metis_tac[] >> qexistsl [`g`,`r`] >> simp[] >> decide_tac
QED

Theorem mm_local_cut_nop_stutter[local]:
  mm_local_cut is gs H n excluded pc t /\
  ((EL n is).inst_opcode = NOP \/ (EL n is).inst_opcode = MLOAD) /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
  (H (SUC n)).vs_memory = (H n).vs_memory /\
  mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
  (!v. v NOTIN excluded ==> lookup_var v (H (SUC n)) = lookup_var v (H n)) ==>
  mm_local_cut is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >> (
  `mm_local_write_capture is H (SUC n) = mm_local_write_capture is H n` by
    metis_tac[mm_local_nop_capture_suc] >>
  `mm_local_epoch_start is gs n <= n` by
    (irule mm_local_epoch_start_bound >> qexistsl [`gs`,`is`] >> simp[]) >>
  gvs[mm_local_cut_def, venomStateTheory.lookup_var_def] >>
  conj_tac
  >- (gvs[mm_local_pending_def] >> qexists `ws` >> simp[] >>
      irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]) >>
  Cases_on `mm_local_pending_indices is gs n = []`
  >- gvs[mm_local_epoch_start_suc, mm_local_pending_empty,
       rich_listTheory.COUNT_LIST_def] >>
  `SUC n - mm_local_epoch_start is gs n = SUC (n - mm_local_epoch_start is gs n)` by
    decide_tac >>
  simp[mm_local_epoch_start_suc, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, MAP_APPEND, FOLDL_APPEND,
    mm_local_write_capture_future])
QED

Theorem mm_local_cut_nop_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  phi_prefix_length is <= n /\ n < LENGTH is /\ (EL n is).inst_opcode = NOP /\
  mm_local_cut is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK s /\
  H (SUC n) = s with vs_inst_idx := SUC (H n).vs_inst_idx /\
  apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es) ==>
  ?fin. step_inst fuel ctx (EL n is) t = OK fin /\
    mm_local_cut is gs H (SUC n) excluded (SUC pc)
      (fin with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  `s = H n` by metis_tac[venomInstPropsTheory.step_nop_identity,
    venomExecSemanticsTheory.exec_result_11] >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n` by
    (irule mm_local_nop_pending_suc >> metis_tac[]) >>
  qexists `t` >> conj_tac
  >- simp[venomInstPropsTheory.step_nop_identity] >>
  irule mm_local_cut_nop_stutter >> simp[venomStateTheory.lookup_var_def]
QED

Theorem mm_local_pending_indices_deferred_suc:
  n < LENGTH is /\
  (EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (?g r. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g) /\
    n < r /\ r < LENGTH is) /\
  (!g. MEM g gs ==> rep_of_group is g <> SOME ((EL n is).inst_id,g)) ==>
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]
Proof
  strip_tac >>
  `?g r. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids /\
    r < LENGTH is /\ SUC n <= r /\
    rep_of_group is g = SOME ((EL r is).inst_id,g)` by
    (qexistsl [`g`,`r`] >> simp[]) >>
  simp[NoAsms, mm_local_pending_indices_def, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, FILTER_APPEND] >>
  reverse IF_CASES_TAC
  >- (gvs[] >>
      qpat_x_assum `!g r. _` (qspecl_then [`g`,`r`] mp_tac) >> simp[]) >>
  simp[NoAsms] >> rewrite_tac[rich_listTheory.FILTER_EQ] >>
  qx_gen_tac `j` >> simp[MEM_COUNT_LIST] >> strip_tac >>
  eq_tac
  >- (strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  strip_tac >> gvs[] >>
  rename1 `rep_of_group is h = SOME ((EL q is).inst_id,h)` >>
  `q <> n` by metis_tac[] >>
  `SUC n <= q` by decide_tac >> qexistsl [`h`,`q`] >> simp[]
QED

Theorem mm_local_erased_write_pending_suc:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  n < LENGTH is /\ (EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM (EL n is).inst_id (nop_ids_of_groups (dfg_build_function fn0) mode is gs) ==>
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `!g. MEM g gs ==> rep_of_group is g <> SOME ((EL n is).inst_id,g)` by
    (rpt strip_tac >>
     `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
     metis_tac[mm_local_prefix_selected_rep]) >>
  `?g. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids` by
    (qpat_x_assum `MEM _ (nop_ids_of_groups _ _ _ _)` mp_tac >>
     pure_rewrite_tac[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >> strip_tac >>
     gvs[] >> rename1 `MEM _ (nop_ids_of_group _ _ _ g)` >>
     qexists `g` >> simp[] >>
     qpat_x_assum `MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
     simp[nop_ids_of_group_def] >>
     Cases_on `REVERSE (sort_ids_by_block bb.bb_instructions g.cg_inst_ids)` >>
     simp[MEM_FILTER, MEM_REVERSE] >> strip_tac >>
     `MEM (EL n bb.bb_instructions).inst_id
       (REVERSE (sort_ids_by_block bb.bb_instructions g.cg_inst_ids))` by
       metis_tac[MEM] >>
     gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER]) >>
  `?r. n <= r /\ r < LENGTH is /\ rep_of_group is g = SOME ((EL r is).inst_id,g)` by
    metis_tac[mm_local_event_rep_position] >>
  `n < r` by (Cases_on `n = r` >> gvs[] >> decide_tac) >>
  irule mm_local_pending_indices_deferred_suc >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_cut_erased_write_stutter[local]:
  mm_local_cut is gs H n excluded pc t /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n] /\
  mm_local_write_capture is H (SUC n) n = SOME (d,bs) /\
  (H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory /\
  mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
  (!v. lookup_var v (H (SUC n)) = lookup_var v (H n)) ==>
  mm_local_cut is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  `mm_local_epoch_start is gs n <= n` by
    (irule mm_local_epoch_start_bound >> qexistsl [`gs`,`is`] >> simp[]) >>
  `!j. MEM j (mm_local_pending_indices is gs n) ==> j < n` by
    simp[mm_local_pending_indices_mem] >>
  `mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs n) (H n) t` by
    (irule mm_local_pending_cap_cong >>
     qexists `mm_local_write_capture is H n` >>
     gvs[mm_local_cut_def] >>
     rpt strip_tac >> sym_tac >> irule mm_local_write_capture_past >> simp[]) >>
  `mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs (SUC n)) (H (SUC n)) t` by
    (asm_rewrite_tac[] >> irule mm_local_pending_create >> metis_tac[]) >>
  gvs[mm_local_cut_def, venomStateTheory.lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `mm_local_pending _ (_ ++ [n]) (H (SUC n)) t`
        (strip_assume_tac o REWRITE_RULE [mm_local_pending_def]) >>
      simp[mm_local_pending_def] >> goal_assum (drule_at Any) >>
      irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]) >>
  `SUC n - mm_local_epoch_start is gs n = SUC (n - mm_local_epoch_start is gs n)` by
    decide_tac >>
  simp[mm_local_epoch_start_suc, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, MAP_APPEND, FOLDL_APPEND] >>
  AP_TERM_TAC >> irule FOLDL_CONG >> simp[] >>
  rpt strip_tac >> gvs[MEM_MAP, MEM_COUNT_LIST] >>
  rename1 `q < n - mm_local_epoch_start is gs n` >>
  `q + mm_local_epoch_start is gs n < n` by decide_tac >>
  `mm_local_write_capture is H n (q + mm_local_epoch_start is gs n) =
   mm_local_write_capture is H (SUC n) (q + mm_local_epoch_start is gs n)` by
    simp[mm_local_write_capture_past] >> simp[]
QED

Theorem mm_local_write_runtime_frame:
  i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  step_inst fuel ctx i s = OK t ==>
  mm_local_nonmemory_frame t = mm_local_nonmemory_frame s /\
  (!v. lookup_var v t = lookup_var v s)
Proof
  simp[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    venomExecSemanticsTheory.exec_write2_def] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[venomMemPropsTheory.mstore_eq_write_mem,
    venomExecSemanticsTheory.mcopy_def,
    venomStateTheory.write_memory_with_expansion_def,
    venomStateTheory.lookup_var_def]
QED

Theorem mm_local_cut_erased_write_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  phi_prefix_length is <= n /\ n < LENGTH is /\
  MEM (EL n is).inst_id ns /\ (EL n is).inst_opcode IN {MSTORE; MCOPY} /\
  mm_local_cut is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK s /\
  H (SUC n) = s with vs_inst_idx := SUC (H n).vs_inst_idx ==>
  apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([mk_nop_from (EL n is)],es) /\
  step_inst fuel ctx (mk_nop_from (EL n is)) t = OK t /\
  mm_local_cut is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  conj_tac >- simp[apply_groups_inst_supply_def] >>
  conj_tac
  >- simp[venomInstPropsTheory.step_nop_identity, mk_nop_from_def] >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]` by
    (irule mm_local_erased_write_pending_suc >>
     fs[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >> metis_tac[]) >>
  `mm_local_nonmemory_frame s = mm_local_nonmemory_frame (H n) /\
    (!v. lookup_var v s = lookup_var v (H n))` by
    (irule mm_local_write_runtime_frame >> metis_tac[pred_setTheory.IN_INSERT,
      pred_setTheory.NOT_IN_EMPTY]) >>
  `?d bs. mm_local_write_capture is H (SUC n) n = SOME (d,bs) /\
    (H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory` by
    (irule mm_local_interval_runtime_capture >>
     `SUC n <= LENGTH is` by decide_tac >>
     simp[] >> metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  irule mm_local_cut_erased_write_stutter >>
  gvs[venomStateTheory.lookup_var_def] >> metis_tac[]
QED

Theorem mm_local_load_runtime_frame[local]:
  i.inst_opcode = MLOAD /\ step_inst fuel ctx i s = OK t ==>
  t.vs_memory = s.vs_memory /\ mm_local_nonmemory_frame t = mm_local_nonmemory_frame s
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_read1_def] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.update_var_def]
QED

Theorem mm_local_cut_erased_load_excluded_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} SUBSET excluded /\
  phi_prefix_length is <= n /\ n < LENGTH is /\
  MEM (EL n is).inst_id ns /\ (EL n is).inst_opcode = MLOAD /\
  mm_local_cut is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK s /\
  H (SUC n) = s with vs_inst_idx := SUC (H n).vs_inst_idx ==>
  apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([mk_nop_from (EL n is)],es) /\
  step_inst fuel ctx (mk_nop_from (EL n is)) t = OK t /\
  mm_local_cut is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  conj_tac >- simp[apply_groups_inst_supply_def] >>
  conj_tac
  >- simp[venomInstPropsTheory.step_nop_identity, mk_nop_from_def] >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n` by
    (irule mm_local_nop_pending_suc >> metis_tac[]) >>
  `s.vs_memory = (H n).vs_memory /\
    mm_local_nonmemory_frame s = mm_local_nonmemory_frame (H n)` by
    (irule mm_local_load_runtime_frame >> metis_tac[]) >>
  `!v. v NOTIN excluded ==> lookup_var v s = lookup_var v (H n)` by
    (rpt strip_tac >>
     `~MEM v (EL n is).inst_outputs` by
       (strip_tac >> `MEM (EL n is) is` by metis_tac[EL_MEM] >>
        fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
     irule venomInstPropsTheory.step_preserves_non_output_vars >>
     qexistsl [`ctx`,`fuel`,`EL n is`] >> simp[venomInstTheory.is_terminator_def]) >>
  irule mm_local_cut_nop_stutter >>
  gvs[venomStateTheory.lookup_var_def]
QED

Theorem mm_local_cut_erased_load_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  excluded = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  phi_prefix_length is <= n /\ n < LENGTH is /\
  MEM (EL n is).inst_id ns /\ (EL n is).inst_opcode = MLOAD /\
  mm_local_cut is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK s /\
  H (SUC n) = s with vs_inst_idx := SUC (H n).vs_inst_idx ==>
  apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([mk_nop_from (EL n is)],es) /\
  step_inst fuel ctx (mk_nop_from (EL n is)) t = OK t /\
  mm_local_cut is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >> irule mm_local_cut_erased_load_excluded_transition >>
  simp[] >> metis_tac[pred_setTheory.SUBSET_REFL]
QED

Theorem mm_local_pending_literal_load_disjoint[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ (EL n is).inst_opcode = MLOAD /\
  (EL n is).inst_operands = [Lit w] /\ (EL n is).inst_outputs = [out] /\
  MEM j (mm_local_pending_indices is gs n) /\
  mm_local_write_capture is H N j = SOME (d,bs) ==>
  bs = [] \/ w2n w + 32 <= d \/ d + LENGTH bs <= w2n w
Proof
  strip_tac >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n` by
    (irule mm_local_nop_pending_suc >> metis_tac[]) >>
  `MEM j (mm_local_pending_indices is gs (SUC n))` by metis_tac[] >>
  qabbrev_tac `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE (SUC n) is)` >>
  `?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length` by
    (irule mm_local_canonical_pending_capture_owner >>
     simp[Abbr `ss`] >> metis_tac[arithmeticTheory.LESS_EQ]) >>
  `ss = scan_load Mem2Mem
    (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is))
    (EL n is)` by
    (simp[Abbr `ss`, rich_listTheory.TAKE_SUC_BY_TAKE, rich_listTheory.SNOC_APPEND,
      FOLDL_APPEND] >> gvs[scan_inst_def, mode_load_opcode_def]) >>
  Cases_on `bs = []` >- simp[] >>
  `0 < h.cg_length` by (Cases_on `bs` >> gvs[] >> decide_tac) >>
  `w2n w + 32 <= h.cg_dst \/ h.cg_dst + h.cg_length <= w2n w` by
    (irule mm_local_load_pending_disjoint >> metis_tac[]) >>
  simp[]
QED

(* Successful nonterminating list execution with the exec_block index update. *)
Definition mm_local_exec_prefix_def:
  (mm_local_exec_prefix fuel ctx [] s t <=> t = s) /\
  (mm_local_exec_prefix fuel ctx (i::is) s t <=>
    ~is_terminator i.inst_opcode /\
    ?u. step_inst fuel ctx i s = OK u /\
      mm_local_exec_prefix fuel ctx is
        (u with vs_inst_idx := SUC s.vs_inst_idx) t)
End

Theorem mm_local_exec_prefix_append:
  !xs ys fuel ctx s t.
    mm_local_exec_prefix fuel ctx (xs ++ ys) s t <=>
    ?u. mm_local_exec_prefix fuel ctx xs s u /\
        mm_local_exec_prefix fuel ctx ys u t
Proof
  Induct_on `xs` >> simp[mm_local_exec_prefix_def] >> metis_tac[]
QED

Theorem mm_local_exec_prefix_single:
  mm_local_exec_prefix fuel ctx [i] s t <=>
  ~is_terminator i.inst_opcode /\
  ?u. step_inst fuel ctx i s = OK u /\
    t = u with vs_inst_idx := SUC s.vs_inst_idx
Proof
  simp[mm_local_exec_prefix_def]
QED

Theorem mm_local_exec_prefix_cursor:
  !is fuel ctx s t.
    mm_local_exec_prefix fuel ctx is s t ==>
    t.vs_inst_idx = s.vs_inst_idx + LENGTH is
Proof
  Induct_on `is` >> simp[mm_local_exec_prefix_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem mm_local_exec_prefix_suffix:
  !xs fuel ctx s t ys.
    mm_local_exec_prefix fuel ctx xs s t ==>
    dft_exec_suffix fuel ctx (xs ++ ys) s = dft_exec_suffix fuel ctx ys t
Proof
  Induct_on `xs` >> simp[mm_local_exec_prefix_def] >> rpt strip_tac >>
  simp[Once dft_exec_suffix_def] >> metis_tac[]
QED

Theorem mm_local_flat_map_supply_append:
  !xs ys f s out t tail u.
    mm_flat_map_supply f s xs = (out,t) /\
    mm_flat_map_supply f t ys = (tail,u) ==>
    mm_flat_map_supply f s (xs ++ ys) = (out ++ tail,u)
Proof
  Induct_on `xs` >> simp[mm_flat_map_supply_def] >> rpt gen_tac >>
  Cases_on `f s h` >> Cases_on `mm_flat_map_supply f r xs` >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[pairTheory.pair_case_eq]
QED

Theorem mm_local_hard_barrier_pending_empty:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state (TAKE n is) /\
  n < LENGTH is /\
  scan_inst (dfg_build_function fn0) mode ss (EL n is) = hard_barrier ss ==>
  mm_local_pending_indices is gs n = []
Proof
  strip_tac >>
  Cases_on `mm_local_pending_indices is gs n` >- simp[] >>
  rename1 `mm_local_pending_indices is gs n = j::js` >>
  `MEM j (mm_local_pending_indices is gs n)` by simp[] >>
  `?A. MEM A ss.ss_copies /\ MEM (EL j is).inst_id A.cg_inst_ids` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_canonical_pending_copy_owner >>
     disch_then irule >> simp[] >> qexistsl [`mode`,`n`] >> gvs[]) >>
  qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `scan_inst (dfg_build_function fn0) mode ss (EL n is) <> hard_barrier ss` by
    (irule mm_local_indexed_future_nonbarrier >> metis_tac[]) >>
  metis_tac[]
QED

Theorem mm_local_hard_barrier_pending_next_empty:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state (TAKE n is) /\
  n < LENGTH is /\
  scan_inst (dfg_build_function fn0) mode ss (EL n is) = hard_barrier ss ==>
  mm_local_pending_indices is gs (SUC n) = []
Proof
  strip_tac >>
  Cases_on `mm_local_pending_indices is gs (SUC n)` >- simp[] >>
  rename1 `mm_local_pending_indices is gs (SUC n) = j::js` >>
  `MEM j (mm_local_pending_indices is gs (SUC n))` by simp[] >>
  `?A. MEM A (FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state (TAKE (SUC n) is)).ss_copies /\
    MEM (EL j is).inst_id A.cg_inst_ids` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_canonical_pending_copy_owner >>
     disch_then irule >> simp[] >> qexistsl [`mode`,`SUC n`] >> gvs[]) >>
  gvs[rich_listTheory.TAKE_SUC_BY_TAKE, rich_listTheory.SNOC_APPEND,
    FOLDL_APPEND, hard_barrier_def]
QED

Theorem mm_local_cut_literal_load_read[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ (EL n is).inst_opcode = MLOAD /\
  (EL n is).inst_operands = [Lit w] /\ (EL n is).inst_outputs = [out] /\
  mm_local_cut is gs H n excluded pc t ==>
  read_memory (w2n w) 32 (H n) = read_memory (w2n w) 32 t
Proof
  strip_tac >>
  `mm_local_pending (mm_local_write_capture is H n)
    (mm_local_pending_indices is gs n) (H n) t` by fs[mm_local_cut_def] >>
  qpat_x_assum `mm_local_pending _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_def]) >>
  irule venomWriteReplayPropsTheory.read_write_log_memory >> qexists `ws` >> simp[] >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  irule mm_local_pending_literal_load_disjoint >> metis_tac[]
QED

Theorem mm_local_cut_representative_protected_operands[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM g gs /\ rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  mm_local_cut is gs H r excluded pc t /\
  (EL r is).inst_opcode = MSTORE /\ g.cg_length = 32 ==>
  !w. MEM (Var w) (EL r is).inst_operands ==>
    lookup_var w (H r) = lookup_var w t
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `ALOOKUP rs (EL r is).inst_id = SOME g /\ ~MEM (EL r is).inst_id ns` by
    metis_tac[mm_local_prefix_selected_rep, EL_MEM] >>
  `apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = ([EL r is],es)` by
    simp[apply_groups_inst_supply_def] >>
  `w NOTIN excluded` by
    (irule (cj 3 mm_local_retained_operand_protected) >>
     simp[] >> metis_tac[EL_MEM, venomWfPropsTheory.operand_var_in_inst_uses]) >>
  fs[mm_local_cut_def]
QED

Theorem mm_local_cut_memory_state_equiv[local]:
  mm_local_cut is gs H n excluded pc t ==>
  state_equiv excluded ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t
Proof
  strip_tac >>
  gvs[mm_local_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
    venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_cut_memory_independent_step[local]:
  mm_local_cut is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
  ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  Eff_MEMORY NOTIN read_effects i.inst_opcode /\
  Eff_MEMORY NOTIN write_effects i.inst_opcode /\
  step_inst fuel ctx i (H n) = OK u ==>
  ?v. step_inst fuel ctx i t = OK v /\
    state_equiv excluded
      (u with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) v
Proof
  strip_tac >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    metis_tac[mm_local_cut_memory_state_equiv] >>
  `step_inst fuel ctx i ((H n) with vs_memory := t.vs_memory) =
    OK (u with vs_memory := t.vs_memory)` by
    metis_tac[passSharedFieldTheory.step_inst_mem_frame] >>
  `step_inst fuel ctx i
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) =
    OK (u with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>)` by
    (irule passSharedFieldTheory.step_inst_mem_frame >>
     simp[analysisSimProofsBaseTheory.step_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def]) >>
  drule_all removeUnusedProofsTheory.step_inst_result_equiv_full >>
  disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
  Cases_on `step_inst fuel ctx i t` >> simp[result_equiv_def]
QED

Theorem mm_local_cut_empty_state_equiv[local]:
  mm_local_cut is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] ==>
  state_equiv excluded ((H n) with vs_inst_idx := pc) t
Proof
  strip_tac >>
  gvs[mm_local_cut_def, mm_local_pending_empty] >>
  gvs[state_equiv_frame, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
    venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_cut_empty_step[local]:
  mm_local_cut is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\
  step_inst fuel ctx i (H n) = OK u ==>
  ?v. step_inst fuel ctx i t = OK v /\
    state_equiv excluded (u with vs_inst_idx := pc) v
Proof
  strip_tac >>
  `state_equiv excluded ((H n) with vs_inst_idx := pc) t` by
    metis_tac[mm_local_cut_empty_state_equiv] >>
  `step_inst fuel ctx i ((H n) with vs_inst_idx := pc) =
    OK (u with vs_inst_idx := pc)` by
    (Cases_on `i.inst_opcode = INVOKE`
     >- simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
     simp[analysisSimProofsBaseTheory.step_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def]) >>
  drule_all removeUnusedProofsTheory.step_inst_result_equiv_full >>
  disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
  Cases_on `step_inst fuel ctx i t` >> simp[result_equiv_def]
QED

Theorem mm_local_cut_empty_transition[local]:
  mm_local_cut is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] /\
  mm_local_pending_indices is gs (SUC n) = [] /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\
  step_inst fuel ctx i (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?v. step_inst fuel ctx i t = OK v /\
    mm_local_cut is gs H (SUC n) excluded (SUC pc)
      (v with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  drule_all mm_local_cut_empty_step >> strip_tac >>
  qexists `v` >> simp[] >>
  `mm_local_epoch_start is gs (SUC n) = SUC n` by
    simp[mm_local_epoch_start_suc] >>
  gvs[mm_local_cut_def, mm_local_pending_empty, state_equiv_frame,
    rich_listTheory.COUNT_LIST_def,
    mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.lookup_var_def, venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_cut_barrier_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE n is) /\
  scan_inst (dfg_build_function fn0) Mem2Mem ss (EL n is) = hard_barrier ss /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es') /\
  mm_local_cut is gs H n excluded pc t /\
  ~is_terminator (EL n is).inst_opcode /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_cut is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >>
  `mm_local_pending_indices is gs n = []` by
    metis_tac[mm_local_hard_barrier_pending_empty] >>
  `mm_local_pending_indices is gs (SUC n) = []` by
    metis_tac[mm_local_hard_barrier_pending_next_empty] >>
  `!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded` by
    (qx_gen_tac `v` >> disch_tac >>
     irule (cj 3 mm_local_retained_operand_protected) >>
     simp[] >> metis_tac[EL_MEM, venomWfPropsTheory.operand_var_in_inst_uses]) >>
  drule_all mm_local_cut_empty_transition >> strip_tac >>
  qexists `v with vs_inst_idx := SUC pc` >> simp[] >>
  gvs[mm_local_exec_prefix_single] >> fs[mm_local_cut_def]
QED

Theorem mm_local_mem2mem_scan_classification[local]:
  scan_inst dfg mode ss i <> hard_barrier ss ==>
  ((?w out. i.inst_opcode = (mode_load_opcode mode) /\ i.inst_operands = [Lit w] /\
       i.inst_outputs = [out]) \/
   (?dst v src. i.inst_opcode = MSTORE /\
       i.inst_operands = [Lit dst; Var v] /\
       FLOOKUP ss.ss_loads v = SOME src) \/
   (?dst src len. i.inst_opcode = (mode_copy_opcode mode) /\
       i.inst_operands = [Lit dst; Lit src; Lit len]) \/
   (i.inst_opcode NOTIN {(mode_load_opcode mode); MSTORE; (mode_copy_opcode mode)} /\ ~is_volatile_memory i))
Proof
  simp[scan_inst_def] >>
  Cases_on `i.inst_opcode = (mode_load_opcode mode)` >> simp[]
  >- (simp[scan_load_def] >> rpt BasicProvers.TOP_CASE_TAC >>
      gvs[operand_lit_val_def] >>
      rename1 `i.inst_operands = [a]` >> Cases_on `a` >>
      gvs[operand_lit_val_def]) >>
  Cases_on `i.inst_opcode = MSTORE` >> simp[]
  >- (simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
      gvs[operand_lit_val_def, operand_var_def] >>
      rename1 `i.inst_operands = [a;b]` >>
      Cases_on `a` >> Cases_on `b` >>
      gvs[operand_lit_val_def, operand_var_def]) >>
  Cases_on `i.inst_opcode = (mode_copy_opcode mode)` >> simp[]
  >- (simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
      gvs[operand_lit_val_def] >>
      rename1 `i.inst_operands = [a;b;c]` >>
      map_every Cases_on [`a`,`b`,`c`] >> gvs[operand_lit_val_def]) >>
  Cases_on `is_volatile_memory i` >> simp[]
QED

Theorem mm_local_mem2mem_nonbarrier_write_owner[local]:
  bb.bb_instructions = pre ++ i::post /\
  ss = FOLDL (scan_inst dfg mode) empty_scan_state pre /\
  i.inst_opcode IN {MSTORE; (mode_copy_opcode mode)} /\
  scan_inst dfg mode ss i <> hard_barrier ss ==>
  ?g. MEM g (scan_block dfg mode bb).ss_flushed /\
      MEM i.inst_id g.cg_inst_ids
Proof
  strip_tac >>
  `(mode_load_opcode mode) <> MSTORE /\
   (mode_copy_opcode mode) <> MSTORE /\
   (mode_load_opcode mode) <> (mode_copy_opcode mode)` by
    (Cases_on `mode` >> simp[mode_load_opcode_def, mode_copy_opcode_def]) >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies` by
    (gvs[] >> irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  drule mm_local_mem2mem_scan_classification >> strip_tac >> fs[]
  >- (`?h. MEM h (scan_store dfg mode ss i).ss_copies /\
        mm_local_copy_ancestor
          <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
            cg_inst_ids := [i.inst_id] ++
              (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id])|> h` by
        (irule mm_local_store_new_fragment >> gvs[operand_var_def, operand_lit_val_def]) >>
      `?g. MEM g (scan_block dfg mode bb).ss_flushed /\
        mm_local_copy_ancestor h g` by
        (irule mm_local_prefix_final_fragment >>
         qexistsl [`post`,`pre ++ [i]`] >>
         gvs[FOLDL_APPEND, scan_inst_def, MEM_APPEND]) >>
      gvs[mm_local_copy_ancestor_def] >> metis_tac[MEM_APPEND, MEM]) >>
  `?h. MEM h (scan_bulk_copy mode ss i).ss_copies /\
    mm_local_copy_ancestor
      <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
        cg_inst_ids := [i.inst_id]|> h` by
    (irule mm_local_bulk_new_fragment >> simp[operand_lit_val_def]) >>
  `?g. MEM g (scan_block dfg mode bb).ss_flushed /\
    mm_local_copy_ancestor h g` by
    (irule mm_local_prefix_final_fragment >>
     qexistsl [`post`,`pre ++ [i]`] >>
     gvs[FOLDL_APPEND, scan_inst_def, MEM_APPEND]) >>
  gvs[mm_local_copy_ancestor_def] >> metis_tac[]
QED

Theorem mm_local_mem2mem_ordinary_classification:
  bb.bb_instructions = pre ++ i::post /\
  ss = FOLDL (scan_inst dfg mode) empty_scan_state pre /\
  (i.inst_opcode IN {MSTORE; (mode_copy_opcode mode)} ==>
    ~(?g. MEM g (scan_block dfg mode bb).ss_flushed /\
          MEM i.inst_id g.cg_inst_ids)) ==>
  scan_inst dfg mode ss i = hard_barrier ss \/
  (?w out. i.inst_opcode = (mode_load_opcode mode) /\ i.inst_operands = [Lit w] /\
     i.inst_outputs = [out]) \/
  (i.inst_opcode NOTIN {(mode_load_opcode mode); MSTORE; (mode_copy_opcode mode)} /\ ~is_volatile_memory i)
Proof
  strip_tac >>
  Cases_on `scan_inst dfg mode ss i = hard_barrier ss` >- simp[] >>
  `i.inst_opcode NOTIN {MSTORE; (mode_copy_opcode mode)}` by
    metis_tac[mm_local_mem2mem_nonbarrier_write_owner] >>
  drule mm_local_mem2mem_scan_classification >> fs[]
QED

Theorem mm_local_nonvolatile_effects:
  ~is_volatile_memory i ==>
  i.inst_opcode <> INVOKE /\ ~is_ext_call_op i.inst_opcode /\
  i.inst_opcode NOTIN {CALLDATACOPY; DLOADBYTES} /\
  Eff_MEMORY NOTIN read_effects i.inst_opcode /\
  Eff_MEMORY NOTIN write_effects i.inst_opcode
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_volatile_memory_def, venomEffectsTheory.read_effects_def,
    venomEffectsTheory.write_effects_def, venomInstTheory.is_ext_call_op_def,
    venomEffectsTheory.all_effects_def]
QED

Theorem mm_local_nonwrite_successor:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  n < LENGTH is /\
  (EL n is).inst_opcode NOTIN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
  mm_local_write_capture is H (SUC n) = mm_local_write_capture is H n
Proof
  strip_tac >>
  `(EL n is).inst_opcode <> MSTORE /\ (EL n is).inst_opcode <> MCOPY /\
   (EL n is).inst_opcode <> CALLDATACOPY /\ (EL n is).inst_opcode <> DLOADBYTES` by fs[] >>
  conj_tac
  >- (`!g. MEM g gs ==> rep_of_group is g <> SOME ((EL n is).inst_id,g)` by
        (rpt strip_tac >> drule_all mm_local_canonical_rep_write >> fs[]) >>
      simp[NoAsms, mm_local_pending_indices_def, rich_listTheory.COUNT_LIST_SNOC,
        rich_listTheory.SNOC_APPEND, FILTER_APPEND] >>
      simp[] >> rewrite_tac[rich_listTheory.FILTER_EQ] >>
      qx_gen_tac `j` >> simp[MEM_COUNT_LIST] >> strip_tac >>
      eq_tac >> strip_tac >> gvs[]
      >- (qexistsl [`g`,`r`] >> simp[] >> decide_tac) >>
      `r <> n` by metis_tac[] >> qexistsl [`g`,`r`] >> simp[] >> decide_tac) >>
  rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `j` >>
  (Cases_on `j = n` >- gvs[mm_local_write_capture_def]) >>
  `j < SUC n <=> j < n` by decide_tac >> simp[mm_local_write_capture_def]
QED

Theorem mm_local_cut_memory_preserving_renew[local]:
  mm_local_cut is gs H n excluded pc t /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
  mm_local_write_capture is H (SUC n) = mm_local_write_capture is H n /\
  (H (SUC n)).vs_memory = (H n).vs_memory /\
  v.vs_memory = t.vs_memory /\
  state_equiv excluded
    ((H (SUC n)) with <|vs_memory := v.vs_memory; vs_inst_idx := SUC pc|>) v ==>
  mm_local_cut is gs H (SUC n) excluded (SUC pc) v
Proof
  strip_tac >>
  `v.vs_inst_idx = SUC pc /\
   mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame v /\
   (!x. x NOTIN excluded ==> lookup_var x (H (SUC n)) = lookup_var x v)` by
    gvs[state_equiv_frame, mm_local_nonmemory_frame_def,
      stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
      venomStateTheory.venom_state_component_equality] >>
  `mm_local_epoch_start is gs n <= n` by
    (irule mm_local_epoch_start_bound >> qexistsl [`gs`,`is`] >> simp[]) >>
  gvs[mm_local_cut_def] >> conj_tac
  >- (gvs[mm_local_pending_def] >> qexists `ws` >> simp[] >>
      irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]) >>
  Cases_on `mm_local_pending_indices is gs n = []`
  >- gvs[mm_local_epoch_start_suc, mm_local_pending_empty,
       rich_listTheory.COUNT_LIST_def] >>
  `SUC n - mm_local_epoch_start is gs n = SUC (n - mm_local_epoch_start is gs n)` by
    decide_tac >>
  simp[mm_local_epoch_start_suc, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, MAP_APPEND, FOLDL_APPEND,
    mm_local_write_capture_future]
QED

Theorem mm_local_cut_nonmemory_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (EL n is).inst_opcode NOTIN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  ~is_terminator (EL n is).inst_opcode /\
  ~is_ext_call_op (EL n is).inst_opcode /\ (EL n is).inst_opcode <> INVOKE /\
  Eff_MEMORY NOTIN read_effects (EL n is).inst_opcode /\
  Eff_MEMORY NOTIN write_effects (EL n is).inst_opcode /\
  mm_local_cut is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_cut is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
   mm_local_write_capture is H (SUC n) = mm_local_write_capture is H n` by
    metis_tac[mm_local_nonwrite_successor] >>
  `?v. step_inst fuel ctx (EL n is) t = OK v /\
    state_equiv excluded
      (u with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) v` by
    (Cases_on `(EL n is).inst_opcode = ALLOCA`
     >- (`state_equiv excluded
           ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
           metis_tac[mm_local_cut_memory_state_equiv] >>
         `step_inst fuel ctx (EL n is)
           ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) =
           OK (u with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>)` by
           (irule venomExecutionReplayPropsTheory.alloca_memory_frame >>
            simp[analysisSimProofsBaseTheory.step_inst_idx_indep,
              instIdxIndepTheory.exec_result_map_def]) >>
         drule_all removeUnusedProofsTheory.step_inst_result_equiv_full >>
         disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
         Cases_on `step_inst fuel ctx (EL n is) t` >> simp[result_equiv_def]) >>
     `~is_alloca_op (EL n is).inst_opcode` by
       (Cases_on `(EL n is).inst_opcode` >> fs[venomInstTheory.is_alloca_op_def]) >>
     metis_tac[mm_local_cut_memory_independent_step]) >>
  `u.vs_memory = (H n).vs_memory /\ v.vs_memory = t.vs_memory` by
    (Cases_on `(EL n is).inst_opcode = ALLOCA`
     >- metis_tac[venomMemPropsTheory.step_inst_alloca_preserves_memory,
          venomInstTheory.is_alloca_op_def] >>
     `~is_alloca_op (EL n is).inst_opcode` by
       (Cases_on `(EL n is).inst_opcode` >> fs[venomInstTheory.is_alloca_op_def]) >>
     metis_tac[passSharedFieldTheory.step_inst_preserves_all]) >>
  `mm_local_cut is gs H (SUC n) excluded (SUC pc)
    (v with vs_inst_idx := SUC pc)` by
    (irule mm_local_cut_memory_preserving_renew >>
     simp[] >> reverse conj_tac
     >- (qexists `t` >> gvs[]) >>
     drule execEquivProofsTheory.state_equiv_inst_idx >>
     disch_then (qspec_then `SUC pc` mp_tac) >> simp[]) >>
  qexists `v with vs_inst_idx := SUC pc` >> simp[] >>
  gvs[mm_local_exec_prefix_single] >> fs[mm_local_cut_def]
QED

Theorem mm_local_cut_literal_load_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (EL n is).inst_opcode = MLOAD /\ (EL n is).inst_operands = [Lit w] /\
  (EL n is).inst_outputs = [out] /\
  mm_local_cut is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_cut is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >>
  `read_memory (w2n w) 32 (H n) = read_memory (w2n w) 32 t` by
    metis_tac[mm_local_cut_literal_load_read] >>
  `mload (w2n w) (H n) = mload (w2n w) t` by
    gvs[venomStateTheory.mload_def, venomStateTheory.read_memory_def] >>
  `u = update_var out (mload (w2n w) t) (H n) /\
   step_inst fuel ctx (EL n is) t = OK (update_var out (mload (w2n w) t) t)` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomExecSemanticsTheory.exec_read1_def,
      venomStateTheory.eval_operand_def] >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
   mm_local_write_capture is H (SUC n) = mm_local_write_capture is H n` by
    (irule mm_local_nonwrite_successor >> simp[] >> metis_tac[]) >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    metis_tac[mm_local_cut_memory_state_equiv] >>
  drule stateEquivProofsTheory.foldl_update_var_state_equiv >>
  disch_then (qspec_then `[(out,mload (w2n w) t)]` assume_tac) >>
  qexists `update_var out (mload (w2n w) t) t with vs_inst_idx := SUC pc` >>
  conj_tac
  >- (gvs[mm_local_exec_prefix_single, venomInstTheory.is_terminator_def] >>
      fs[mm_local_cut_def]) >>
  irule mm_local_cut_memory_preserving_renew >> simp[] >>
  reverse conj_tac >- (qexists `t` >> gvs[]) >>
  gvs[state_equiv_frame, venomStateTheory.update_var_def,
    venomStateTheory.lookup_var_def, stateFrameTheory.state_frame_def,
    venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_cut_ordinary_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  ((EL n is).inst_opcode IN {MSTORE; MCOPY} ==>
    ~(?g. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids)) /\
  apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es') /\
  mm_local_cut is gs H n excluded pc t /\
  ~is_terminator (EL n is).inst_opcode /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_cut is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >>
  `bb.bb_instructions = TAKE n is ++ EL n is::DROP (SUC n) is` by
    (qspec_then `n` (qspec_then `is` mp_tac) rich_listTheory.TAKE_DROP_SUC >> simp[]) >>
  `scan_inst (dfg_build_function fn0) Mem2Mem
      (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is))
      (EL n is) = hard_barrier
      (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is)) \/
   (?w out. (EL n is).inst_opcode = MLOAD /\ (EL n is).inst_operands = [Lit w] /\
       (EL n is).inst_outputs = [out]) \/
   ((EL n is).inst_opcode NOTIN {MLOAD; MSTORE; MCOPY} /\
      ~is_volatile_memory (EL n is))` by
    (mp_tac (Q.INST [`mode` |-> `Mem2Mem`,
       `dfg` |-> `dfg_build_function fn0`, `pre` |-> `TAKE n is`,
       `post` |-> `DROP (SUC n) is`, `i` |-> `EL n is`,
       `ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
         empty_scan_state (TAKE n is)`]
       (SPEC_ALL mm_local_mem2mem_ordinary_classification)) >>
     pure_rewrite_tac[mode_load_opcode_def, mode_copy_opcode_def] >>
     impl_tac >- metis_tac[] >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `bb.bb_instructions = _ ++ _` kall_tac >>
  pop_assum strip_assume_tac
  >- (irule mm_local_cut_barrier_transition >> metis_tac[])
  >- (irule mm_local_cut_literal_load_transition >> metis_tac[]) >>
  drule mm_local_nonvolatile_effects >> strip_tac >>
  `!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded` by
    (qx_gen_tac `v` >> disch_tac >>
     irule (cj 3 mm_local_retained_operand_protected) >>
     simp[] >> metis_tac[EL_MEM, venomWfPropsTheory.operand_var_in_inst_uses]) >>
  irule mm_local_cut_nonmemory_transition >> fs[] >> metis_tac[]
QED

Theorem mm_local_cut_init:
  h = phi_prefix_length is /\
  state_equiv excluded (H h with vs_inst_idx := pc) t ==>
  mm_local_cut is gs H h excluded pc t
Proof
  strip_tac >>
  `mm_local_pending_indices is gs h = []` by
    (Cases_on `mm_local_pending_indices is gs h` >> simp[] >>
     rename1 `mm_local_pending_indices is gs h = j::js` >>
     `MEM j (mm_local_pending_indices is gs h)` by simp[] >>
     drule mm_local_pending_indices_after_phis >>
     gvs[mm_local_pending_indices_mem]) >>
  `h <= mm_local_epoch_start is gs h` by
    (gvs[] >> irule mm_local_epoch_start_after_phis >> simp[]) >>
  `mm_local_epoch_start is gs h <= h` by
    (irule mm_local_epoch_start_bound >> qexistsl [`gs`,`is`] >> simp[]) >>
  `mm_local_epoch_start is gs h = h` by decide_tac >>
  gvs[state_equiv_frame, stateFrameTheory.state_frame_def,
    venomStateTheory.venom_state_component_equality,
    mm_local_cut_def, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, mm_local_pending_empty,
    rich_listTheory.COUNT_LIST_def, venomStateTheory.lookup_var_def]
QED

Theorem mm_local_runtime_representative_operand_frame[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (!q. h <= q /\ q <= r ==> ~is_terminator (EL q is).inst_opcode /\
    ?z. step_inst fuel ctx (EL q is) (H q) = OK z /\
      H (SUC q) = z with vs_inst_idx := SUC (H q).vs_inst_idx) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\ a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js (H r) t /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  ((EL r is).inst_opcode = MSTORE /\ g.cg_length = 32 ==>
    !w. MEM (Var w) (EL r is).inst_operands ==>
      lookup_var w (H r) = lookup_var w t) /\
  fresh_inst_id es = (lid,es1) /\ fresh_ir_var es1 = (v,es2) /\
  (!x. x IN P ==> x <> v) /\
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\ g.cg_length < dimword (:256) /\
  a' = mm_local_epoch_start is gs (SUC r) ==>
  ?out es' fin.
    apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = (out,es') /\
    ((?i. out = [i] /\ step_inst fuel ctx i t = OK fin) \/
     (?i j mid. out = [i;j] /\ step_inst fuel ctx i t = OK mid /\
       step_inst fuel ctx j (mid with vs_inst_idx := SUC t.vs_inst_idx) = OK fin)) /\
    (!x. x IN P ==> lookup_var x fin = lookup_var x t) /\
    mm_local_nonmemory_frame fin = mm_local_nonmemory_frame t /\
    mm_local_pending cap (mm_local_pending_indices is gs (SUC r))
      (H (SUC r)) (fin with vs_inst_idx := t.vs_inst_idx + LENGTH out) /\
    (fin with vs_inst_idx := t.vs_inst_idx + LENGTH out).vs_memory =
      (FOLDL (\st q. if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
        case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
        (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL r is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `ALOOKUP rs (EL r is).inst_id = SOME g /\ ~MEM (EL r is).inst_id ns` by
    (qpat_x_assum `ns = _` SUBST_ALL_TAC >>
     qpat_x_assum `rs = _` SUBST_ALL_TAC >>
     qpat_x_assum `is = _` SUBST_ALL_TAC >>
     qpat_x_assum `gs = _` SUBST_ALL_TAC >>
     drule_all mm_local_prefix_selected_rep >> simp[]) >>
  `!q. h <= q /\ q < r ==> ~is_terminator (EL q is).inst_opcode /\
    ?z. step_inst fuel ctx (EL q is) (H q) = OK z /\
      H (SUC q) = z with vs_inst_idx := SUC (H q).vs_inst_idx` by
    metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `?out es' fin.
    apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = (out,es') /\
    ((?i. out = [i] /\ step_inst fuel ctx i t = OK fin) \/
     (?i j mid. out = [i;j] /\ step_inst fuel ctx i t = OK mid /\
       step_inst fuel ctx j (mid with vs_inst_idx := SUC t.vs_inst_idx) = OK fin)) /\
    (!x. x IN P ==> lookup_var x fin = lookup_var x t) /\
    mm_local_nonmemory_frame fin = mm_local_nonmemory_frame t /\
    fin.vs_memory = (write_memory_with_expansion g.cg_dst
      (read_memory g.cg_src g.cg_length t) t).vs_memory` by
    (Cases_on `g.cg_length = 32`
     >- (Cases_on `(EL r is).inst_opcode = MSTORE`
         >- suspend "retained"
         >> suspend "word") >> suspend "bulk") >>
  suspend "renew"
QED

Resume mm_local_runtime_representative_operand_frame[bulk]:
  drule_all mm_local_mem2mem_bulk_runtime >>
  disch_then (qspecl_then [`t`,`es`,`fuel`,`ctx`] strip_assume_tac) >>
  qexistsl [`[out]`,`es`,`fin`] >> simp[]
QED
Resume mm_local_runtime_representative_operand_frame[word]:
  drule_all mm_local_mem2mem_word_runtime >>
  disch_then (qspecl_then [`t`,`fuel`,`ctx`] strip_assume_tac) >>
  `mm_local_nonmemory_frame fin = mm_local_nonmemory_frame t` by
    (qpat_x_assum `(_ with vs_inst_idx := SUC (SUC _)) = _`
       (mp_tac o AP_TERM ``mm_local_nonmemory_frame``) >> simp[]) >>
  qexistsl [`[load;store]`,`es2`,`fin`] >> simp[] >> metis_tac[]
QED
Resume mm_local_runtime_representative_operand_frame[retained]:
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `?dst w src. (EL r is).inst_operands = [Lit dst; Var w] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE r is)).ss_loads w = SOME src` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
       (REWRITE_RULE [mode_copy_opcode_def]
         (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >>
     disch_then (qspecl_then [`r`,`is`,`g`] mp_tac) >>
     simp[] >> impl_tac >- gvs[] >> metis_tac[]) >>
  `g.cg_dst = w2n dst /\ lookup_var w (H r) = SOME (mload g.cg_src t)` by
    (irule mm_local_runtime_representative_store_payload >> metis_tac[]) >>
  `apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = ([EL r is],es)` by
    simp[apply_groups_inst_supply_def] >>
  `lookup_var w (H r) = lookup_var w t` by
    (qpat_x_assum `_ /\ _ ==> !w. _` mp_tac >> simp[]) >>
  qpat_assum `!q. h <= q /\ q <= r ==> _` (qspec_then `r` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all mm_local_mem2mem_retained_payload >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  qexistsl [`[EL r is]`,`es`,`fin`] >> simp[] >> gvs[]
QED
Resume mm_local_runtime_representative_operand_frame[renew]:
  markerLib.RESUME_TAC >>
  `fin.vs_memory = (FOLDL (\st q.
    if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory` by
    (irule mm_local_runtime_retained_renew >> metis_tac[]) >>
  `FILTER (\j. mm_local_rep_index is gs j <> r) js =
    mm_local_pending_indices is gs (SUC r)` by
    (`~MEM r (mm_local_pending_indices is gs (SUC r))` by
       (strip_tac >>
        qpat_x_assum `MEM r (mm_local_pending_indices _ _ _)`
          (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
        rename1 `SUC r <= rr` >>
        `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
        `rr = r` by (irule mm_local_write_rep_unique >> metis_tac[]) >> decide_tac) >>
     `FILTER (\j. j < r) (mm_local_pending_indices is gs (SUC r)) =
       mm_local_pending_indices is gs (SUC r)` by
       (rewrite_tac[FILTER_EQ_ID, EVERY_MEM] >> qx_gen_tac `birth` >> strip_tac >>
        drule (iffLR mm_local_pending_indices_mem) >> strip_tac >>
        `birth <> r` by metis_tac[] >> simp[] >> decide_tac) >>
     `r <= LENGTH is` by decide_tac >>
     qpat_x_assum `js = _` SUBST_ALL_TAC >>
     `FILTER (\j. mm_local_rep_index is gs j <> r) (mm_local_pending_indices is gs r) =
       FILTER (\j. SUC r <= mm_local_rep_index is gs j) (mm_local_pending_indices is gs r)` suffices_by
       metis_tac[mm_local_canonical_pending_keep] >>
     rewrite_tac[rich_listTheory.FILTER_EQ] >> qx_gen_tac `x` >> strip_tac >>
     `r <= mm_local_rep_index is gs x` by
       (drule (iffLR mm_local_pending_indices_mem) >> strip_tac >>
        `x < LENGTH is` by decide_tac >>
        metis_tac[mm_local_rep_index_eq, pred_setTheory.IN_INSERT]) >> BETA_TAC >> decide_tac) >>
  `(EL r is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    metis_tac[mm_local_canonical_rep_write] >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `(EL r is).inst_opcode = MSTORE \/ (EL r is).inst_opcode = MCOPY` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
       (REWRITE_RULE [mode_copy_opcode_def]
         (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >>
     disch_then (qspec_then `r` mp_tac) >> gvs[] >> metis_tac[]) >>
  `?d bs. cap r = SOME (d,bs) /\
    (H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory` by
    (qpat_assum `!q. h <= q /\ q <= r ==> _` (qspec_then `r` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `cap = _` SUBST_ALL_TAC >>
     irule mm_local_interval_runtime_capture >>
     `SUC r <= LENGTH is /\ r < SUC r` by decide_tac >> metis_tac[]) >>
  `mm_local_pending cap (FILTER (\j. mm_local_rep_index is gs j <> r) js)
    (H (SUC r)) fin` by
    (irule mm_local_runtime_pending_discharge >> metis_tac[]) >>
  qexistsl [`out`,`es'`,`fin`] >> simp[] >>
  gvs[mm_local_pending_def] >>
  qexists `ws'` >> simp[] >> irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]
QED
Finalise mm_local_runtime_representative_operand_frame

Theorem mm_local_runtime_representative_transition_frame[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (!q. h <= q /\ q <= r ==> ~is_terminator (EL q is).inst_opcode /\
    ?z. step_inst fuel ctx (EL q is) (H q) = OK z /\
      H (SUC q) = z with vs_inst_idx := SUC (H q).vs_inst_idx) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\ a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js (H r) t /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  excluded = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  (!v. v NOTIN excluded ==> lookup_var v (H r) = lookup_var v t) /\
  fresh_inst_id es = (lid,es1) /\ fresh_ir_var es1 = (v,es2) /\
  (!x. x IN P ==> x <> v) /\
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\ g.cg_length < dimword (:256) /\
  a' = mm_local_epoch_start is gs (SUC r) ==>
  ?out es' fin.
    apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = (out,es') /\
    ((?i. out = [i] /\ step_inst fuel ctx i t = OK fin) \/
     (?i j mid. out = [i;j] /\ step_inst fuel ctx i t = OK mid /\
       step_inst fuel ctx j (mid with vs_inst_idx := SUC t.vs_inst_idx) = OK fin)) /\
    (!x. x IN P ==> lookup_var x fin = lookup_var x t) /\
    mm_local_nonmemory_frame fin = mm_local_nonmemory_frame t /\
    mm_local_pending cap (mm_local_pending_indices is gs (SUC r))
      (H (SUC r)) (fin with vs_inst_idx := t.vs_inst_idx + LENGTH out) /\
    (fin with vs_inst_idx := t.vs_inst_idx + LENGTH out).vs_memory =
      (FOLDL (\st q. if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
        case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
        (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory
Proof
  strip_tac >>
  `((EL r is).inst_opcode = MSTORE /\ g.cg_length = 32 ==>
    !w. MEM (Var w) (EL r is).inst_operands ==>
      lookup_var w (H r) = lookup_var w t)` by
    (rpt strip_tac >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by metis_tac[mm_local_prefix_wf_id_distinct] >>
     `ALOOKUP rs (EL r is).inst_id = SOME g /\ ~MEM (EL r is).inst_id ns` by
       metis_tac[mm_local_prefix_selected_rep, EL_MEM] >>
     `apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = ([EL r is],es)` by
       simp[apply_groups_inst_supply_def] >>
     irule mm_local_retained_operand_agreement >>
     goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `apply_groups_inst_supply _ _ _ _ _ = _`)) >>
     qexists `excluded` >>
     simp[venomInstTheory.inst_uses_def,
       passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     gvs[] >> simp[EL_MEM]) >>
  drule_all mm_local_runtime_representative_operand_frame >> simp[]
QED

Theorem mm_local_runtime_representative_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (!q. h <= q /\ q <= r ==> ~is_terminator (EL q is).inst_opcode /\
    ?z. step_inst fuel ctx (EL q is) (H q) = OK z /\
      H (SUC q) = z with vs_inst_idx := SUC (H q).vs_inst_idx) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\ a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js (H r) t /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  excluded = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  (!v. v NOTIN excluded ==> lookup_var v (H r) = lookup_var v t) /\
  fresh_inst_id es = (lid,es1) /\ fresh_ir_var es1 = (v,es2) /\
  (!x. x IN P ==> x <> v) /\
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\ g.cg_length < dimword (:256) /\
  a' = mm_local_epoch_start is gs (SUC r) ==>
  ?out es' fin.
    apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = (out,es') /\
    ((?i. out = [i] /\ step_inst fuel ctx i t = OK fin) \/
     (?i j mid. out = [i;j] /\ step_inst fuel ctx i t = OK mid /\
       step_inst fuel ctx j (mid with vs_inst_idx := SUC t.vs_inst_idx) = OK fin)) /\
    (!x. x IN P ==> lookup_var x fin = lookup_var x t) /\
    mm_local_pending cap (mm_local_pending_indices is gs (SUC r))
      (H (SUC r)) (fin with vs_inst_idx := t.vs_inst_idx + LENGTH out) /\
    (fin with vs_inst_idx := t.vs_inst_idx + LENGTH out).vs_memory =
      (FOLDL (\st q. if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
        case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
        (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory
Proof
  strip_tac >> drule_all mm_local_runtime_representative_transition_frame >>
  strip_tac >> qexistsl [`out`,`es'`,`fin`] >> simp[]
QED

Theorem mm_local_cut_representative_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (!q. h <= q /\ q <= r ==> ~is_terminator (EL q is).inst_opcode /\
    ?z. step_inst fuel ctx (EL q is) (H q) = OK z /\
      H (SUC q) = z with vs_inst_idx := SUC (H q).vs_inst_idx) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  mm_local_cut is gs H r excluded pc t /\
  ((EL r is).inst_opcode = MSTORE /\ g.cg_length = 32 ==>
    !w. MEM (Var w) (EL r is).inst_operands ==>
      lookup_var w (H r) = lookup_var w t) /\
  fresh_inst_id es = (lid,es1) /\ fresh_ir_var es1 = (v,es2) /\ v IN excluded /\
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\ g.cg_length < dimword (:256) ==>
  ?out es' fin.
    apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = (out,es') /\
    ((?i. out = [i] /\ step_inst fuel ctx i t = OK fin) \/
     (?i j mid. out = [i;j] /\ step_inst fuel ctx i t = OK mid /\
       step_inst fuel ctx j (mid with vs_inst_idx := SUC t.vs_inst_idx) = OK fin)) /\
    mm_local_cut is gs H (SUC r) excluded (pc + LENGTH out)
      (fin with vs_inst_idx := pc + LENGTH out)
Proof
  strip_tac >>
  `mm_local_epoch_start is gs r <= r` by
    (irule mm_local_epoch_start_bound >> qexistsl [`gs`,`is`] >> simp[]) >>
  `mm_local_pending (mm_local_write_capture is H (SUC r))
    (mm_local_pending_indices is gs r) (H r) t` by
    (irule mm_local_pending_cap_cong >>
     qexists `mm_local_write_capture is H r` >>
     gvs[mm_local_cut_def] >> rpt strip_tac >>
     sym_tac >> irule mm_local_write_capture_past >>
     gvs[mm_local_pending_indices_mem]) >>
  `t.vs_memory =
    (FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
      case mm_local_write_capture is H (SUC r) q of NONE => st
      | SOME (d,bs) => write_memory_with_expansion d bs st)
      (H (mm_local_epoch_start is gs r))
      (MAP (\q. mm_local_epoch_start is gs r + q)
        (COUNT_LIST (r - mm_local_epoch_start is gs r)))).vs_memory` by
    (qpat_assum `mm_local_cut _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [mm_local_cut_def]) >>
     qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     AP_TERM_TAC >> irule FOLDL_CONG >> simp[] >>
     rpt strip_tac >> gvs[MEM_MAP, MEM_COUNT_LIST] >>
     rename1 `q < r - mm_local_epoch_start is gs r` >>
     `q + mm_local_epoch_start is gs r < r` by decide_tac >>
     `mm_local_write_capture is H r (q + mm_local_epoch_start is gs r) =
      mm_local_write_capture is H (SUC r) (q + mm_local_epoch_start is gs r)` by
       (irule mm_local_write_capture_past >> simp[]) >> simp[]) >>
  `(EL r is).inst_opcode = MSTORE \/ (EL r is).inst_opcode = MCOPY` by
    (`(EL r is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
       (irule mm_local_canonical_rep_write >> metis_tac[]) >>
     `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
     metis_tac[REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)]) >>
  `?z. step_inst fuel ctx (EL r is) (H r) = OK z /\
    H (SUC r) = z with vs_inst_idx := SUC (H r).vs_inst_idx` by metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
  `mm_local_nonmemory_frame (H (SUC r)) = mm_local_nonmemory_frame (H r) /\
    (!w. lookup_var w (H (SUC r)) = lookup_var w (H r))` by
    (`mm_local_nonmemory_frame z = mm_local_nonmemory_frame (H r) /\
      (!w. lookup_var w z = lookup_var w (H r))` by
       (irule mm_local_write_runtime_frame >>
        metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
     gvs[venomStateTheory.lookup_var_def]) >>
  qabbrev_tac `cap = mm_local_write_capture is H (SUC r)` >>
  qabbrev_tac `js = mm_local_pending_indices is gs r` >>
  qabbrev_tac `a = mm_local_epoch_start is gs r` >>
  qabbrev_tac `a' = mm_local_epoch_start is gs (SUC r)` >>
  qmatch_asmsub_abbrev_tac `t.vs_memory = u.vs_memory` >>
  `!x. x IN {x | x NOTIN excluded} ==> x <> v` by simp[] >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all (Q.INST [`P` |-> `{x | x NOTIN excluded}`]
    mm_local_runtime_representative_operand_frame) >>
  strip_tac >> qexistsl [`out`,`es'`,`fin`] >>
  simp[] >>
  gvs[mm_local_cut_def, venomStateTheory.lookup_var_def] >>
  metis_tac[]
QED

Theorem mm_local_representative_finite_bounds:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\ eom < dimword (:256) /\
  (!q. h <= q /\ q <= r ==> (H q).vs_inst_idx = q /\
    (H q).vs_current_bb = bb.bb_label /\
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL q is) (H q) /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u) ==>
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
  g.cg_length < dimword (:256)
Proof
  strip_tac >>
  qabbrev_tac `due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r)` >>
  `?c. g.cg_dst <= c.cg_dst /\
    c.cg_dst + c.cg_length <= g.cg_dst + g.cg_length /\
    c.cg_src = g.cg_src + (c.cg_dst - g.cg_dst) /\
    ((?d s l. (EL r is).inst_opcode = MCOPY /\
      (EL r is).inst_operands = [Lit d; Lit s; Lit l] /\
      c = <|cg_dst := w2n d; cg_src := w2n s; cg_length := w2n l;
        cg_inst_ids := [(EL r is).inst_id]|>) \/
     (?d v src. (EL r is).inst_opcode = MSTORE /\
      (EL r is).inst_operands = [Lit d; Var v] /\
      FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE r is)).ss_loads v = SOME src /\
      c = <|cg_dst := w2n d; cg_src := src; cg_length := 32;
        cg_inst_ids := [(EL r is).inst_id] ++
          (case dfg_get_def (dfg_build_function fn0) v of NONE => []
            | SOME li => [li.inst_id])|>))` by
    (`MEM r (due ++ [r])` by simp[] >>
     `due = FILTER (\j. mm_local_rep_index is gs j = r)
       (mm_local_pending_indices is gs r)` by simp[Abbr `due`] >>
     drule_all (Q.INST [`j` |-> `r`, `s0` |->
       `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE r is)`]
       mm_local_canonical_due_birth_geometry |> SRULE []) >>
     simp[]) >>
  `g.cg_src < dimword (:256)` by
    (Cases_on `(EL r is).inst_opcode = MCOPY`
     >- (gvs[] >> mp_tac (Q.ISPEC `s:256 word` wordsTheory.w2n_lt) >> simp[] >> decide_tac) >>
     gvs[] >> drule mm_local_scan_lookup_origin >> strip_tac >> gvs[] >>
     mp_tac (Q.ISPEC `w:256 word` wordsTheory.w2n_lt) >> simp[] >> decide_tac) >>
  `?j dj lj. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    mm_local_write_footprint (EL j is) = SOME (dj,lj) /\
    dj + lj = g.cg_dst + g.cg_length` by
    (`MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
     drule_all (Q.INST [`cap` |-> `\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
       (mm_local_write_footprint (EL p is))`] mm_local_final_footprint_extent |> SRULE []) >>
     simp[mm_local_group_endpoint_def] >> strip_tac >>
     gvs[AllCaseEqs()] >> PairCases_on `z` >> gvs[] >> metis_tac[]) >>
  `due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r)` by simp[Abbr `due`] >>
  `MEM j (due ++ [r])` by metis_tac[mm_local_canonical_due_footprint_indices] >>
  `h <= j /\ j <= r` by
    (Cases_on `j = r` >- gvs[] >>
     `MEM j (mm_local_pending_indices is gs r)` by gvs[Abbr `due`, MEM_FILTER] >>
     drule mm_local_pending_indices_after_phis >>
     gvs[mm_local_pending_indices_mem] >> decide_tac) >>
  `wf_function (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (irule mm_local_prefix_function_wf >> metis_tac[wf_ssa_def]) >>
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by
    (simp[listTheory.MEM_LUPDATE]) >>
  `lookup_block bb.bb_label (LUPDATE bb index fn0.fn_blocks) = SOME bb` by
    (mp_tac (Q.SPECL [`fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks`, `bb`]
       venomExecProofsTheory.wf_lookup_block) >> simp[]) >>
  ` (H j).vs_inst_idx = j /\ (H j).vs_current_bb = bb.bb_label /\
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL j is) (H j) /\ ?u. step_inst fuel ctx (EL j is) (H j) = OK u` by
    metis_tac[] >>
  drule_all (Q.INST [`j` |-> `j`, `s0` |->
    `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is)`]
    mm_local_canonical_due_birth_geometry |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >> strip_tac >>
  `~in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) (H j)` by
    (simp[contextCodegenRelTheory.in_revert_forward_def] >> strip_tac >>
     `get_instruction bb j = SOME (EL j is)` by (gvs[venomInstTheory.get_instruction_def]) >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
  qpat_x_assum `!q. h <= q /\ q <= r ==> _` kall_tac >>
  qpat_x_assum `static_mem_ok _ _ _ (EL j is) _` mp_tac >>
  simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    EVERY_APPEND] >> strip_tac >>
  (Cases_on `(EL j bb.bb_instructions).inst_opcode = MCOPY`
  >- (gvs[mm_local_write_footprint_def, codegenRelTheory.source_memory_write_ranges_def,
        codegenRelTheory.sized_source_write_range_def, venomStateTheory.eval_operand_def] >>
      rename1 `(EL j bb.bb_instructions).inst_operands = [Lit dw; Lit sw; Lit lw]` >>
      mp_tac (Q.ISPEC `dw:256 word` wordsTheory.w2n_lt) >> simp[] >> decide_tac) >>
  gvs[mm_local_write_footprint_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  asm_simp_tac (srw_ss()) [venomExecSemanticsTheory.step_inst_non_invoke] >>
  with_opcode_clause simp >>
  simp[venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operand_def] >>
  rename1 `(EL j bb.bb_instructions).inst_operands = [Lit dstw; Var valuev]` >>
  Cases_on `lookup_var valuev (H j)` >> simp[] >> strip_tac >>
  gvs[codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def, venomStateTheory.eval_operand_def] >>
  decide_tac)
QED

Theorem mm_local_mem2mem_prefix_execution:
  !n fn0 supply index k bb sk is gs ns rs deleted excluded h H fuel ctx eom pre esh out esn t0.
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  h = phi_prefix_length is /\ h <= n /\ n <= LENGTH is /\
  (!q. h <= q /\ q < n ==>
    (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
    ~is_terminator (EL q is).inst_opcode /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
      H (SUC q) = u with vs_inst_idx := SUC q) /\
  (!q. h <= q /\ q < n ==>
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL q is) (H q)) /\
  eom < dimword (:256) /\
  state_equiv excluded (H h with vs_inst_idx := LENGTH pre) t0 /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE h is) = (pre,esh) /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
    (TAKE (n-h) (DROP h is)) = (out,esn) ==>
  ?t. mm_local_exec_prefix fuel ctx out t0 t /\
    mm_local_cut is gs H n excluded (LENGTH pre + LENGTH out) t /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE n is) =
      (pre ++ out,esn) /\
    ir_supply_extends sk esh /\ ir_supply_extends esh esn /\
    t.vs_inst_idx = LENGTH pre + LENGTH out
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `t0.vs_inst_idx = LENGTH pre` by fs[state_equiv_def] >>
  Cases_on `n = h`
  >- (qpat_x_assum `!m. m < _ ==> _` kall_tac >>
      qpat_x_assum `n = h` SUBST_ALL_TAC >>
      fs[mm_flat_map_supply_def] >>
      qexists `t0` >>
      simp[mm_local_exec_prefix_def, irSupplyFreshPropsTheory.ir_supply_extends_refl] >>
      conj_tac >- (irule mm_local_cut_init >> gvs[]) >>
      irule (cj 1 mm_local_list_resources) >>
      qexistsl [`apply_groups_inst_supply Mem2Mem ns rs`,`TAKE h is`] >>
      metis_tac[mm_local_mode_resources]) >>
  Cases_on `n` >- fs[] >> rename1 `SUC r <= LENGTH is` >>
  `h <= r /\ r < LENGTH is` by decide_tac >>
  Cases_on `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
    (TAKE (r-h) (DROP h is))` >>
  rename1 `mm_flat_map_supply _ esh (TAKE (r-h) (DROP h is)) = (front,es)` >>
  `!q. h <= q /\ q < r ==>
    (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
    ~is_terminator (EL q is).inst_opcode /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
      H (SUC q) = u with vs_inst_idx := SUC q` by
    (qx_gen_tac `q` >> strip_tac >>
     qpat_assum `!q. h <= q /\ q < SUC r ==> (H q).vs_inst_idx = q /\ _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  `!q. h <= q /\ q < r ==>
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL q is) (H q)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  `r <= LENGTH is` by decide_tac >>
  qpat_x_assum `!m. m < SUC r ==> _` (qspec_then `r` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `apply_groups_inst_supply Mem2Mem ns rs es (EL r is)` >>
  rename1 `apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = (frag,es')` >>
  `TAKE (SUC r-h) (DROP h is) = TAKE (r-h) (DROP h is) ++ [EL r is]` by
    (`SUC r-h = SUC (r-h) /\ r-h < LENGTH (DROP h is)` by
       (simp[] >> gvs[]) >>
     gvs[rich_listTheory.TAKE_SUC_BY_TAKE, rich_listTheory.SNOC_APPEND,
       rich_listTheory.EL_DROP]) >>
  `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
     (TAKE (SUC r-h) (DROP h is)) = (front ++ frag,es')` by
    (qpat_assum `TAKE (SUC r-h) (DROP h is) = _` (fn th => rewrite_tac[th]) >>
     irule mm_local_flat_map_supply_append >>
     qexists `es` >> simp[mm_flat_map_supply_def]) >>
  `out = front ++ frag /\ esn = es'` by metis_tac[pairTheory.PAIR_EQ] >>
  `ir_supply_extends es es'` by
    (irule (cj 1 mm_local_mode_resources) >> metis_tac[]) >>
  `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk
     (TAKE (SUC r) is) = (pre ++ out,esn)` by
    (qpat_assum `out = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `esn = _` (fn th => rewrite_tac[th]) >>
     `TAKE (SUC r) is = TAKE r is ++ [EL r is]` by
       simp[rich_listTheory.TAKE_SUC_BY_TAKE, rich_listTheory.SNOC_APPEND] >>
     qpat_assum `TAKE (SUC r) is = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[APPEND_ASSOC] >>
     irule mm_local_flat_map_supply_append >>
     qexists `es` >> simp[mm_flat_map_supply_def]) >>
  `?t'. mm_local_exec_prefix fuel ctx frag t t' /\
    mm_local_cut is gs H (SUC r) excluded
      (LENGTH pre + LENGTH front + LENGTH frag) t'` suffices_by
    (strip_tac >> qexists `t'` >>
     conj_tac >- (qpat_assum `out = _` (fn th => rewrite_tac[th]) >>
       metis_tac[mm_local_exec_prefix_append]) >>
     conj_tac >- metis_tac[listTheory.LENGTH_APPEND, arithmeticTheory.ADD_ASSOC] >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     conj_tac >- metis_tac[irSupplyFreshPropsTheory.ir_supply_extends_trans] >>
     drule mm_local_exec_prefix_cursor >> simp[]) >>
  ` (H r).vs_inst_idx = r /\ ~is_terminator (EL r is).inst_opcode /\
    ?u. step_inst fuel ctx (EL r is) (H r) = OK u /\
      H (SUC r) = u with vs_inst_idx := SUC r` by
    (qpat_assum `!q. h <= q /\ q < SUC r ==> (H q).vs_inst_idx = q /\ _`
      (qspec_then `r` mp_tac) >> simp[]) >>
  Cases_on `MEM (EL r is).inst_id ns`
  >- (Cases_on `(EL r is).inst_opcode = MLOAD`
      >- (`{v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} SUBSET excluded` by
            (simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
          `phi_prefix_length is <= r` by metis_tac[] >>
          `H (SUC r) = u with vs_inst_idx := SUC (H r).vs_inst_idx` by simp[] >>
          drule_all mm_local_cut_erased_load_excluded_transition >>
          disch_then (qspec_then `es` strip_assume_tac) >>
          `frag = [mk_nop_from (EL r is)]` by metis_tac[pairTheory.PAIR_EQ] >>
          qexists `t with vs_inst_idx := SUC (LENGTH pre + LENGTH front)` >>
          conj_tac >- gvs[mm_local_exec_prefix_def, mk_nop_from_def,
            venomInstTheory.is_terminator_def] >> gvs[arithmeticTheory.ADD1]) >>
      Cases_on `(EL r is).inst_opcode IN {MSTORE; MCOPY}`
      >- (`phi_prefix_length is <= r` by metis_tac[] >>
          `H (SUC r) = u with vs_inst_idx := SUC (H r).vs_inst_idx` by simp[] >>
          drule_all mm_local_cut_erased_write_transition >>
          disch_then (qspec_then `es` strip_assume_tac) >>
          `frag = [mk_nop_from (EL r is)]` by metis_tac[pairTheory.PAIR_EQ] >>
          qexists `t with vs_inst_idx := SUC (LENGTH pre + LENGTH front)` >>
          conj_tac >- gvs[mm_local_exec_prefix_def, mk_nop_from_def,
            venomInstTheory.is_terminator_def] >> gvs[arithmeticTheory.ADD1]) >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
        metis_tac[mm_local_prefix_wf_id_distinct] >>
      `MEM (EL r is) bb.bb_instructions` by metis_tac[EL_MEM] >>
      `!g. MEM g gs ==> ~MEM (EL r is).inst_id g.cg_inst_ids` by
        (gvs[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
         metis_tac[mm_local_prefix_nonselected_group_absent,
           mode_copy_opcode_def, mode_load_opcode_def]) >>
      qpat_x_assum `MEM (EL r is).inst_id ns` mp_tac >>
      pure_asm_rewrite_tac[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >>
      strip_tac >> gvs[] >>
      rename1 `MEM _ (nop_ids_of_group _ _ _ g)` >>
      qpat_x_assum `MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
      simp[nop_ids_of_group_def] >>
      Cases_on `REVERSE (sort_ids_by_block bb.bb_instructions g.cg_inst_ids)` >>
      simp[MEM_FILTER] >> strip_tac >>
      `MEM (EL r bb.bb_instructions).inst_id
        (REVERSE (sort_ids_by_block bb.bb_instructions g.cg_inst_ids))` by
        (pure_asm_rewrite_tac[MEM] >> simp[]) >>
      gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER] >> metis_tac[]) >>
  Cases_on `ALOOKUP rs (EL r is).inst_id`
  >- (`frag = [EL r is] /\ es' = es` by
        (gvs[apply_groups_inst_supply_def]) >>
      `((EL r is).inst_opcode IN {MSTORE; MCOPY} ==>
        ~(?g. MEM g gs /\ MEM (EL r is).inst_id g.cg_inst_ids))` by
        (strip_tac >> strip_tac >>
         `MEM (EL r is) bb.bb_instructions` by metis_tac[EL_MEM] >>
         `(EL r is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by gvs[] >>
         `!v li. dfg_get_def (dfg_build_function fn0) v = SOME li ==>
           li.inst_id <> (EL r is).inst_id` by
           metis_tac[mm_local_prefix_write_not_def] >>
         `!rep. rep_pin_id (dfg_build_function fn0) Mem2Mem rep g <>
           SOME (EL r is).inst_id` by
           (simp[rep_pin_id_def, AllCaseEqs()] >> metis_tac[]) >>
         drule_all mm_local_prefix_write_origin >> strip_tac >>
         rename1 `MEM orig (EL index fn0.fn_blocks).bb_instructions` >>
         `dfg_get_inst_by_id (dfg_build_function fn0) orig.inst_id = SOME orig` by
           (irule venomTransformStructurePropsTheory.function_ids_exact >> simp[] >>
            irule venomFnInstsProofsTheory.MEM_fn_insts >>
            qexists `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
         `~MEM (EL r is).inst_id
           (nop_ids_of_group (dfg_build_function fn0) Mem2Mem is g)` by
           (gvs[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
         `MEM (EL r is).inst_id (sort_ids_by_block is g.cg_inst_ids)` by
           (simp[sort_ids_by_block_def, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
         Cases_on `REVERSE (sort_ids_by_block is g.cg_inst_ids)`
         >- metis_tac[MEM_REVERSE, MEM] >>
         rename1 `REVERSE (sort_ids_by_block is g.cg_inst_ids) = rep::earlier` >>
         `rep_of_group is g = SOME (rep,g)` by gvs[rep_of_group_def] >>
         `rep = (EL r is).inst_id` by
           (Cases_on `rep = (EL r is).inst_id` >- simp[] >>
            `MEM (EL r is).inst_id earlier` by metis_tac[MEM_REVERSE, MEM] >>
            qpat_x_assum `~MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
            pure_asm_rewrite_tac[nop_ids_of_group_def, MEM_FILTER, MEM_REVERSE] >>
            gvs[MEM_FILTER, MEM_REVERSE, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
         `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
           metis_tac[mm_local_prefix_wf_id_distinct] >>
         `MEM ((EL r is).inst_id,g) rs` by
           (pure_asm_rewrite_tac[rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
            qexists `SOME ((EL r is).inst_id,g)` >> simp[] >>
            qexists `g` >> simp[] >> metis_tac[]) >>
         gvs[alistTheory.ALOOKUP_NONE, MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      `?t'. mm_local_exec_prefix fuel ctx [EL r is] t t' /\
        mm_local_cut is gs H (SUC r) excluded
          (SUC (LENGTH pre + LENGTH front)) t'` by
        (irule mm_local_cut_ordinary_transition >> metis_tac[]) >>
      gvs[arithmeticTheory.ADD1] >> metis_tac[]) >>
  `?g. MEM g gs /\ rep_of_group is g = SOME ((EL r is).inst_id,x)` by
    (drule alistTheory.ALOOKUP_MEM >>
     pure_asm_rewrite_tac[rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
     strip_tac >> rename1 `IS_SOME opt` >>
     Cases_on `opt` >> fs[] >>
     metis_tac[]) >>
  `g = x` by
    (gvs[rep_of_group_def, AllCaseEqs()]) >>
  `rep_of_group is x = SOME ((EL r is).inst_id,x) /\ MEM x gs` by metis_tac[] >>
  `!q. h <= q /\ q <= r ==> ~is_terminator (EL q is).inst_opcode /\
    ?z. step_inst fuel ctx (EL q is) (H q) = OK z /\
      H (SUC q) = z with vs_inst_idx := SUC (H q).vs_inst_idx` by
    (qx_gen_tac `q` >> strip_tac >>
     qpat_assum `!q. h <= q /\ q < SUC r ==> (H q).vs_inst_idx = q /\ _`
       (qspec_then `q` mp_tac) >> simp[] >> gvs[]) >>
  `((EL r is).inst_opcode = MSTORE /\ x.cg_length = 32 ==>
    !w. MEM (Var w) (EL r is).inst_operands ==>
      lookup_var w (H r) = lookup_var w t)` by
    (rpt strip_tac >> irule mm_local_cut_representative_protected_operands >>
     metis_tac[]) >>
  Cases_on `fresh_inst_id es` >> rename1 `fresh_inst_id es = (lid,es1)` >>
  Cases_on `fresh_ir_var es1` >> rename1 `fresh_ir_var es1 = (v,es2)` >>
  `v IN excluded` by
    (irule mm_local_emission_fresh_excluded >> metis_tac[]) >>
  `!q. h <= q /\ q <= r ==> (H q).vs_inst_idx = q /\
    (H q).vs_current_bb = bb.bb_label /\
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL q is) (H q) /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u` by
    (qx_gen_tac `q` >> strip_tac >>
     qpat_assum `!q. h <= q /\ q < SUC r ==> (H q).vs_inst_idx = q /\ _`
       (qspec_then `q` mp_tac) >>
     qpat_assum `!q. h <= q /\ q < SUC r ==> static_mem_ok _ _ _ _ _`
       (qspec_then `q` mp_tac) >> simp[] >> metis_tac[]) >>
  `x.cg_dst < dimword (:256) /\ x.cg_src < dimword (:256) /\
    x.cg_length < dimword (:256)` by
    (irule mm_local_representative_finite_bounds >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) frag` by
    (qpat_x_assum `is = bb.bb_instructions` kall_tac >>
     qpat_x_assum `apply_groups_inst_supply _ _ _ _ _ = (frag,es')` mp_tac >>
     pure_asm_rewrite_tac[apply_groups_inst_supply_def] >>
     Cases_on `x.cg_length = 32` >>
     Cases_on `(EL r is).inst_opcode = MSTORE` >>
     pure_asm_rewrite_tac[] >>
     simp[mk_bulk_copy_inst_def, mk_load_inst_def, mk_mstore_from_load_def,
       mode_copy_opcode_def, mode_load_opcode_def] >>
     strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  drule_all mm_local_cut_representative_transition >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `mm_local_cut _ _ _ (SUC r) _ _ done` >>
  qexists `done` >> simp[] >>
  simp[mm_local_exec_prefix_def, Abbr `done`, arithmeticTheory.ADD1] >>
  qexists `fin` >> gvs[arithmeticTheory.ADD1]
QED

Theorem mm_local_mem2mem_terminal_cut[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  n < LENGTH is /\ SUC n = LENGTH is /\
  is_terminator (EL n is).inst_opcode /\
  mm_local_cut is gs H n excluded pc t ==>
  mm_local_pending_indices is gs n = [] /\
  t.vs_memory = (H n).vs_memory /\
  state_equiv excluded ((H n) with vs_inst_idx := pc) t /\
  (!v. MEM (Var v) (EL n is).inst_operands ==>
    lookup_var v (H n) = lookup_var v t) /\
  (!es. apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `(EL n is).inst_opcode <> MSTORE /\
   (EL n is).inst_opcode <> mode_copy_opcode Mem2Mem /\
   (EL n is).inst_opcode <> mode_load_opcode Mem2Mem` by
    (gvs[mode_copy_opcode_def, mode_load_opcode_def] >>
     metis_tac[venomInstTheory.is_terminator_def]) >>
  `!g. MEM g gs ==> ~MEM (EL n is).inst_id g.cg_inst_ids` by
    metis_tac[mm_local_prefix_nonselected_group_absent] >>
  `mm_local_pending_indices is gs n = []` by
    (`!j. ~MEM j (mm_local_pending_indices is gs n)` suffices_by
       (Cases_on `mm_local_pending_indices is gs n` >> simp[] >> metis_tac[]) >>
     qx_gen_tac `j` >> rewrite_tac[mm_local_pending_indices_mem] >> strip_tac >>
     `r = n` by decide_tac >> metis_tac[mm_local_rep_member]) >>
  `~MEM (EL n is).inst_id ns` by
    (strip_tac >> qpat_x_assum `MEM (EL n is).inst_id ns` mp_tac >>
     pure_asm_rewrite_tac[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >>
     strip_tac >> gvs[] >>
     rename1 `MEM _ (nop_ids_of_group _ _ _ g)` >>
     `~MEM (EL n bb.bb_instructions).inst_id
       (REVERSE (sort_ids_by_block bb.bb_instructions g.cg_inst_ids))` by
       (simp[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER] >> metis_tac[]) >>
     qpat_x_assum `MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
     simp[nop_ids_of_group_def] >>
     Cases_on `REVERSE (sort_ids_by_block bb.bb_instructions g.cg_inst_ids)` >>
     gvs[MEM_FILTER]) >>
  `ALOOKUP rs (EL n is).inst_id = NONE` by
    (Cases_on `ALOOKUP rs (EL n is).inst_id` >> simp[] >>
     `ALOOKUP (rep_map_of_groups bb.bb_instructions
       (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed)
       (EL n is).inst_id = SOME x` by metis_tac[] >>
     metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY,
       venomInstTheory.is_terminator_def, mm_local_prefix_rep_write]) >>
  `!es. apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es)` by
    simp[apply_groups_inst_supply_def] >>
  `t.vs_memory = (H n).vs_memory` by
    gvs[mm_local_cut_def, mm_local_pending_empty] >>
  `state_equiv excluded ((H n) with vs_inst_idx := pc) t` by
    (`(H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|> =
       (H n) with vs_inst_idx := pc` by
       simp[venomStateTheory.venom_state_component_equality] >>
     metis_tac[mm_local_cut_memory_state_equiv]) >>
  simp[] >> rpt strip_tac >>
  `MEM v (venomInst$inst_uses (EL n is))` by
    gvs[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  `ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
    (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
   rs = rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
  `v NOTIN excluded` by
    (qpat_assum `!es. apply_groups_inst_supply _ _ _ _ _ = _`
       (qspec_then `sk` assume_tac) >>
     qpat_x_assum `is = _` SUBST_ALL_TAC >>
     drule_all mm_local_retained_operand_protected >> simp[]) >>
  gvs[mm_local_cut_def]
QED

Theorem mm_local_mem2mem_terminal_prefix_boundary[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  h = phi_prefix_length is /\ h <= n /\ SUC n = LENGTH is /\
  is_terminator (EL n is).inst_opcode /\
  (!q. h <= q /\ q < n ==>
    (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
    ~is_terminator (EL q is).inst_opcode /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
      H (SUC q) = u with vs_inst_idx := SUC q) /\
  (!q. h <= q /\ q < n ==>
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL q is) (H q)) /\ eom < dimword (:256) /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE h is) = (pre,esh) /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
    (TAKE (n-h) (DROP h is)) = (out,esn) ==>
  ?t. mm_local_exec_prefix fuel ctx out (H h with vs_inst_idx := LENGTH pre) t /\
    mm_local_cut is gs H n excluded (LENGTH pre + LENGTH out) t /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE n is) =
      (pre ++ out,esn) /\
    ir_supply_extends sk esh /\ ir_supply_extends esh esn /\
    t.vs_inst_idx = LENGTH pre + LENGTH out /\
    mm_local_pending_indices is gs n = [] /\ t.vs_memory = (H n).vs_memory /\
    state_equiv excluded ((H n) with vs_inst_idx := LENGTH pre + LENGTH out) t /\
    (!v. MEM (Var v) (EL n is).inst_operands ==>
      lookup_var v (H n) = lookup_var v t) /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esn (DROP n is) =
      ([EL n is],esn) /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk is =
      (pre ++ out ++ [EL n is],esn) /\
    dft_exec_suffix fuel ctx (out ++ [EL n is]) (H h with vs_inst_idx := LENGTH pre) =
      dft_exec_suffix fuel ctx [EL n is] t
Proof
  strip_tac >> `n < LENGTH is /\ n <= LENGTH is` by decide_tac >>
  `state_equiv excluded (H h with vs_inst_idx := LENGTH pre)
    (H h with vs_inst_idx := LENGTH pre)` by simp[stateEquivProofsTheory.state_equiv_refl] >>
  drule_all mm_local_mem2mem_prefix_execution >> strip_tac >>
  drule_all mm_local_mem2mem_terminal_cut >> strip_tac >>
  `DROP n is = [EL n is]` by
    (qspecl_then [`n`, `is`] mp_tac rich_listTheory.DROP_CONS_EL >>
     simp[]) >>
  `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esn (DROP n is) =
    ([EL n is],esn)` by gvs[mm_flat_map_supply_def] >>
  `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk is =
    (pre ++ out ++ [EL n is],esn)` by
    (qspecl_then [`TAKE n is`, `DROP n is`]
       (irule o SRULE [listTheory.TAKE_DROP, listTheory.APPEND_ASSOC])
       mm_local_flat_map_supply_append >> metis_tac[]) >>
  qexists `t` >> simp[] >> metis_tac[mm_local_exec_prefix_suffix]
QED

Theorem mm_local_cut_empty_non_ok[local]:
  mm_local_cut is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\
  ~(?u. step_inst fuel ctx i (H n) = OK u) ==>
  lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx i (H n)) (step_inst fuel ctx i t)
Proof
  strip_tac >> irule venomExecutionReplayPropsTheory.state_non_ok >>
  metis_tac[mm_local_cut_empty_state_equiv]
QED

Theorem mm_local_mem2mem_phi_emission:
  !xs es. wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions gs /\
  rs = rep_map_of_groups bb.bb_instructions gs /\
  EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI) xs ==>
  mm_flat_map_supply (apply_groups_inst_supply mode ns rs) es xs = (xs,es)
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt strip_tac >> fs[] >>
  `!r. apply_groups_inst_supply mode ns rs r h = ([h],r)` by
    (gvs[] >> irule mm_local_prefix_nonselected_unchanged >>
     Cases_on `mode` >>
     simp[mode_copy_opcode_def, mode_load_opcode_def] >> metis_tac[]) >>
  simp[mm_flat_map_supply_def] >> gvs[]
QED

Theorem mm_local_mem2mem_phi_boundary:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions gs /\
  rs = rep_map_of_groups bb.bb_instructions gs /\
  bb.bb_instructions = phis ++ tail_insts /\
  EVERY (\i. i.inst_opcode = PHI) phis /\
  EVERY (\i. i.inst_opcode <> PHI) tail_insts /\
  mm_flat_map_supply (apply_groups_inst_supply mode ns rs) sk tail_insts = (out,es) ==>
  mm_flat_map_supply (apply_groups_inst_supply mode ns rs) sk bb.bb_instructions =
    (phis ++ out,es) /\
  EVERY (\i. i.inst_opcode <> PHI) out /\
  phi_prefix_length (phis ++ out) = phi_prefix_length bb.bb_instructions /\
  (!s. eval_phis s (phis ++ out) = eval_phis s bb.bb_instructions)
Proof
  strip_tac >>
  `mm_flat_map_supply (apply_groups_inst_supply mode ns rs) sk phis = (phis,sk)` by
    (irule mm_local_mem2mem_phi_emission >>
     qexistsl [`bb`, `fn0`, `gs`, `index`, `k`, `sk`, `supply`] >>
     simp[EVERY_MEM, MEM_APPEND] >> gvs[EVERY_MEM]) >>
  `EVERY (\i. i.inst_opcode <> PHI) out` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM i tail_insts` by
       (irule (Q.ISPECL [`apply_groups_inst_supply mode ns rs`,
           `\i:instruction. i.inst_opcode = PHI`]
          mmSupplyWfProofsTheory.mm_flat_map_supply_origin) >>
        metis_tac[mmSupplyWfProofsTheory.apply_groups_inst_supply_phi_origin]) >>
     gvs[EVERY_MEM]) >>
  conj_tac >- (qpat_x_assum `bb.bb_instructions = _` SUBST_ALL_TAC >>
    irule mm_local_flat_map_supply_append >> metis_tac[]) >>
  simp[dftIndexedExecTheory.dft_phi_prefix_append,
    dftIndexedExecTheory.dft_eval_phis_append]
QED

Theorem mm_local_cut_assert_abort[local]:
  mm_local_cut is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  (i.inst_opcode = ASSERT \/ i.inst_opcode = ASSERT_UNREACHABLE) /\
  step_inst fuel ctx i (H n) = Abort a u ==>
  ?v. step_inst fuel ctx i t = Abort a v /\ revert_equiv u v
Proof
  strip_tac >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    metis_tac[mm_local_cut_memory_state_equiv] >>
  `!op. MEM op i.inst_operands ==>
    eval_operand op (H n) = eval_operand op t` by
    (rpt strip_tac >> Cases_on `op` >>
     gvs[venomStateTheory.eval_operand_def, state_equiv_def,
       execution_equiv_def, venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst fuel ctx i (H n) = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[revert_equiv_def, venomStateTheory.revert_state_def,
    venomStateTheory.halt_state_def, venomStateTheory.set_returndata_def]
QED

Theorem mm_local_cut_noninvoke_abort[local]:
  mm_local_cut is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  step_inst fuel ctx i (H n) = Abort a u ==>
  ?v. step_inst fuel ctx i t = Abort a v /\ revert_equiv u v
Proof
  strip_tac >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    metis_tac[mm_local_cut_memory_state_equiv] >>
  drule_all venomExecutionReplayPropsTheory.state_noninvoke_abort >> simp[]
QED

Theorem mm_local_cut_nonterminator_stop[local]:
  mm_local_cut is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\
  (i.inst_opcode = INVOKE ==> mm_local_pending_indices is gs n = []) /\
  ~(?err. step_inst fuel ctx i (H n) = Error err) /\
  ~(?u. step_inst fuel ctx i (H n) = OK u) ==>
  lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx i (H n)) (step_inst fuel ctx i t)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (irule mm_local_cut_empty_non_ok >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx i (H n)` >> gvs[lift_result_def]
  >- (drule opcodeClassTheory.step_inst_halt_opcodes >> strip_tac >>
      gvs[venomInstTheory.is_terminator_def])
  >- (drule_all mm_local_cut_noninvoke_abort >>
      strip_tac >> simp[lift_result_def])
  >- (gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
      drule opcodeClassTheory.step_inst_base_intret_opcodes >> strip_tac >>
      gvs[venomInstTheory.is_terminator_def])
QED

Theorem mm_local_mem2mem_stopping_cut[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  h = phi_prefix_length is /\ h <= LENGTH is /\ s.vs_inst_idx = h /\
  s.vs_current_bb = bb.bb_label /\
  state_equiv excluded (s with vs_inst_idx := LENGTH pre) t0 /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn bb s) /\
  ~(?err. exec_block fuel ctx bb s = Error err) /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE h is) = (pre,esh) ==>
  ?n H out esn t. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==>
      (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
      static_mem_ok eom ctx fn (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n) /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
      (TAKE (n-h) (DROP h is)) = (out,esn) /\
    mm_local_exec_prefix fuel ctx out t0 t /\
    mm_local_cut is gs H n excluded (LENGTH pre + LENGTH out) t /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE n is) =
      (pre ++ out,esn) /\ t.vs_inst_idx = LENGTH pre + LENGTH out
Proof
  strip_tac >>
  `?n H. h <= n /\ n < LENGTH bb.bb_instructions /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q bb.bb_instructions).inst_opcode /\
      ?u. step_inst fuel ctx (EL q bb.bb_instructions) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn (EL q bb.bb_instructions) (H q)) /\
    (is_terminator (EL n bb.bb_instructions).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n bb.bb_instructions) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n bb.bb_instructions] (H n)` by
    (irule venomExecutionReplayPropsTheory.source_stopping_history >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `!q. h <= q /\ q <= n ==> (H q).vs_current_bb = bb.bb_label` by
    metis_tac[venomExecutionReplayPropsTheory.source_history_label] >>
  Cases_on `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
    (TAKE (n-h) (DROP h is))` >>
  rename1 `mm_flat_map_supply _ esh _ = (out,esn)` >>
  `n <= LENGTH is` by simp[] >>
  `!q. h <= q /\ q < n ==>
    (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
    ~is_terminator (EL q is).inst_opcode /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
      H (SUC q) = u with vs_inst_idx := SUC q` by
    (rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  `!q. h <= q /\ q < n ==>
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL q is) (H q)` by
    (rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  `state_equiv excluded (H h with vs_inst_idx := LENGTH pre) t0` by metis_tac[] >>
  drule_all mm_local_mem2mem_prefix_execution >> strip_tac >>
  qexistsl [`n`,`H`,`out`,`esn`,`t`] >> simp[] >>
  metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Theorem mm_local_mem2mem_nonterminator_stopping_boundary[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  mm_local_cut is gs H n excluded pc t /\
  ~is_terminator (EL n is).inst_opcode /\
  ~(?err. step_inst fuel ctx (EL n is) (H n) = Error err) /\
  ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u) ==>
  (!es. apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es)) /\
  lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx (EL n is) (H n)) (step_inst fuel ctx (EL n is) t)
Proof
  strip_tac >>
  `(EL n is).inst_opcode <> MSTORE /\
   (EL n is).inst_opcode <> MCOPY /\ (EL n is).inst_opcode <> MLOAD` by
    (Cases_on `(EL n is).inst_opcode = INVOKE` >- gvs[] >>
     Cases_on `step_inst fuel ctx (EL n is) (H n)` >> gvs[]
     >- (drule opcodeClassTheory.step_inst_halt_opcodes >> strip_tac >> gvs[])
     >- (drule opcodeClassTheory.step_inst_abort_opcodes >> strip_tac >> gvs[])
     >- (gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
         drule opcodeClassTheory.step_inst_base_intret_opcodes >> strip_tac >> gvs[])) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `!es. apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es)` by
    (gvs[] >> irule mm_local_prefix_nonselected_unchanged >>
     simp[mode_copy_opcode_def, mode_load_opcode_def, EL_MEM] >> metis_tac[]) >>
  `!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded` by
    (qx_gen_tac `v` >> disch_tac >> irule (cj 3 mm_local_retained_operand_protected) >>
     gvs[] >> metis_tac[EL_MEM, venomWfPropsTheory.operand_var_in_inst_uses]) >>
  gvs[] >> irule mm_local_cut_nonterminator_stop >>
  simp[] >>
  qexistsl [`(scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed`,
    `bb.bb_instructions`,`pc`] >> simp[] >>
  strip_tac >> irule mm_local_hard_barrier_pending_empty >>
  simp[] >>
  qexistsl [`bb`,`fn0`,`index`,`k`,`Mem2Mem`,`sk`,`supply`] >>
  simp[scan_inst_def, mode_copy_opcode_def, mode_load_opcode_def,
    is_volatile_memory_def, venomEffectsTheory.read_effects_def,
    venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def]
QED

Theorem mm_local_cut_terminator_result[local]:
  mm_local_cut is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  is_terminator i.inst_opcode ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [i] (H n)) (dft_exec_suffix fuel ctx [i] t)
Proof
  strip_tac >> irule venomExecutionReplayPropsTheory.state_terminator_result >>
  metis_tac[mm_local_cut_empty_state_equiv]
QED

Theorem mm_local_mem2mem_stopping_result:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  mm_local_cut is gs H n excluded pc t /\
  ~(?err. dft_exec_suffix fuel ctx [EL n is] (H n) = Error err) /\
  (is_terminator (EL n is).inst_opcode \/
    ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) ==>
  (!es. apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es)) /\
   lift_result
     (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
     (execution_equiv excluded) revert_equiv
     (dft_exec_suffix fuel ctx [EL n is] (H n))
     (dft_exec_suffix fuel ctx [EL n is] t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_terminator (EL n is).inst_opcode`
     >- ( `bb_well_formed bb` by
            (irule (cj 1 mm_local_prefix_wf_last) >>
             qexistsl [`fn0`,`index`,`k`,`sk`,`supply`] >>
             gvs[venomWfTheory.wf_ssa_def, ir_supply_covers_fn_def,
               irSupplyTheory.fn_ir_inst_ids_def, irSupplyTheory.block_ir_inst_ids_def,
               EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM, MEM_MAP]) >>
          `SUC n = LENGTH is` by
            (qpat_x_assum `bb_well_formed bb` mp_tac >>
             simp[venomWfTheory.bb_well_formed_def] >> strip_tac >>
             `n = PRE (LENGTH is)` by metis_tac[] >>
             qpat_x_assum `is = _` (fn th => SUBST_ALL_TAC (SYM th)) >> decide_tac) >>
          drule_all mm_local_mem2mem_terminal_cut >> strip_tac >>
          conj_tac >- simp[] >>
          irule mm_local_cut_terminator_result >>
          reverse conj_tac
          >- (simp[] >> qexistsl [`gs`,`is`,`pc`] >> gvs[]) >>
          qx_gen_tac `v` >> disch_tac >>
          `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
          irule (cj 3 mm_local_retained_operand_protected) >>
          gvs[] >> metis_tac[venomWfPropsTheory.operand_var_in_inst_uses])
     >- (fs[] >>
     `~(?err. step_inst fuel ctx (EL n is) (H n) = Error err)` by
       (Cases_on `step_inst fuel ctx (EL n is) (H n)` >>
        gvs[dft_exec_suffix_def]) >>
     mp_tac (Q.INST [`pc` |-> `pc`]
       mm_local_mem2mem_nonterminator_stopping_boundary) >>
     (impl_tac >- gvs[]) >> strip_tac >>
     simp[] >>
     Cases_on `step_inst fuel ctx (EL n is) (H n)` >>
     Cases_on `step_inst fuel ctx (EL n is) t` >>
     gvs[lift_result_def, dft_exec_suffix_def])
QED

Theorem mm_local_mem2mem_post_phi_result:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  transform_block_mode_supply (dfg_build_function fn0) Mem2Mem sk bb = (bb',sk') /\
  s.vs_inst_idx = phi_prefix_length is /\ s.vs_current_bb = bb.bb_label /\
  state_equiv excluded s t0 /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn bb s) /\
  ~(?err. exec_block fuel ctx bb s = Error err) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (exec_block fuel ctx bb s) (exec_block fuel ctx bb' t0)
Proof
  strip_tac >>
  `t0.vs_inst_idx = phi_prefix_length is` by gvs[state_equiv_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `phi_prefix_length is <= LENGTH is` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `EVERY (\i. i.inst_opcode = PHI) (TAKE (phi_prefix_length is) is)` by
    simp[analysisSimProofsBaseTheory.phi_prefix_all_phi] >>
  `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk
    (TAKE (phi_prefix_length is) is) = (TAKE (phi_prefix_length is) is,sk)` by
    (irule mm_local_mem2mem_phi_emission >>
     qexistsl [`bb`,`fn0`,`gs`,`index`,`k`,`sk`,`supply`] >>
     gvs[EVERY_MEM] >> metis_tac[MEM_TAKE]) >>
  `?n H out esn t. phi_prefix_length is <= n /\ n < LENGTH is /\
    H (phi_prefix_length is) = s /\
    (!q. phi_prefix_length is <= q /\ q <= n ==>
      (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
      static_mem_ok eom ctx fn (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n) /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk
      (TAKE (n-phi_prefix_length is) (DROP (phi_prefix_length is) is)) = (out,esn) /\
    mm_local_exec_prefix fuel ctx out t0 t /\
    mm_local_cut is gs H n excluded (phi_prefix_length is + LENGTH out) t /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE n is) =
      (TAKE (phi_prefix_length is) is ++ out,esn) /\
    t.vs_inst_idx = phi_prefix_length is + LENGTH out` by
    (mp_tac (Q.INST [`h` |-> `phi_prefix_length is`,
       `pre` |-> `TAKE (phi_prefix_length is) is`, `esh` |-> `sk`]
       mm_local_mem2mem_stopping_cut) >>
     `s with vs_inst_idx := phi_prefix_length is = s` by
       simp[venomStateTheory.venom_state_component_equality] >>
     gvs[]) >>
  `(!es. apply_groups_inst_supply Mem2Mem ns rs es (EL n is) = ([EL n is],es)) /\
   lift_result
     (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
     (execution_equiv excluded) revert_equiv
     (dft_exec_suffix fuel ctx [EL n is] (H n))
     (dft_exec_suffix fuel ctx [EL n is] t)` by
    (`~(?err. dft_exec_suffix fuel ctx [EL n is] (H n) = Error err)` by metis_tac[] >>
     mp_tac (Q.INST [`pc` |-> `phi_prefix_length is + LENGTH (out:instruction list)`]
       mm_local_mem2mem_stopping_result) >>
     (impl_tac >- asm_rewrite_tac[]) >> simp[]) >>
  Cases_on `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esn
    (DROP (SUC n) is)` >>
  rename1 `mm_flat_map_supply _ esn (DROP (SUC n) is) = (tail,fin)` >>
  `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esn (DROP n is) =
    (EL n is :: tail,fin)` by
    (gvs[arithmeticTheory.ADD1] >>
     simp[rich_listTheory.DROP_EL_CONS, mm_flat_map_supply_def]) >>
  `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk is =
    (TAKE (phi_prefix_length is) is ++ out ++ EL n is :: tail,fin)` by
    (drule_all mm_local_flat_map_supply_append >> simp[TAKE_DROP, APPEND_ASSOC]) >>
  `bb'.bb_instructions = TAKE (phi_prefix_length is) is ++ out ++ EL n is :: tail` by
    (qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
     simp[transform_block_mode_supply_def] >>
     gvs[] >> strip_tac >> gvs[]) >>
  `exec_block fuel ctx bb' t0 = dft_exec_suffix fuel ctx (out ++ EL n is :: tail) t0` by
    (irule dftIndexedExecTheory.dft_exec_suffix_boundary >>
     gvs[] >> simp[listTheory.DROP_APPEND, LENGTH_TAKE,
       venomExecProofsTheory.phi_prefix_length_le, DROP_TAKE] >>
     `!a b:num. a - (b+a) = 0 /\ a - (b+(a+1)) = 0` by decide_tac >> simp[]) >>
  drule mm_local_exec_prefix_suffix >>
  disch_then (qspec_then `EL n is :: tail` assume_tac) >>
  gvs[] >>
  Cases_on `is_terminator (EL n bb.bb_instructions).inst_opcode`
  >- gvs[dft_exec_suffix_def] >>
  Cases_on `step_inst fuel ctx (EL n bb.bb_instructions) (H n)` >>
  gvs[dft_exec_suffix_def, lift_result_def] >>
  Cases_on `step_inst fuel ctx (EL n bb.bb_instructions) t` >>
  gvs[dft_exec_suffix_def, lift_result_def]
QED

Theorem mm_local_mem2mem_run_block_result[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  transform_block_mode_supply (dfg_build_function fn0) Mem2Mem sk bb = (bb',sk') /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  s.vs_current_bb = bb.bb_label /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ eom < dimword (:256) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_blocks [] d (SUC fuel) ctx fn s) /\
  ~(?err. run_block fuel ctx bb s = Error err) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (run_block fuel ctx bb s) (run_block fuel ctx bb' s)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `bb_well_formed bb` by
    (irule (cj 1 mm_local_prefix_wf_last) >>
     qexistsl [`fn0`,`index`,`k`,`sk`,`supply`] >>
     gvs[venomWfTheory.wf_ssa_def, ir_supply_covers_fn_def,
       irSupplyTheory.fn_ir_inst_ids_def, irSupplyTheory.block_ir_inst_ids_def,
       EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM, MEM_MAP]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (DROP (phi_prefix_length is) is)` by
    (irule simplifyCfgFixupStaticTheory.scfg_phi_suffix_nonphi >>
     gvs[venomWfTheory.bb_well_formed_def]) >>
  Cases_on `mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk
    (DROP (phi_prefix_length is) is)` >>
  rename1 `mm_flat_map_supply _ sk _ = (out,es)` >>
  mp_tac (Q.INST [`mode` |-> `Mem2Mem`,
    `phis` |-> `TAKE (phi_prefix_length is) is`,
    `tail_insts` |-> `DROP (phi_prefix_length is) is`] mm_local_mem2mem_phi_boundary) >>
  (impl_tac >- gvs[TAKE_DROP, analysisSimProofsBaseTheory.phi_prefix_all_phi]) >>
  strip_tac >>
  `bb'.bb_instructions = TAKE (phi_prefix_length is) is ++ out` by
    (qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
     simp[transform_block_mode_supply_def] >> gvs[] >> strip_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`s`,`bb.bb_instructions`]
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      drule_all dftGasFromListTraceDefsTheory.trace_blocks_enter >>
      disch_then (fn th => fs[th, EVERY_APPEND]) >>
      `sp.vs_current_bb = bb.bb_label` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
      `~(?err. exec_block fuel ctx bb
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Error err)` by
        gvs[venomExecSemanticsTheory.run_block_def] >>
      `lift_result
        (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
        (execution_equiv excluded) revert_equiv
        (exec_block fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
        (exec_block fuel ctx bb' (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
        (irule mm_local_mem2mem_post_phi_result >>
         (conj_tac >- metis_tac[]) >>
         (conj_tac >- simp[]) >>
         reverse conj_tac >- simp[stateEquivProofsTheory.state_equiv_refl] >>
         qexistsl [`SUC d`,`deleted`,`eom`,`fn`,`fn0`,`gs`,`index`,`is`,`k`,`ns`,`rs`,`sk`,`sk'`,`supply`] >>
         gvs[stateEquivProofsTheory.state_equiv_refl]) >>
      gvs[venomExecSemanticsTheory.run_block_def]) >>
  gvs[venomExecSemanticsTheory.run_block_def]
QED

Theorem mm_local_pending_indices_endpoints:
  mm_local_pending_indices is gs 0 = [] /\
  mm_local_pending_indices is gs (LENGTH is) = []
Proof
  simp[mm_local_pending_indices_def, listTheory.FILTER_EQ_NIL, EVERY_MEM,
    MEM_COUNT_LIST]
QED

