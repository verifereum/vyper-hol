(* Local memmerging phase: memzero and shared safe execution. *)
Theory mmLocalSafeExecutionProofs
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
  mmLocalMem2MemProofs
  venomTransformStructureProps venomWriteReplayProps venomExecutionReplayProps irSupplyFreshProps
Libs
  wordsLib finite_mapLib stepInstBaseLib

Definition mm_local_zero_cut_def:
  mm_local_zero_cut dfg is gs H n excluded pc t <=>
    t.vs_inst_idx = pc /\
    mm_local_nonmemory_frame (H n) = mm_local_nonmemory_frame t /\
    (!v. v NOTIN excluded ==> lookup_var v (H n) = lookup_var v t) /\
    mm_local_pending (mm_local_zero_capture dfg is n)
      (mm_local_pending_indices is gs n) (H n) t
End

Theorem mm_local_zero_cut_init[local]:
  mm_local_zero_cut dfg is gs H 0 excluded pc
    ((H 0) with vs_inst_idx := pc)
Proof
  simp[mm_local_zero_cut_def, mm_local_pending_indices_endpoints,
    mm_local_pending_empty, venomStateTheory.lookup_var_def]
QED

Theorem mm_local_zero_cut_empty[local]:
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] ==>
  state_equiv excluded ((H n) with vs_inst_idx := pc) t
Proof
  strip_tac >> gvs[mm_local_zero_cut_def, mm_local_pending_empty] >>
  gvs[state_equiv_frame, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
    venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_zero_cut_operands[local]:
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) ==>
  MAP (\op. eval_operand op (H n)) i.inst_operands =
  MAP (\op. eval_operand op t) i.inst_operands
Proof
  strip_tac >> irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  `MEM (EL x i.inst_operands) i.inst_operands` by simp[EL_MEM] >>
  Cases_on `EL x i.inst_operands` >>
  gvs[venomStateTheory.eval_operand_def, mm_local_zero_cut_def,
    mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_zero_cut_calldata[local]:
  mm_local_zero_cut dfg is gs H n excluded pc t ==>
  t.vs_call_ctx = (H n).vs_call_ctx
Proof
  simp[mm_local_zero_cut_def, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def,
    venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_zero_cut_end[local]:
  mm_local_zero_cut dfg is gs H (LENGTH is) excluded pc t ==>
  state_equiv excluded ((H (LENGTH is)) with vs_inst_idx := pc) t
Proof
  strip_tac >> irule mm_local_zero_cut_empty >>
  qexistsl [`dfg`,`gs`,`is`] >>
  simp[mm_local_pending_indices_endpoints] >> metis_tac[]
QED

Theorem mm_local_zero_store_fragment_exec[local]:
  dst < dimword (:256) ==>
  mm_local_exec_prefix fuel ctx [mk_zero_store_inst i dst] s
    ((write_memory_with_expansion dst (REPLICATE 32 0w) s)
      with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  simp[mm_local_exec_prefix_single, mk_zero_store_inst_def,
    venomInstTheory.is_terminator_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_write2_def,
    venomStateTheory.eval_operand_def, mstore_0w_eq_write]
QED

Theorem mm_local_zero_copy_fragment_exec[local]:
  g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  mm_local_exec_prefix fuel ctx
    [<| inst_id := id; inst_opcode := CALLDATASIZE;
        inst_operands := []; inst_outputs := [v] |>;
     mk_memzero_calldatacopy i g v] s
    ((write_memory_with_expansion g.cg_dst (REPLICATE g.cg_length 0w)
       (update_var v (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s))
      with vs_inst_idx := s.vs_inst_idx + 2)
Proof
  strip_tac >>
  simp[mm_local_exec_prefix_def, mk_memzero_calldatacopy_def,
    venomInstTheory.is_terminator_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_read0_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    calldatacopy_past_end_bytes] >>
  simp[venomStateTheory.write_memory_with_expansion_def,
    venomStateTheory.write_memory_def,
    venomStateTheory.expand_memory_def, arithmeticTheory.ADD1]
QED

Theorem mm_local_zero_cut_erased_write_stutter[local]:
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n] /\
  mm_local_zero_capture dfg is (SUC n) n = SOME (d,bs) /\
  (H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory /\
  mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
  (!v. lookup_var v (H (SUC n)) = lookup_var v (H n)) ==>
  mm_local_zero_cut dfg is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  `mm_local_pending (mm_local_zero_capture dfg is (SUC n))
    (mm_local_pending_indices is gs n) (H n) t` by
    (irule mm_local_pending_cap_cong >>
     qexists `mm_local_zero_capture dfg is n` >>
     fs[mm_local_zero_cut_def] >>
     rpt strip_tac >> irule mm_local_zero_capture_past >>
     gvs[mm_local_pending_indices_mem]) >>
  `mm_local_pending (mm_local_zero_capture dfg is (SUC n))
    (mm_local_pending_indices is gs (SUC n)) (H (SUC n)) t` by
    (simp[] >> irule mm_local_pending_create >> metis_tac[]) >>
  gvs[mm_local_zero_cut_def, venomStateTheory.lookup_var_def] >>
  qpat_x_assum `mm_local_pending _ (_ ++ [n]) _ _` mp_tac >>
  simp[mm_local_pending_def] >> strip_tac >>
  qexists `ws` >> simp[] >>
  irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]
QED

Theorem mm_local_zero_capture_after_phis[local]:
  mm_local_zero_capture dfg is n j = SOME (d,bs) ==>
  phi_prefix_length is <= j
Proof
  strip_tac >> spose_not_then assume_tac >>
  `j < phi_prefix_length is` by decide_tac >>
  drule venomExecProofsTheory.phi_prefix_length_el_phi >> strip_tac >>
  drule mm_local_zero_capture_cases >> strip_tac >> gvs[is_calldatasize_copy_def]
QED

Theorem mm_local_zero_cut_post_phi_init[local]:
  h = phi_prefix_length is /\
  state_equiv excluded (H h with vs_inst_idx := pc) t ==>
  mm_local_zero_cut dfg is gs H h excluded pc t
Proof
  strip_tac >>
  `mm_local_pending_indices is gs h = []` by
    (Cases_on `mm_local_pending_indices is gs h` >> simp[] >>
     rename1 `mm_local_pending_indices is gs h = j::js` >>
     `MEM j (mm_local_pending_indices is gs h)` by simp[] >>
     drule mm_local_pending_indices_after_phis >>
     gvs[mm_local_pending_indices_mem]) >>
  gvs[mm_local_zero_cut_def, mm_local_pending_empty, state_equiv_frame,
    mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.lookup_var_def, venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_zero_selected_actual_prefix[local]:
  h = phi_prefix_length is /\ n <= N /\
  (!j. h <= j /\ j < N ==>
    (H j).vs_current_bb = lbl /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
      H (SUC j) = u with vs_inst_idx := SUC j) ==>
  !j d bs. mm_local_zero_capture dfg is n j = SOME (d,bs) ==>
    (H j).vs_current_bb = lbl /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
      H (SUC j) = u with vs_inst_idx := SUC j
Proof
  rpt strip_tac >>
  `phi_prefix_length is <= j` by metis_tac[mm_local_zero_capture_after_phis] >>
  `j < n` by metis_tac[mm_local_zero_capture_cases] >>
  `h <= j /\ j < N` by (gvs[] >> decide_tac) >> metis_tac[]
QED

Theorem mm_local_zero_capture_actual_step[local]:
  mm_local_zero_capture dfg is n j = SOME (d,bs) /\
  step_inst fuel ctx (EL j is) s = OK u /\
  (!dst v len. is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v s = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)) ==>
  (u with vs_inst_idx := SUC j).vs_memory =
    (write_memory_with_expansion d bs s).vs_memory /\
  mm_local_nonmemory_frame (u with vs_inst_idx := SUC j) =
    mm_local_nonmemory_frame s /\
  (!v. lookup_var v (u with vs_inst_idx := SUC j) = lookup_var v s)
Proof
  strip_tac >>
  `(EL j is).inst_opcode IN {MSTORE; CALLDATACOPY}` by
    (drule mm_local_zero_capture_cases >>
     gvs[is_calldatasize_copy_def] >> metis_tac[]) >>
  `mm_local_nonmemory_frame u = mm_local_nonmemory_frame s /\
    (!v. lookup_var v u = lookup_var v s)` by
    (drule_at Any mm_local_write_runtime_frame >>
     gvs[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  reverse conj_tac
  >- gvs[venomStateTheory.lookup_var_def] >>
  simp[] >> drule mm_local_zero_capture_cases >> strip_tac >> gvs[]
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[venomExecSemanticsTheory.step_inst_non_invoke,
        venomExecSemanticsTheory.step_inst_base_def,
        venomExecSemanticsTheory.exec_write2_def,
        venomStateTheory.eval_operand_def] >>
      strip_tac >> gvs[mstore_0w_eq_write]) >>
  `lookup_var v s = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  gvs[is_calldatasize_copy_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomStateTheory.eval_operand_def] >>
  strip_tac >> gvs[calldatacopy_past_end_bytes, TAKE_LENGTH_ID_rwt]
QED

Theorem mm_local_zero_capture_finite[local]:
  is = bb.bb_instructions /\
  mm_local_zero_capture dfg is n j = SOME (d,bs) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  s.vs_current_bb = bb.bb_label /\ s.vs_inst_idx = j /\
  static_mem_ok eom ctx fn (EL j is) s /\ eom < dimword (:256) /\
  step_inst fuel ctx (EL j is) s = OK u ==>
  d + LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ d + LENGTH bs <= eom)
Proof
  strip_tac >> drule mm_local_zero_capture_cases >> strip_tac >>
  `(EL j is).inst_opcode IN {MSTORE; CALLDATACOPY}` by
    gvs[is_calldatasize_copy_def] >>
  `~in_revert_forward fn s` by
    (simp[contextCodegenRelTheory.in_revert_forward_def] >> strip_tac >>
     `get_instruction bb j = SOME (EL j is)` by
       gvs[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >>
     gvs[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  qpat_x_assum `static_mem_ok _ _ _ _ _` mp_tac >>
  simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    EVERY_APPEND] >> strip_tac >>
  gvs[is_calldatasize_copy_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    codegenRelTheory.sized_source_write_range_def,
    venomStateTheory.eval_operand_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  with_opcode_clause simp >>
  simp[venomStateTheory.eval_operand_def] >>
  Cases_on `lookup_var v s` >> gvs[] >> strip_tac >>
  mp_tac (Q.ISPEC `dst:256 word` wordsTheory.w2n_lt) >>
  simp[] >> decide_tac
QED

Theorem mm_local_zero_representative_selected_bounds[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  MEM g gs /\ r < LENGTH is /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j d bs. mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u) /\
  eom < dimword (:256) ==>
  g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
  (g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom)
Proof
  strip_tac >>
  `mm_local_group_endpoint is (SUC r)
    (mm_local_zero_capture dfg is (SUC r)) g` by
    (gvs[] >> irule mm_local_zero_representative_endpoint >> simp[]) >>
  `!j d bs. mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs) ==>
    d + LENGTH bs < dimword (:256) /\
    (LENGTH bs = 0 \/ d + LENGTH bs <= eom)` by
    (rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     drule_all mm_local_zero_capture_finite >> simp[]) >>
  `g.cg_dst + g.cg_length < dimword (:256)` by
    (fs[mm_local_group_endpoint_def] >> metis_tac[]) >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  Cases_on `g.cg_length = 0` >- simp[] >> simp[] >>
  `mm_local_group_coverage is (SUC r)
    (mm_local_zero_capture dfg is (SUC r)) g` by
    (gnvs[] >> drule_all mm_local_zero_representative_certificate >> simp[]) >>
  `?j d bs. j < SUC r /\ j < LENGTH is /\
    mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs) /\
    d <= g.cg_dst + g.cg_length - 1 /\
    g.cg_dst + g.cg_length - 1 < d + LENGTH bs` by
    (qpat_x_assum `mm_local_group_coverage _ _ _ _` mp_tac >>
     pure_rewrite_tac[mm_local_group_coverage_def] >>
     disch_then (qspec_then `g.cg_dst + g.cg_length - 1` mp_tac) >>
     asm_simp_tac pure_ss [AND_CLAUSES, EQ_CLAUSES] >>
     strip_tac >>
     `g.cg_dst <= g.cg_dst + g.cg_length - 1 /\
       g.cg_dst + g.cg_length - 1 < g.cg_dst + g.cg_length` by decide_tac >>
     gvs[] >> qexistsl [`j`,`d`,`bs`] >> gvs[]) >>
  `LENGTH bs = 0 \/ d + LENGTH bs <= eom` by metis_tac[] >> decide_tac
QED

Theorem mm_local_zero_representative_finite[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  MEM g gs /\ r < LENGTH is /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_history is H (SUC r) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j. j <= r ==> (H j).vs_current_bb = bb.bb_label /\
    (H j).vs_inst_idx = j /\ static_mem_ok eom ctx fn (EL j is) (H j)) /\
  eom < dimword (:256) ==>
  g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256)
Proof
  strip_tac >>
  `mm_local_group_endpoint is (SUC r)
    (mm_local_zero_capture dfg is (SUC r)) g` by
    (gvs[] >> irule mm_local_zero_representative_endpoint >> simp[]) >>
  `?j d bs. j < SUC r /\ j < LENGTH is /\
      mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs) /\
      d + LENGTH bs = g.cg_dst + g.cg_length` by
    (fs[mm_local_group_endpoint_def] >> metis_tac[]) >>
  `(EL j is).inst_opcode IN {MSTORE; CALLDATACOPY}` by
    (drule mm_local_zero_capture_cases >>
     gvs[is_calldatasize_copy_def, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY] >> metis_tac[]) >>
  `step_inst fuel ctx (EL j is) (H j) = OK (H (SUC j))` by
    (gvs[mm_local_history_def, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY,
       venomExecSemanticsTheory.step_inst_non_invoke]) >>
  `(H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j)` by
    (first_x_assum irule >> decide_tac) >>
  `d + LENGTH bs < dimword (:256)` by
    (drule_all mm_local_zero_capture_finite >> simp[]) >> decide_tac
QED

Theorem mm_local_zero_representative_static_bound[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  MEM g gs /\ r < LENGTH is /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_history is H (SUC r) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j. j <= r ==> (H j).vs_current_bb = bb.bb_label /\
    (H j).vs_inst_idx = j /\ static_mem_ok eom ctx fn (EL j is) (H j)) /\
  eom < dimword (:256) ==>
  g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom
Proof
  strip_tac >> Cases_on `g.cg_length = 0` >- simp[] >> simp[] >>
  `mm_local_group_coverage is (SUC r)
    (mm_local_zero_capture dfg is (SUC r)) g` by
    (gnvs[] >> drule_all mm_local_zero_representative_certificate >> simp[]) >>
  `g.cg_dst <= g.cg_dst + g.cg_length - 1 /\
    g.cg_dst + g.cg_length - 1 < g.cg_dst + g.cg_length` by decide_tac >>
  `?j d bs. j < SUC r /\ j < LENGTH is /\
    mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs) /\
    d <= g.cg_dst + g.cg_length - 1 /\
    g.cg_dst + g.cg_length - 1 < d + LENGTH bs` by
    (qpat_x_assum `mm_local_group_coverage _ _ _ _` mp_tac >>
     pure_rewrite_tac[mm_local_group_coverage_def] >>
     disch_then (qspec_then `g.cg_dst + g.cg_length - 1` mp_tac) >>
     asm_simp_tac pure_ss [AND_CLAUSES, EQ_CLAUSES] >> strip_tac >>
     qexistsl [`j`,`d`,`bs`] >> gvs[]) >>
  `(EL j is).inst_opcode IN {MSTORE; CALLDATACOPY}` by
    (drule mm_local_zero_capture_cases >>
     gvs[is_calldatasize_copy_def, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY] >> metis_tac[]) >>
  `step_inst fuel ctx (EL j is) (H j) = OK (H (SUC j))` by
    (gvs[mm_local_history_def, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY, venomExecSemanticsTheory.step_inst_non_invoke]) >>
  `(H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j)` by
    (first_x_assum irule >> decide_tac) >>
  `LENGTH bs = 0 \/ d + LENGTH bs <= eom` by
    (drule_all mm_local_zero_capture_finite >> simp[]) >> decide_tac
QED

Theorem mm_local_zero_cut_representative_write[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_zero_cut dfg is gs H r excluded pc t /\
  mm_local_zero_capture dfg is (SUC r) r = SOME (d,bs) /\
  (H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory /\
  mm_local_nonmemory_frame (H (SUC r)) = mm_local_nonmemory_frame (H r) /\
  (!v. lookup_var v (H (SUC r)) = lookup_var v (H r)) /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (REPLICATE g.cg_length 0w) t).vs_memory /\
  mm_local_nonmemory_frame t' = mm_local_nonmemory_frame t /\
  (!v. v NOTIN excluded ==> lookup_var v t' = lookup_var v t) /\
  t'.vs_inst_idx = pc' ==>
  mm_local_zero_cut dfg is gs H (SUC r) excluded pc' t'
Proof
  strip_tac >>
  `mm_local_pending (mm_local_zero_capture dfg is (SUC r))
    (mm_local_pending_indices is gs r) (H r) t` by
    (irule mm_local_pending_cap_cong >>
     qexists `mm_local_zero_capture dfg is r` >>
     fs[mm_local_zero_cut_def] >> rpt strip_tac >>
     irule mm_local_zero_capture_past >> gvs[mm_local_pending_indices_mem]) >>
  `mm_local_pending (mm_local_zero_capture dfg is (SUC r))
    (mm_local_pending_indices is gs (SUC r)) (H (SUC r)) t'` by
    (irule mm_local_zero_representative_discharge >> simp[] >>
     conj_tac >- (qexistsl [`bb`,`dfg`] >> simp[]) >>
     qexistsl [`g`,`H r`,`t`] >> gvs[]) >>
  gvs[mm_local_zero_cut_def] >> metis_tac[]
QED

Theorem mm_local_zero_store_static[local]:
  dst < dimword (:256) /\ dst + 32 <= eom ==>
  static_mem_ok eom ctx fn (mk_zero_store_inst inst dst) t
Proof
  strip_tac >> simp[unitMemInvTheory.static_mem_ok_def,
    unitMemInvTheory.inst_mem_ranges_def, mk_zero_store_inst_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def, venomStateTheory.eval_operand_def,
    wordsTheory.w2n_n2w]
QED

Theorem mm_local_zero_copy_static[local]:
  g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
  (g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom) ==>
  static_mem_ok eom ctx fn (mk_memzero_calldatacopy inst g v) u
Proof
  strip_tac >>
  simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    mk_memzero_calldatacopy_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.sized_source_write_range_def, venomStateTheory.eval_operand_def,
    wordsTheory.w2n_n2w] >>
  Cases_on `lookup_var v u` >> simp[]
QED

Theorem mm_local_zero_store_cut_exec[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_zero_cut dfg is gs H r excluded pc t /\
  mm_local_zero_capture dfg is (SUC r) r = SOME (d,bs) /\
  (H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory /\
  mm_local_nonmemory_frame (H (SUC r)) = mm_local_nonmemory_frame (H r) /\
  (!v. lookup_var v (H (SUC r)) = lookup_var v (H r)) /\
  g.cg_length = 32 /\ g.cg_dst < dimword (:256) ==>
  mm_local_exec_prefix fuel ctx [mk_zero_store_inst (EL r is) g.cg_dst] t
    ((write_memory_with_expansion g.cg_dst (REPLICATE 32 0w) t)
      with vs_inst_idx := SUC pc) /\
  mm_local_zero_cut dfg is gs H (SUC r) excluded (SUC pc)
    ((write_memory_with_expansion g.cg_dst (REPLICATE 32 0w) t)
      with vs_inst_idx := SUC pc)
Proof
  strip_tac >> conj_tac
  >- (fs[mm_local_zero_cut_def] >>
      qpat_x_assum `t.vs_inst_idx = pc` (SUBST1_TAC o SYM) >>
      irule mm_local_zero_store_fragment_exec >> simp[]) >>
  irule mm_local_zero_cut_representative_write >>
  simp[mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.write_memory_with_expansion_def,
    venomStateTheory.write_memory_def, venomStateTheory.expand_memory_def,
    venomStateTheory.lookup_var_def] >>
  conj_tac >- (qexists `bb` >> simp[]) >>
  qexistsl [`g`,`pc`,`t`] >> gvs[]
QED

Theorem mm_local_zero_copy_cut_exec[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_zero_cut dfg is gs H r excluded pc t /\
  mm_local_zero_capture dfg is (SUC r) r = SOME (d,bs) /\
  (H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory /\
  mm_local_nonmemory_frame (H (SUC r)) = mm_local_nonmemory_frame (H r) /\
  (!v. lookup_var v (H (SUC r)) = lookup_var v (H r)) /\
  g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\ v IN excluded ==>
  mm_local_exec_prefix fuel ctx
    [<|inst_id := id; inst_opcode := CALLDATASIZE;
       inst_operands := []; inst_outputs := [v]|>;
     mk_memzero_calldatacopy (EL r is) g v] t
    ((write_memory_with_expansion g.cg_dst (REPLICATE g.cg_length 0w)
      (update_var v (n2w (LENGTH t.vs_call_ctx.cc_calldata)) t))
      with vs_inst_idx := pc + 2) /\
  mm_local_zero_cut dfg is gs H (SUC r) excluded (pc + 2)
    ((write_memory_with_expansion g.cg_dst (REPLICATE g.cg_length 0w)
      (update_var v (n2w (LENGTH t.vs_call_ctx.cc_calldata)) t))
      with vs_inst_idx := pc + 2)
Proof
  strip_tac >> conj_tac
  >- (fs[mm_local_zero_cut_def] >>
      qpat_x_assum `t.vs_inst_idx = pc` (SUBST1_TAC o SYM) >>
      irule mm_local_zero_copy_fragment_exec >> simp[]) >>
  irule mm_local_zero_cut_representative_write >>
  simp[mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.write_memory_with_expansion_def,
    venomStateTheory.write_memory_def, venomStateTheory.expand_memory_def,
    venomStateTheory.lookup_var_def, venomStateTheory.update_var_def] >>
  conj_tac >- (qexists `bb` >> simp[]) >>
  qexistsl [`g`,`pc`,`t`] >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem mm_local_zero_representative_transition[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  MEM g gs /\ r < LENGTH is /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_history is H (SUC r) /\
  (!j dst v len. j < SUC r /\ is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j. j <= r ==> (H j).vs_current_bb = bb.bb_label /\
    (H j).vs_inst_idx = j /\ static_mem_ok eom ctx fn (EL j is) (H j)) /\
  eom < dimword (:256) /\
  mm_local_zero_cut dfg is gs H r excluded pc t /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL r is) = (chunk,es') ==>
  (!f u. EVERY (\i. static_mem_ok eom ctx f i u) chunk) /\
  ?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
    mm_local_zero_cut dfg is gs H (SUC r) excluded (pc + LENGTH chunk) t'
Proof
  strip_tac >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by
    metis_tac[mm_local_rep_member] >>
  `(EL r is).inst_opcode IN {MSTORE; CALLDATACOPY} /\
    ?d bs. mm_local_zero_capture dfg is (SUC r) r = SOME (d,bs)` by
    (gnvs[] >> `r < SUC r` by simp[] >>
     drule_all (Q.INST [`n` |-> `SUC r`] mm_local_zero_member_capture) >> simp[]) >>
  `(H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory` by
    (irule (cj 3 mm_local_zero_capture_sound) >>
     qexistsl [`dfg`,`is`,`SUC r`] >> simp[]) >>
  `step_inst fuel ctx (EL r is) (H r) = OK (H (SUC r))` by
    (gvs[mm_local_history_def, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY,
       venomExecSemanticsTheory.step_inst_non_invoke]) >>
  `mm_local_nonmemory_frame (H (SUC r)) = mm_local_nonmemory_frame (H r) /\
    (!v. lookup_var v (H (SUC r)) = lookup_var v (H r))` by
    (irule mm_local_write_runtime_frame >>
     metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  `g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256)` by
    (irule mm_local_zero_representative_finite >> metis_tac[]) >>
  `ALOOKUP (rep_map_of_groups is gs) (EL r is).inst_id = SOME g /\
    ~MEM (EL r is).inst_id (nop_ids_of_groups dfg Mem2Mem is gs)` by
    (gvs[] >> irule mm_local_zero_selected_rep >> simp[]) >>
  `g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom` by
    (irule mm_local_zero_representative_static_bound >> metis_tac[]) >>
  (conj_tac
  >- (Cases_on `g.cg_length = 32`
      >- (gvs[apply_memzero_inst_supply_def] >> rpt gen_tac >>
          irule mm_local_zero_store_static >> gvs[]) >>
      Cases_on `fresh_inst_id es` >> rename1 `fresh_inst_id es = (lid,es1)` >>
      Cases_on `fresh_ir_var es1` >>
      gvs[apply_memzero_inst_supply_def] >> rpt gen_tac >>
      simp[mm_local_zero_copy_static] >>
      simp[unitMemInvTheory.static_mem_ok_def,
           unitMemInvTheory.inst_mem_ranges_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def]) >>
  Cases_on `g.cg_length = 32`
  >- (gvs[apply_memzero_inst_supply_def] >>
      mp_tac (Q.INST [`is` |-> `bb.bb_instructions`,
        `gs` |-> `(scan_block_memzero dfg bb).mz_flushed`]
        mm_local_zero_store_cut_exec) >> simp[] >>
      strip_tac >> goal_assum (drule_at Any) >> gvs[arithmeticTheory.ADD1]) >>
  Cases_on `fresh_inst_id es` >> rename1 `fresh_inst_id es = (id,es1)` >>
  Cases_on `fresh_ir_var es1` >> rename1 `fresh_ir_var es1 = (v,es2)` >>
  `v IN excluded` by
    (drule irSupplyTheory.fresh_ir_var_contract >>
     gvs[irSupplyTheory.fresh_inst_id_def] >> metis_tac[]) >>
  gvs[apply_memzero_inst_supply_def] >>
  mp_tac (Q.INST [`is` |-> `bb.bb_instructions`,
    `gs` |-> `(scan_block_memzero dfg bb).mz_flushed`]
    mm_local_zero_copy_cut_exec) >> simp[] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `mm_local_exec_prefix fuel ctx chunk0 t out` >>
  qexists_tac `out` >> simp[])
QED

Theorem mm_local_zero_representative_actual_transition[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  MEM g gs /\ r < LENGTH is /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  step_inst fuel ctx (EL r is) (H r) = OK u /\
  H (SUC r) = u with vs_inst_idx := SUC r /\
  (!dst v len. is_calldatasize_copy dfg (EL r is) /\
    (EL r is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H r) = SOME (n2w (LENGTH (H r).vs_call_ctx.cc_calldata)) /\
    LENGTH (H r).vs_call_ctx.cc_calldata < dimword (:256)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j d bs. mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u) /\
  eom < dimword (:256) /\
  mm_local_zero_cut dfg is gs H r excluded pc t /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL r is) = (chunk,es') ==>
  (!f u. EVERY (\i. static_mem_ok eom ctx f i u) chunk) /\
  ?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
    mm_local_zero_cut dfg is gs H (SUC r) excluded (pc + LENGTH chunk) t'
Proof
  strip_tac >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by
    metis_tac[mm_local_rep_member] >>
  `(EL r is).inst_opcode IN {MSTORE; CALLDATACOPY} /\
    ?d bs. mm_local_zero_capture dfg is (SUC r) r = SOME (d,bs)` by
    (gnvs[] >> `r < SUC r` by simp[] >>
     drule_all (Q.INST [`n` |-> `SUC r`] mm_local_zero_member_capture) >> simp[]) >>
  `(H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory /\
    mm_local_nonmemory_frame (H (SUC r)) = mm_local_nonmemory_frame (H r) /\
    (!v. lookup_var v (H (SUC r)) = lookup_var v (H r))` by
    (drule_all mm_local_zero_capture_actual_step >> simp[]) >>
  `g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
    (g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom)` by
    (drule_all mm_local_zero_representative_selected_bounds >> simp[]) >>
  `ALOOKUP (rep_map_of_groups is gs) (EL r is).inst_id = SOME g /\
    ~MEM (EL r is).inst_id (nop_ids_of_groups dfg Mem2Mem is gs)` by
    (gvs[] >> irule mm_local_zero_selected_rep >> simp[]) >>
  (conj_tac
  >- (Cases_on `g.cg_length = 32`
      >- (gvs[apply_memzero_inst_supply_def] >> rpt gen_tac >>
          irule mm_local_zero_store_static >> gvs[]) >>
      Cases_on `fresh_inst_id es` >> rename1 `fresh_inst_id es = (lid,es1)` >>
      Cases_on `fresh_ir_var es1` >>
      gvs[apply_memzero_inst_supply_def] >> rpt gen_tac >>
      simp[mm_local_zero_copy_static] >>
      simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def]) >>
  Cases_on `g.cg_length = 32`
  >- (gvs[apply_memzero_inst_supply_def] >>
      mp_tac (Q.INST [`is` |-> `bb.bb_instructions`,
        `gs` |-> `(scan_block_memzero dfg bb).mz_flushed`]
        mm_local_zero_store_cut_exec) >> simp[] >>
      strip_tac >> goal_assum (drule_at Any) >> gvs[arithmeticTheory.ADD1]) >>
  Cases_on `fresh_inst_id es` >> rename1 `fresh_inst_id es = (id,es1)` >>
  Cases_on `fresh_ir_var es1` >> rename1 `fresh_ir_var es1 = (v,es2)` >>
  `v IN excluded` by
    (drule irSupplyTheory.fresh_ir_var_contract >>
     gvs[irSupplyTheory.fresh_inst_id_def] >> metis_tac[]) >>
  gvs[apply_memzero_inst_supply_def] >>
  mp_tac (Q.INST [`is` |-> `bb.bb_instructions`,
    `gs` |-> `(scan_block_memzero dfg bb).mz_flushed`]
    mm_local_zero_copy_cut_exec) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mm_local_exec_prefix fuel ctx chunk0 t out` >>
  qexists_tac `out` >> simp[])
QED

Theorem mm_local_zero_erased_pending_suc[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ (EL n is).inst_opcode IN {MSTORE; CALLDATACOPY} /\
  MEM (EL n is).inst_id (nop_ids_of_groups dfg Mem2Mem is gs) ==>
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]
Proof
  strip_tac >>
  `!g. MEM g gs ==> rep_of_group is g <> SOME ((EL n is).inst_id,g)` by
    (rpt strip_tac >> metis_tac[mm_local_zero_selected_rep]) >>
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
  irule mm_local_pending_indices_deferred_suc >> gvs[] >> metis_tac[]
QED

Theorem mm_local_zero_erased_transition[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  MEM g gs /\ n < LENGTH is /\ MEM (EL n is).inst_id g.cg_inst_ids /\
  MEM (EL n is).inst_id (nop_ids_of_groups dfg Mem2Mem is gs) /\
  mm_local_history is H (SUC n) /\
  (!j dst v len. j < SUC n /\ is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  mm_local_zero_cut dfg is gs H n excluded pc t ==>
  apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is) = ([mk_nop_from (EL n is)],es) /\
  mm_local_exec_prefix fuel ctx [mk_nop_from (EL n is)] t
    (t with vs_inst_idx := SUC pc) /\
  mm_local_zero_cut dfg is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >> gnvs[] >>
  SUBGOAL_THEN
    ``is_zero_store (EL n bb.bb_instructions) \/
      is_calldatasize_copy dfg (EL n bb.bb_instructions)`` assume_tac
  >- (drule_all mm_local_memzero_group_roles >> strip_tac >>
      `i = EL n bb.bb_instructions` by
        metis_tac[mmWfProofsTheory.all_distinct_map_inv, EL_MEM] >> gvs[]) >>
  `(EL n bb.bb_instructions).inst_opcode IN {MSTORE; CALLDATACOPY}` by
    gvs[is_zero_store_def, is_calldatasize_copy_def] >>
  conj_tac >- simp[apply_memzero_inst_supply_def] >>
  conj_tac
  >- (simp[mm_local_exec_prefix_single, venomInstPropsTheory.step_nop_identity,
        mk_nop_from_def, venomInstTheory.is_terminator_def] >>
      fs[mm_local_zero_cut_def]) >>
  `?d bs. mm_local_zero_capture dfg bb.bb_instructions (SUC n) n = SOME (d,bs)` by
    (simp[mm_local_zero_capture_def] >>
     Cases_on `is_zero_store (EL n bb.bb_instructions)`
     >- (fs[is_zero_store_def] >>
         rpt (CASE_TAC >> gvs[operand_lit_val_def])) >>
     fs[is_calldatasize_copy_def] >>
     rpt (CASE_TAC >> gvs[operand_lit_val_def, operand_var_def]) >>
     gvs[oneline operand_lit_val_def, oneline operand_var_def, AllCaseEqs()]) >>
  `(H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory` by
    (irule (cj 3 mm_local_zero_capture_sound) >>
     qexistsl [`dfg`,`bb.bb_instructions`,`SUC n`] >> simp[]) >>
  `mm_local_pending_indices bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed (SUC n) =
    mm_local_pending_indices bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed n ++ [n]` by
    (irule mm_local_zero_erased_pending_suc >> metis_tac[]) >>
  `step_inst fuel ctx (EL n bb.bb_instructions) (H n) = OK (H (SUC n))` by
    (fs[mm_local_history_def] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
     gvs[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  `mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
    (!v. lookup_var v (H (SUC n)) = lookup_var v (H n))` by
    (irule mm_local_write_runtime_frame >>
     metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  irule mm_local_zero_cut_erased_write_stutter >> metis_tac[]
QED

Theorem mm_local_zero_erased_actual_transition[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  MEM g gs /\ n < LENGTH is /\ MEM (EL n is).inst_id g.cg_inst_ids /\
  MEM (EL n is).inst_id (nop_ids_of_groups dfg Mem2Mem is gs) /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n /\
  (!dst v len. is_calldatasize_copy dfg (EL n is) /\
    (EL n is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H n) = SOME (n2w (LENGTH (H n).vs_call_ctx.cc_calldata)) /\
    LENGTH (H n).vs_call_ctx.cc_calldata < dimword (:256)) /\
  mm_local_zero_cut dfg is gs H n excluded pc t ==>
  apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is) = ([mk_nop_from (EL n is)],es) /\
  mm_local_exec_prefix fuel ctx [mk_nop_from (EL n is)] t
    (t with vs_inst_idx := SUC pc) /\
  mm_local_zero_cut dfg is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  `(EL n is).inst_opcode IN {MSTORE; CALLDATACOPY} /\
    ?d bs. mm_local_zero_capture dfg is (SUC n) n = SOME (d,bs)` by
    (gnvs[] >> `n < SUC n` by simp[] >>
     drule_all (Q.INST [`n` |-> `SUC n`] mm_local_zero_member_capture) >> simp[]) >>
  conj_tac >- simp[apply_memzero_inst_supply_def] >>
  conj_tac
  >- (simp[mm_local_exec_prefix_single, venomInstPropsTheory.step_nop_identity,
        mk_nop_from_def, venomInstTheory.is_terminator_def] >>
      fs[mm_local_zero_cut_def]) >>
  `(H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory /\
    mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
    (!v. lookup_var v (H (SUC n)) = lookup_var v (H n))` by
    (drule_all mm_local_zero_capture_actual_step >> simp[]) >>
  `mm_local_pending_indices is gs (SUC n) =
    mm_local_pending_indices is gs n ++ [n]` by
    (irule mm_local_zero_erased_pending_suc >> metis_tac[]) >>
  irule mm_local_zero_cut_erased_write_stutter >> metis_tac[]
QED

Theorem mm_local_zero_barrier_pending_empty[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ is_volatile_memory (EL n is) /\
  ~is_zero_store (EL n is) /\ ~is_calldatasize_copy dfg (EL n is) /\
  n <= m /\ m <= SUC n ==>
  mm_local_pending_indices is gs m = []
Proof
  strip_tac >>
  Cases_on `mm_local_pending_indices is gs m` >- simp[] >>
  rename1 `mm_local_pending_indices is gs m = j::js` >>
  `MEM j (mm_local_pending_indices is gs m)` by simp[] >>
  qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `j <= n` by decide_tac >>
  `j <> n` by
    (strip_tac >> gnvs[] >> drule_all mm_local_memzero_group_roles >>
     strip_tac >>
     (`j < LENGTH bb.bb_instructions` by decide_tac >>
      `i = EL j bb.bb_instructions` by
        metis_tac[mmWfProofsTheory.all_distinct_map_inv, EL_MEM] >>
      metis_tac[])) >>
  `MEM (EL j is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (pure_rewrite_tac [MEM_MAP] >> qexists_tac `EL j is` >>
     conj_tac >- simp[] >>
     pure_rewrite_tac [MEM_EL] >> qexists_tac `j` >>
     `j < n /\ n <= LENGTH bb.bb_instructions` by (gvs[] >> decide_tac) >>
     simp[listTheory.LENGTH_TAKE, listTheory.EL_TAKE]) >>
  `bb.bb_instructions = TAKE n is ++ [EL n is] ++ DROP (SUC n) is` by
    gvs[rich_listTheory.TAKE_DROP_SUC] >>
  drule mm_local_memzero_barrier_position >>
  pop_assum kall_tac >>
  disch_then (qspecl_then [`(EL j is).inst_id`,`dfg`,`g`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  gnvs[] >>
  `n <= LENGTH bb.bb_instructions` by decide_tac >>
  `k < LENGTH bb.bb_instructions` by
    (fs[listTheory.LENGTH_TAKE] >> decide_tac) >>
  `EL k (MAP (\i. i.inst_id) bb.bb_instructions) =
   EL r (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (fs[EL_MAP]) >>
  `k = r` by
    (drule listTheory.ALL_DISTINCT_EL_IMP >>
     disch_then (qspecl_then [`k`,`r`] mp_tac) >> simp[]) >>
  fs[listTheory.LENGTH_TAKE] >> decide_tac
QED

Theorem mm_local_zero_barrier_transition[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ is_volatile_memory (EL n is) /\
  ~is_zero_store (EL n is) /\ ~is_calldatasize_copy dfg (EL n is) /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  ~is_terminator (EL n is).inst_opcode /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_zero_cut dfg is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >>
  `mm_local_pending_indices is gs n = [] /\
   mm_local_pending_indices is gs (SUC n) = []` by
    (conj_tac >> irule mm_local_zero_barrier_pending_empty >>
     qexistsl [`bb`,`dfg`,`n`] >> gvs[]) >>
  `state_equiv excluded ((H n) with vs_inst_idx := pc) t` by
    metis_tac[mm_local_zero_cut_empty] >>
  `step_inst fuel ctx (EL n is) ((H n) with vs_inst_idx := pc) =
   OK (u with vs_inst_idx := pc)` by
    (Cases_on `(EL n is).inst_opcode = INVOKE`
     >- simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
     simp[analysisSimProofsBaseTheory.step_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def]) >>
  drule_all removeUnusedProofsTheory.step_inst_result_equiv_full >>
  disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
  Cases_on `step_inst fuel ctx (EL n is) t` >>
  simp[result_equiv_def] >> strip_tac >>
  qexists_tac `v with vs_inst_idx := SUC pc` >>
  conj_tac
  >- gvs[mm_local_exec_prefix_single, mm_local_zero_cut_def] >>
  gvs[mm_local_zero_cut_def, mm_local_pending_empty, state_equiv_frame,
    mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.lookup_var_def, venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_zero_nonvolatile_successor[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ ~is_volatile_memory (EL n is) ==>
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
  mm_local_zero_capture dfg is (SUC n) = mm_local_zero_capture dfg is n
Proof
  strip_tac >>
  `~is_zero_store (EL n is) /\ ~is_calldatasize_copy dfg (EL n is)` by
    (Cases_on `(EL n is).inst_opcode` >>
     gvs[is_volatile_memory_def, is_zero_store_def, is_calldatasize_copy_def,
       venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
       venomEffectsTheory.all_effects_def]) >>
  `!g. MEM g gs ==> rep_of_group is g <> SOME ((EL n is).inst_id,g)` by
    (rpt strip_tac >> drule mm_local_rep_member >> strip_tac >>
     gvs[] >> drule_all mm_local_memzero_group_roles >> strip_tac >>
     `i = EL n bb.bb_instructions` by
       (gvs[] >> metis_tac[mmWfProofsTheory.all_distinct_map_inv, EL_MEM]) >>
     metis_tac[]) >>
  `~((EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES})` by
    (Cases_on `(EL n is).inst_opcode` >>
     gvs[is_volatile_memory_def, venomEffectsTheory.read_effects_def,
       venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def]) >>
  conj_tac
  >- (gvs[] >>
      simp[mm_local_pending_indices_def, rich_listTheory.COUNT_LIST_SNOC,
        rich_listTheory.SNOC_APPEND, FILTER_APPEND] >>
      AP_THM_TAC >> AP_TERM_TAC >> rewrite_tac[FUN_EQ_THM] >>
      qx_gen_tac `j` >>
      eq_tac >> strip_tac >> gvs[]
      >- (qexistsl [`g`,`r`] >> simp[] >> decide_tac) >>
      `r <> n` by metis_tac[] >> qexistsl [`g`,`r`] >> simp[] >> decide_tac) >>
  rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `j` >>
  (Cases_on `j = n` >- gvs[mm_local_zero_capture_def]) >>
  `j < SUC n <=> j < n` by decide_tac >> simp[mm_local_zero_capture_def]
QED

Theorem mm_local_zero_nonvolatile_transition[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ ~is_volatile_memory (EL n is) /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  ~is_terminator (EL n is).inst_opcode /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_zero_cut dfg is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >> drule mm_local_nonvolatile_effects >> strip_tac >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
   mm_local_zero_capture dfg is (SUC n) = mm_local_zero_capture dfg is n` by
    metis_tac[mm_local_zero_nonvolatile_successor] >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    gvs[mm_local_zero_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
      stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
      venomStateTheory.venom_state_component_equality] >>
  `step_inst fuel ctx (EL n is)
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) =
    OK (u with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>)` by
    (Cases_on `(EL n is).inst_opcode = ALLOCA`
     >- (irule venomExecutionReplayPropsTheory.alloca_memory_frame >>
         simp[analysisSimProofsBaseTheory.step_inst_idx_indep,
           instIdxIndepTheory.exec_result_map_def]) >>
     `~is_alloca_op (EL n is).inst_opcode` by
       (Cases_on `(EL n is).inst_opcode` >> fs[venomInstTheory.is_alloca_op_def]) >>
     irule passSharedFieldTheory.step_inst_mem_frame >>
     simp[analysisSimProofsBaseTheory.step_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def]) >>
  drule_all removeUnusedProofsTheory.step_inst_result_equiv_full >>
  disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
  Cases_on `step_inst fuel ctx (EL n is) t` >>
  simp[result_equiv_def] >> strip_tac >>
  `u.vs_memory = (H n).vs_memory /\ v.vs_memory = t.vs_memory` by
    (Cases_on `(EL n is).inst_opcode = ALLOCA`
     >- metis_tac[venomMemPropsTheory.step_inst_alloca_preserves_memory,
          venomInstTheory.is_alloca_op_def] >>
     `~is_alloca_op (EL n is).inst_opcode` by
       (Cases_on `(EL n is).inst_opcode` >> fs[venomInstTheory.is_alloca_op_def]) >>
     metis_tac[passSharedFieldTheory.step_inst_preserves_all]) >>
  qexists_tac `v with vs_inst_idx := SUC pc` >> conj_tac
  >- gvs[mm_local_exec_prefix_single, mm_local_zero_cut_def] >>
  gvs[mm_local_zero_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
    venomStateTheory.venom_state_component_equality] >>
  gvs[mm_local_pending_def] >> qexists_tac `ws` >> simp[] >>
  irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]
QED

Theorem mm_local_zero_retained_selected_dispatch[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ MEM i bb.bb_instructions /\
  (is_zero_store i \/ is_calldatasize_copy (dfg_build_function fn0) i) /\
  ~MEM i.inst_id (nop_ids_of_groups (dfg_build_function fn0) Mem2Mem
    bb.bb_instructions (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed) ==>
  ?g. MEM g (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed /\
    rep_of_group bb.bb_instructions g = SOME (i.inst_id,g)
Proof
  strip_tac >>
  `mm_local_prefix fn0 supply index 0 = (bb,supply)` by
    gvs[mm_local_prefix_def] >>
  `i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    gvs[is_zero_store_def, is_calldatasize_copy_def] >>
  `i.inst_opcode NOTIN {MLOAD; CALLDATALOAD; DLOAD}` by gvs[] >>
  `dfg_get_inst_by_id (dfg_build_function fn0) i.inst_id = SOME i` by
    (irule venomTransformStructurePropsTheory.function_ids_exact >> simp[] >>
     irule venomFnInstsProofsTheory.MEM_fn_insts >> qexists `bb` >> gvs[EL_MEM]) >>
  `!v li. dfg_get_def (dfg_build_function fn0) v = SOME li ==>
    li.inst_id <> i.inst_id` by
    (rpt gen_tac >> disch_tac >>
     irule mm_local_prefix_write_not_def >>
     simp[] >> qexistsl [`bb`,`fn0`,`index`,`0`,`supply`,`supply`,`v`] >> simp[]) >>
  `?g. MEM g (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed /\
    MEM i.inst_id g.cg_inst_ids` by metis_tac[mm_local_zero_selected_member] >>
  qexists `g` >> simp[] >> irule mm_local_retained_store_rep >>
  simp[] >> (reverse conj_tac >- metis_tac[]) >>
  qexistsl [`dfg_build_function fn0`,
    `(scan_block_memzero (dfg_build_function fn0) bb).mz_flushed`,`Mem2Mem`] >>
  simp[rep_pin_id_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem mm_local_zero_selected_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\
  (is_zero_store (EL n is) \/ is_calldatasize_copy dfg (EL n is)) /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n /\
  (!dst v len. is_calldatasize_copy dfg (EL n is) /\
    (EL n is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H n) = SOME (n2w (LENGTH (H n).vs_call_ctx.cc_calldata)) /\
    LENGTH (H n).vs_call_ctx.cc_calldata < dimword (:256)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j d bs. mm_local_zero_capture dfg is (SUC n) j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u) /\
  eom < dimword (:256) /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is) = (chunk,es') ==>
  (!f u. EVERY (\i. static_mem_ok eom ctx f i u) chunk) /\
  ?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
    mm_local_zero_cut dfg is gs H (SUC n) excluded (pc + LENGTH chunk) t'
Proof
  strip_tac >> (
  Cases_on `MEM (EL n is).inst_id (nop_ids_of_groups dfg Mem2Mem is gs)`
  >- (`?g. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids` by
        (gvs[] >> metis_tac[mm_local_zero_selected_member, EL_MEM]) >>
      drule_all mm_local_zero_erased_actual_transition >>
      disch_then (qspec_then `es` strip_assume_tac) >>
      gvs[] >> simp[mk_nop_from_def, unitMemInvTheory.static_mem_ok_def,
        unitMemInvTheory.inst_mem_ranges_def,
        contextCodegenRelTheory.source_memory_read_ranges_def,
        codegenRelTheory.source_memory_write_ranges_def, arithmeticTheory.ADD1] >>
      metis_tac[mk_nop_from_def, arithmeticTheory.ADD1]) >>
  `?g. MEM g gs /\ rep_of_group is g = SOME ((EL n is).inst_id,g)` by
    (gvs[] >> irule mm_local_zero_retained_selected_dispatch >>
     simp[EL_MEM] >> metis_tac[]) >>
  drule_all mm_local_zero_representative_actual_transition >> simp[])
QED

Theorem mm_local_zero_actual_transition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ ~is_terminator (EL n is).inst_opcode /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n /\
  (!dst v len. is_calldatasize_copy dfg (EL n is) /\
    (EL n is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H n) = SOME (n2w (LENGTH (H n).vs_call_ctx.cc_calldata)) /\
    LENGTH (H n).vs_call_ctx.cc_calldata < dimword (:256)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j d bs. mm_local_zero_capture dfg is (SUC n) j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u) /\
  eom < dimword (:256) /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is) = (chunk,es') ==>
  ?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
    mm_local_zero_cut dfg is gs H (SUC n) excluded (pc + LENGTH chunk) t'
Proof
  strip_tac >>
  Cases_on `is_zero_store (EL n is) \/ is_calldatasize_copy dfg (EL n is)`
  >- (drule_all mm_local_zero_selected_transition >> simp[]) >>
  `apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is) = ([EL n is],es)` by
    (qpat_x_assum `apply_memzero_inst_supply _ _ _ _ = _` kall_tac >>
     gvs[] >> irule mm_local_memzero_nonselected_unchanged >> simp[EL_MEM]) >>
  `chunk = [EL n is]` by metis_tac[pairTheory.PAIR_EQ] >>
  `~is_zero_store (EL n is) /\ ~is_calldatasize_copy dfg (EL n is)` by metis_tac[] >>
  simp[] >>
  Cases_on `is_volatile_memory (EL n is)`
  >- (drule_all mm_local_zero_barrier_transition >> simp[arithmeticTheory.ADD1]) >>
  drule_all mm_local_zero_nonvolatile_transition >> simp[arithmeticTheory.ADD1]
QED

Theorem mm_local_zero_actual_interval[local]:
  !m n es t pc out es'.
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  h = phi_prefix_length is /\ h <= n /\ n + m <= LENGTH is /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ eom < dimword (:256) /\
  (!j. h <= j /\ j < n + m ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ~is_terminator (EL j is).inst_opcode /\
    (!v. MEM (Var v) (EL j is).inst_operands ==> v NOTIN excluded) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
      H (SUC j) = u with vs_inst_idx := SUC j) /\
  (!j dst v len. h <= j /\ j < n + m /\
    is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  (!j. n <= j /\ j <= n + m ==>
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  mm_flat_map_supply
    (apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
      (rep_map_of_groups is gs)) es (TAKE m (DROP n is)) = (out,es') ==>
  ?t'. mm_local_exec_prefix fuel ctx out t t' /\
    mm_local_zero_cut dfg is gs H (n + m) excluded (pc + LENGTH out) t'
Proof
  Induct_on `m`
  >- (simp[mm_flat_map_supply_def, mm_local_exec_prefix_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `n < LENGTH is` by decide_tac >>
  `TAKE (SUC m) (DROP n is) = EL n is :: TAKE m (DROP (SUC n) is)` by
    simp[rich_listTheory.DROP_CONS_EL] >>
  Cases_on `apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is)` >>
  rename1 `apply_memzero_inst_supply _ _ es (EL n is) = (chunk,es1)` >>
  Cases_on `mm_flat_map_supply
    (apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
      (rep_map_of_groups is gs)) es1 (TAKE m (DROP (SUC n) is))` >>
  rename1 `mm_flat_map_supply _ es1 _ = (tail,es2)` >>
  `out = chunk ++ tail /\ es' = es2` by
    gvs[mm_flat_map_supply_def] >>
  `?u. step_inst fuel ctx (EL n is) (H n) = OK u /\
    H (SUC n) = u with vs_inst_idx := SUC n` by
    (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `(H n).vs_current_bb = bb.bb_label /\ (H n).vs_inst_idx = n /\
    static_mem_ok eom ctx fn (EL n is) (H n) /\
    ~is_terminator (EL n is).inst_opcode /\
    (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded)` by
    (qpat_x_assum `!j. h <= j /\ j < n + SUC m ==> _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by
    (fs[mm_local_zero_cut_def, mm_local_nonmemory_frame_def] >>
     metis_tac[arithmeticTheory.LE_REFL, arithmeticTheory.LE_ADD]) >>
  `!j d bs. mm_local_zero_capture dfg is (SUC n) j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u` by
    (rpt strip_tac >>
     `h <= j /\ j < n + SUC m` by
       (drule mm_local_zero_capture_cases >>
        drule mm_local_zero_capture_after_phis >> gvs[] >> decide_tac) >>
     metis_tac[]) >>
  `!dst v len. is_calldatasize_copy dfg (EL n is) /\
    (EL n is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H n) = SOME (n2w (LENGTH (H n).vs_call_ctx.cc_calldata)) /\
    LENGTH (H n).vs_call_ctx.cc_calldata < dimword (:256)` by
    (rpt strip_tac >>
     qpat_x_assum `!j dst v len. _` (qspec_then `n` mp_tac) >> simp[]) >>
  `?t1. mm_local_exec_prefix fuel ctx chunk t t1 /\
    mm_local_zero_cut dfg is gs H (SUC n) excluded (pc + LENGTH chunk) t1` by
    (drule_all mm_local_zero_actual_transition >> simp[]) >>
  `!v. v NOTIN excluded ==> MEM v es1.irs_used_vars` by
    (drule_at (Pat `apply_memzero_inst_supply _ _ _ _ = _`)
       mm_local_memzero_old_use >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `!n es t pc out es'. _`
    (qspecl_then [`SUC n`,`es1`,`t1`,`pc + LENGTH chunk`,`tail`,`es2`] mp_tac) >>
  (impl_tac >- (gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >>
    rpt strip_tac >> metis_tac[])) >>
  strip_tac >> qexists `t'` >>
  conj_tac
  >- (asm_rewrite_tac[] >> rewrite_tac[mm_local_exec_prefix_append] >>
      qexists `t1` >> simp[]) >>
  `n + SUC m = SUC n + m` by decide_tac >>
  `pc + LENGTH out = pc + LENGTH chunk + LENGTH tail` by simp[] >>
  metis_tac[]
QED

Theorem mm_local_zero_no_output_recognition[local]:
  i.inst_outputs = [] /\
  apply_memzero_inst_supply ns rm s i = (out,s') /\
  (!v. p = Var v ==> MEM v s.irs_used_vars) /\
  (!v. q = Var v ==> MEM v s.irs_used_vars) ==>
  same_after_assigns (REVERSE out ++ xs) p q = same_after_assigns xs p q
Proof
  strip_tac >> Cases_on `p = q`
  >- simp[contextCodegenRelPropsTheory.same_after_assigns_refl] >>
  gvs[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def,
      mk_memzero_calldatacopy_def, irSupplyTheory.fresh_inst_id_def] >>
  TRY (drule irSupplyTheory.fresh_ir_var_contract >> strip_tac) >>
  Cases_on `p` >> Cases_on `q` >>
  gvs[contextCodegenRelTheory.same_after_assigns_def,
      contextCodegenRelTheory.step_back_assign_def] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem mm_local_zero_same_after_assigns_list[local]:
  !xs s out s' P p q.
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  f = apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) /\
  EVERY (\i. MEM i bb.bb_instructions /\ inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) xs /\
  (!v. v IN P ==> MEM v s.irs_used_vars) /\
  (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
  mm_flat_map_supply f s xs = (out,s') /\
  same_after_assigns (REVERSE xs) p q ==>
  same_after_assigns (REVERSE out) p q
Proof
  Induct using listTheory.SNOC_INDUCT
  >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `p = q`
  >- simp[contextCodegenRelPropsTheory.same_after_assigns_refl] >>
  fs[listTheory.SNOC_APPEND] >>
  Cases_on `mm_flat_map_supply f s xs` >>
  rename1 `mm_flat_map_supply f s xs = (pre,sm)` >>
  Cases_on `f sm x` >> rename1 `f sm x = (chunk,se)` >>
  `out = pre ++ chunk /\ s' = se` by
    (`mm_flat_map_supply f sm [x] = (chunk,se)` by
       simp[mm_flat_map_supply_def] >>
     drule_all mm_local_flat_map_supply_append >> simp[]) >>
  `!v. v IN P ==> MEM v sm.irs_used_vars` by
    (drule_at (Pat `mm_flat_map_supply _ _ _ = _`)
       (Q.ISPEC `venomInst$inst_uses` mm_local_list_old_vars) >>
     simp[] >>
     (impl_tac >- metis_tac[mm_local_memzero_old_use]) >>
     strip_tac >> metis_tac[]) >>
  Cases_on `x.inst_outputs = []`
  >- (`same_after_assigns (REVERSE chunk ++ REVERSE pre) p q =
       same_after_assigns (REVERSE pre) p q` by
        (irule mm_local_zero_no_output_recognition >> metis_tac[]) >>
      `same_after_assigns (REVERSE xs) p q` by
        (Cases_on `p` >> Cases_on `q` >>
         gvs[REVERSE_APPEND, contextCodegenRelTheory.same_after_assigns_def,
             contextCodegenRelTheory.step_back_assign_def]) >>
      gvs[REVERSE_APPEND] >> first_x_assum irule >> metis_tac[]) >>
  `chunk = [x] /\ se = sm` by
    (drule_all mm_local_memzero_producer_unchanged >>
     disch_then (qspecl_then [`dfg`,`sm`] mp_tac) >> gvs[]) >>
  gvs[REVERSE_APPEND, contextCodegenRelTheory.same_after_assigns_def] >>
  Cases_on `step_back_assign x p` >- gvs[] >>
  Cases_on `step_back_assign x q` >- gvs[] >> gvs[] >>
  rename1 `step_back_assign x p = SOME p1` >>
  rename1 `step_back_assign x q = SOME q1` >>
  `(!v. p1 = Var v ==> v IN P) /\
   (!v. q1 = Var v ==> v IN P)` by
    (qpat_x_assum `!s out s' P p q. _` kall_tac >>
     metis_tac[contextCodegenRelPropsTheory.step_back_assign_preserves_vars]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem mm_local_zero_same_after_assigns_prefix[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  f = apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) /\
  EVERY (\i. inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) bb.bb_instructions /\
  (!v. v IN P ==> MEM v supply.irs_used_vars) /\
  (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
  mm_flat_map_supply f supply (TAKE n bb.bb_instructions) = (pre,sn) /\
  same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) p q ==>
  same_after_assigns (REVERSE pre) p q
Proof
  strip_tac >> irule mm_local_zero_same_after_assigns_list >>
  goal_assum (drule_at Any) >> qexists `P` >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem mm_local_zero_assign_interval[local]:
  !xs s out s'.
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = ASSIGN) xs /\
  mm_flat_map_supply
    (apply_memzero_inst_supply
      (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
        (scan_block_memzero dfg bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block_memzero dfg bb).mz_flushed)) s xs = (out,s') ==>
  out = xs /\ s' = s
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >>
  `!r. apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) r h = ([h],r)` by
    (irule mm_local_memzero_nonselected_unchanged >>
     gvs[is_zero_store_def, is_calldatasize_copy_def]) >>
  gvs[mm_flat_map_supply_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem mm_local_flat_map_supply_identity[local]:
  !xs es out es'.
  (!i es. MEM i xs ==> f es i = ([i],es)) /\
  mm_flat_map_supply f es xs = (out,es') ==>
  out = xs /\ es' = es
Proof
  Induct_on `xs` >> simp[mm_flat_map_supply_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem mm_local_forward_layout[local]:
  bb.bb_instructions = left ++ a :: gap ++ b :: right /\
  (!i es. MEM i (a :: gap ++ [b]) ==> f es i = ([i],es)) /\
  mm_flat_map_supply f supply left = (pre,sm) /\
  mm_flat_map_supply f supply bb.bb_instructions = (bb'.bb_instructions,supply') ==>
  (?tail. bb'.bb_instructions = pre ++ a :: gap ++ b :: tail /\
    mm_flat_map_supply f sm right = (tail,supply')) /\
  mm_flat_map_supply f supply (left ++ a :: gap) = (pre ++ a :: gap,sm)
Proof
  strip_tac >>
  `(!s. f s a = ([a],s)) /\ (!s. f s b = ([b],s))` by simp[] >>
  Cases_on `mm_flat_map_supply f sm gap` >>
  rename1 `mm_flat_map_supply f sm gap = (gap',sg)` >>
  `gap' = gap /\ sg = sm` by
    (irule mm_local_flat_map_supply_identity >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `gap' = gap` SUBST_ALL_TAC >>
  qpat_x_assum `sg = sm` SUBST_ALL_TAC >>
  `mm_flat_map_supply f sm (a :: gap) = (a :: gap,sm)` by
    simp[mm_flat_map_supply_def] >>
  `mm_flat_map_supply f supply (left ++ a :: gap) = (pre ++ a :: gap,sm)` by
    (irule mm_local_flat_map_supply_append >> goal_assum (drule_at Any) >> simp[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `mm_flat_map_supply f sm right` >>
  rename1 `mm_flat_map_supply f sm right = (tail,sr)` >>
  `mm_flat_map_supply f sm (a :: gap ++ b :: right) =
    (a :: gap ++ b :: tail,sr)` by
    (`mm_flat_map_supply f sm (b :: right) = (b :: tail,sr)` by
       simp[mm_flat_map_supply_def] >>
     `mm_flat_map_supply f sm (gap ++ b :: right) =
       (gap ++ b :: tail,sr)` by
       (irule mm_local_flat_map_supply_append >>
        goal_assum (drule_at Any) >> simp[]) >>
     simp[mm_flat_map_supply_def]) >>
  `mm_flat_map_supply f supply bb.bb_instructions =
    (pre ++ a :: gap ++ b :: tail,sr)` by
    (qpat_assum `bb.bb_instructions = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule mm_local_flat_map_supply_append >>
     goal_assum (drule_at Any) >> simp[mm_flat_map_supply_def]) >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Theorem mm_local_revert_forward_transport[local]:
  EVERY (\x. inst_wf x /\
    !v. MEM (Var v) x.inst_operands ==> v IN P) bb.bb_instructions /\
  (!x es. MEM x bb.bb_instructions /\
    x.inst_opcode IN {ASSIGN; RETURNDATACOPY; REVERT} ==>
    f es x = ([x],es)) /\
  (!n pre sn p q.
    (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
    mm_flat_map_supply f supply (TAKE n bb.bb_instructions) = (pre,sn) /\
    same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) p q ==>
    same_after_assigns (REVERSE pre) p q) /\
  mm_flat_map_supply f supply (TAKE i bb.bb_instructions) = (pre,si) /\
  mm_flat_map_supply f supply (TAKE j bb.bb_instructions) = (prej,sj) /\
  mm_flat_map_supply f supply bb.bb_instructions = (bb'.bb_instructions,supply') /\
  revert_forward_pair bb i j ==>
  revert_forward_pair bb' (LENGTH pre) (LENGTH prej)

Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb i j`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [contextCodegenRelTheory.revert_forward_pair_def, venomInstTheory.get_instruction_def]) >>
  qabbrev_tac `inst1 = EL i bb.bb_instructions` >>
  qabbrev_tac `inst2 = EL j bb.bb_instructions` >>
  qabbrev_tac `left = TAKE i bb.bb_instructions` >>
  qabbrev_tac `gap = TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)` >>
  qabbrev_tac `right = DROP (SUC j) bb.bb_instructions` >>
  `bb.bb_instructions = left ++ inst1 :: gap ++ inst2 :: right /\
   LENGTH left = i /\ LENGTH gap = j - SUC i /\
   TAKE j bb.bb_instructions = left ++ inst1 :: gap` by
    suspend "source_layout" >>
  `EVERY (\x. x.inst_opcode = ASSIGN) gap` by
    (simp[Abbr `gap`, EVERY_EL, EL_TAKE, EL_DROP] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!x es. MEM x (inst1 :: gap ++ [inst2]) ==> f es x = ([x],es)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  drule_all mm_local_forward_layout >> strip_tac >>
  `prej = pre ++ inst1 :: gap` by metis_tac[pairTheory.PAIR_EQ] >>
  `(!v. src = Var v ==> v IN P) /\
   (!v. p = Var v ==> v IN P) /\
   (!v. rds = Var v ==> v IN P) /\
   (!v. p' = Var v ==> v IN P) /\
   (!v. rds' = Var v ==> v IN P)` by
    (fs[EVERY_MEM] >> metis_tac[MEM, EL_MEM]) >>
  `EVERY (\x. !v. MEM (Var v) x.inst_operands ==> v IN P) (REVERSE gap)` by
    (fs[EVERY_MEM, MEM_REVERSE] >> metis_tac[MEM_APPEND]) >>
  `(!v. resolve_block_assigns (REVERSE gap) p' = Var v ==> v IN P) /\
   (!v. resolve_block_assigns (REVERSE gap) rds' = Var v ==> v IN P)` by
    metis_tac[contextCodegenRelPropsTheory.resolve_block_assigns_preserves_vars] >>
  `same_after_assigns (REVERSE pre) src (Lit 0w) /\
   same_after_assigns (REVERSE pre) p (resolve_block_assigns (REVERSE gap) p') /\
   same_after_assigns (REVERSE pre) rds (resolve_block_assigns (REVERSE gap) rds')` by
    (qpat_assum `!n pre sn p q. _` (qspecl_then [`i`,`pre`,`si`] mp_tac) >>
     simp[Abbr `left`] >> metis_tac[]) >>
  suspend "target_layout"
QED

Resume mm_local_revert_forward_transport[source_layout]:
  `SUC i + (j - SUC i) = j /\ SUC (i + j - SUC i) = j` by decide_tac >>
  `DROP (SUC i) bb.bb_instructions = gap ++ inst2 :: right` by
    (qspecl_then [`j - SUC i`,`DROP (SUC i) bb.bb_instructions`] mp_tac
       rich_listTheory.TAKE_DROP_SUC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[Abbr `gap`, Abbr `inst2`, Abbr `right`, EL_DROP, DROP_DROP,
       arithmeticTheory.ADD_CLAUSES]) >>
  `bb.bb_instructions = left ++ inst1 :: gap ++ inst2 :: right` by
    (qspecl_then [`i`,`bb.bb_instructions`] mp_tac rich_listTheory.TAKE_DROP_SUC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[Abbr `left`, Abbr `inst1`]) >>
  `LENGTH left = i /\ LENGTH gap = j - SUC i` by
    simp[Abbr `left`, Abbr `gap`] >>
  asm_rewrite_tac[] >>
  `j = LENGTH left + SUC (LENGTH gap)` by decide_tac >>
  pop_assum SUBST1_TAC >> simp[NoAsms, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, arithmeticTheory.ADD1]
QED

Resume mm_local_revert_forward_transport[target_layout]:
  qpat_x_assum `!n pre sn p q. _` kall_tac >>
  qpat_x_assum `!x es. _` kall_tac >>
  qpat_x_assum `LENGTH gap = _` kall_tac >>
  simp[contextCodegenRelTheory.revert_forward_pair_def,
    venomInstTheory.get_instruction_def, EL_APPEND_EQN,
    TAKE_APPEND, DROP_APPEND, arithmeticTheory.ADD1] >>
  `LENGTH pre - (LENGTH gap + (LENGTH pre + 1)) = 0 /\
   LENGTH pre - (LENGTH pre + 1) = 0 /\
   LENGTH pre + 1 - (LENGTH gap + (LENGTH pre + 1)) = 0` by decide_tac >>
  simp[] >> conj_tac >- (
    rpt strip_tac >>
    `k - LENGTH pre = SUC (k - LENGTH pre - 1) /\
     k - LENGTH pre - 1 < LENGTH gap` by decide_tac >>
    simp[] >> fs[EVERY_EL]) >>
  `DROP (LENGTH pre + 1) pre = []` by simp[DROP_EQ_NIL] >> simp[]
QED

Finalise mm_local_revert_forward_transport

Theorem mm_local_in_revert_forward_transport[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  index < LENGTH fn.fn_blocks /\ bb = EL index fn.fn_blocks /\
  bb'.bb_label = bb.bb_label /\
  EVERY (\x. inst_wf x /\
    !v. MEM (Var v) x.inst_operands ==> v IN P) bb.bb_instructions /\
  (!x es. MEM x bb.bb_instructions /\
    x.inst_opcode IN {ASSIGN; RETURNDATACOPY; REVERT} ==>
    f es x = ([x],es)) /\
  (!n pre sn p q.
    (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
    mm_flat_map_supply f supply (TAKE n bb.bb_instructions) = (pre,sn) /\
    same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) p q ==>
    same_after_assigns (REVERSE pre) p q) /\
  mm_flat_map_supply f supply bb.bb_instructions = (bb'.bb_instructions,supply') /\
  mm_flat_map_supply f supply (TAKE n bb.bb_instructions) = (pre,sn) /\
  s.vs_current_bb = bb.bb_label /\ s.vs_inst_idx = n /\
  t.vs_current_bb = bb.bb_label /\ t.vs_inst_idx = LENGTH pre /\
  in_revert_forward fn s ==>
  in_revert_forward (fn with fn_blocks := LUPDATE bb' index fn.fn_blocks) t

Proof
  strip_tac >>
  `MAP (\b. b.bb_label) (LUPDATE bb' index fn.fn_blocks) =
   MAP (\b. b.bb_label) fn.fn_blocks` by
    (simp[NoAsms, LUPDATE_MAP] >>
     `bb'.bb_label = EL index (MAP (\b. b.bb_label) fn.fn_blocks)` by simp[EL_MAP] >>
     pop_assum SUBST1_TAC >> irule LUPDATE_SAME >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[EL_MEM]) >>
  `lookup_block t.vs_current_bb (LUPDATE bb' index fn.fn_blocks) = SOME bb'` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[MEM_LUPDATE] >>
     metis_tac[]) >>
  `revert_forward_at bb n` by
    gvs[contextCodegenRelTheory.in_revert_forward_def] >>
  simp[contextCodegenRelTheory.in_revert_forward_def] >>
  qexists `bb'` >> conj_tac >- metis_tac[] >>
  qpat_x_assum `revert_forward_at bb n` mp_tac >>
  pure_rewrite_tac[contextCodegenRelTheory.revert_forward_at_def] >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  Cases_on `mm_flat_map_supply f supply (TAKE j bb.bb_instructions)` >>
  rename1 `mm_flat_map_supply f supply (TAKE j bb.bb_instructions) = (prej,sj)` >>
  qexists `LENGTH prej` >>
  drule_all mm_local_revert_forward_transport >> simp[]
QED

Theorem mm_local_zero_forward_layout[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  bb.bb_instructions = left ++ a :: gap ++ b :: right /\
  a.inst_opcode = RETURNDATACOPY /\ b.inst_opcode = REVERT /\
  EVERY (\i. i.inst_opcode = ASSIGN) gap /\
  f = apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) /\
  mm_flat_map_supply f supply left = (pre,sm) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') ==>
  (?tail. bb'.bb_instructions = pre ++ a :: gap ++ b :: tail /\
    mm_flat_map_supply f sm right = (tail,supply')) /\
  mm_flat_map_supply f supply (left ++ a :: gap) = (pre ++ a :: gap,sm)
Proof
  strip_tac >>
  `mm_flat_map_supply f supply bb.bb_instructions = (bb'.bb_instructions,supply')` by
    (qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
     simp[transform_block_memzero_supply_def] >> gvs[] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `!x es. MEM x bb.bb_instructions /\
    x.inst_opcode IN {ASSIGN; RETURNDATACOPY; REVERT} ==>
    f es x = ([x],es)` by
    (rpt strip_tac >>
     qpat_assum `f = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule mm_local_memzero_nonselected_unchanged >>
     conj_tac >- first_assum ACCEPT_TAC >>
     gvs[is_zero_store_def, is_calldatasize_copy_def,
       pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  `!x es. MEM x (a :: gap ++ [b]) ==> f es x = ([x],es)` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  drule_all mm_local_forward_layout >> simp[]
QED

Theorem mm_local_zero_revert_forward_transport[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  f = apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) /\
  EVERY (\i. inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) bb.bb_instructions /\
  (!v. v IN P ==> MEM v supply.irs_used_vars) /\
  mm_flat_map_supply f supply (TAKE i bb.bb_instructions) = (pre,si) /\
  mm_flat_map_supply f supply (TAKE j bb.bb_instructions) = (prej,sj) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  revert_forward_pair bb i j ==>
  revert_forward_pair bb' (LENGTH pre) (LENGTH prej)
Proof
  strip_tac >>
  `mm_flat_map_supply f supply bb.bb_instructions = (bb'.bb_instructions,supply')` by
    (qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
     simp[transform_block_memzero_supply_def] >> gvs[] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `!x es. MEM x bb.bb_instructions /\
    x.inst_opcode IN {ASSIGN; RETURNDATACOPY; REVERT} ==>
    f es x = ([x],es)` by
    (rpt strip_tac >>
     qpat_assum `f = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule mm_local_memzero_nonselected_unchanged >>
     conj_tac >- first_assum ACCEPT_TAC >>
     gvs[is_zero_store_def, is_calldatasize_copy_def,
       pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  `!n pre sn p q.
    (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
    mm_flat_map_supply f supply (TAKE n bb.bb_instructions) = (pre,sn) /\
    same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) p q ==>
    same_after_assigns (REVERSE pre) p q` by
    (rpt strip_tac >> drule_all mm_local_zero_same_after_assigns_prefix >> simp[]) >>
  drule_all mm_local_revert_forward_transport >> simp[]
QED

Theorem mm_local_zero_in_revert_forward_transport[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  index < LENGTH fn.fn_blocks /\ bb = EL index fn.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  f = apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) /\
  EVERY (\i. inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) bb.bb_instructions /\
  (!v. v IN P ==> MEM v supply.irs_used_vars) /\
  mm_flat_map_supply f supply (TAKE n bb.bb_instructions) = (pre,sn) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  s.vs_current_bb = bb.bb_label /\ s.vs_inst_idx = n /\
  t.vs_current_bb = bb.bb_label /\ t.vs_inst_idx = LENGTH pre /\
  in_revert_forward fn s ==>
  in_revert_forward (fn with fn_blocks := LUPDATE bb' index fn.fn_blocks) t
Proof
  strip_tac >>
  `mm_flat_map_supply f supply bb.bb_instructions = (bb'.bb_instructions,supply')` by
    (qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
     simp[transform_block_memzero_supply_def] >> gvs[] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `!x es. MEM x bb.bb_instructions /\
    x.inst_opcode IN {ASSIGN; RETURNDATACOPY; REVERT} ==>
    f es x = ([x],es)` by
    (rpt strip_tac >>
     qpat_assum `f = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule mm_local_memzero_nonselected_unchanged >>
     conj_tac >- first_assum ACCEPT_TAC >>
     gvs[is_zero_store_def, is_calldatasize_copy_def,
       pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  `!n pre sn p q.
    (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
    mm_flat_map_supply f supply (TAKE n bb.bb_instructions) = (pre,sn) /\
    same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) p q ==>
    same_after_assigns (REVERSE pre) p q` by
    (rpt strip_tac >> drule_all mm_local_zero_same_after_assigns_prefix >> simp[]) >>
  `bb'.bb_label = bb.bb_label` by
    metis_tac[mmSupplyWfProofsTheory.transform_block_memzero_supply_label] >>
  drule_all mm_local_in_revert_forward_transport >> simp[]
QED

Theorem mm_local_mode_no_output_recognition[local]:
  i.inst_outputs = [] /\
  apply_groups_inst_supply mode ns rm s i = (out,s') /\
  (!v. p = Var v ==> MEM v s.irs_used_vars) /\
  (!v. q = Var v ==> MEM v s.irs_used_vars) ==>
  same_after_assigns (REVERSE out ++ xs) p q = same_after_assigns xs p q
Proof
  strip_tac >> Cases_on `p = q`
  >- simp[contextCodegenRelPropsTheory.same_after_assigns_refl] >>
  Cases_on `fresh_ir_var (SND (fresh_inst_id s))` >>
  drule (cj 1 irSupplyTheory.fresh_ir_var_contract) >> strip_tac >>
  gvs[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def, irSupplyTheory.fresh_inst_id_def] >>
  Cases_on `p` >> Cases_on `q` >>
  gvs[contextCodegenRelTheory.same_after_assigns_def,
      contextCodegenRelTheory.step_back_assign_def, mode_load_opcode_def,
      mode_copy_opcode_def] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem mm_local_mode_same_after_assigns_list[local]:
  !xs s out s' P p q.
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  f = apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) /\
  EVERY (\i. MEM i bb.bb_instructions /\ inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) xs /\
  (!v. v IN P ==> MEM v s.irs_used_vars) /\
  (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
  mm_flat_map_supply f s xs = (out,s') /\
  same_after_assigns (REVERSE xs) p q ==>
  same_after_assigns (REVERSE out) p q
Proof
  Induct using listTheory.SNOC_INDUCT
  >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `p = q`
  >- simp[contextCodegenRelPropsTheory.same_after_assigns_refl] >>
  fs[listTheory.SNOC_APPEND] >>
  Cases_on `mm_flat_map_supply f s xs` >>
  rename1 `mm_flat_map_supply f s xs = (pre,sm)` >>
  Cases_on `f sm x` >> rename1 `f sm x = (chunk,se)` >>
  `out = pre ++ chunk /\ s' = se` by
    (`mm_flat_map_supply f sm [x] = (chunk,se)` by simp[mm_flat_map_supply_def] >>
     drule_all mm_local_flat_map_supply_append >> simp[]) >>
  `!v. v IN P ==> MEM v sm.irs_used_vars` by
    (drule_at (Pat `mm_flat_map_supply _ _ _ = _`)
       (Q.ISPEC `venomInst$inst_uses` mm_local_list_old_vars) >>
     simp[] >> (impl_tac >- metis_tac[mm_local_mode_old_use]) >>
     strip_tac >> metis_tac[]) >>
  Cases_on `x.inst_outputs = []`
  >- (`same_after_assigns (REVERSE chunk ++ REVERSE pre) p q =
       same_after_assigns (REVERSE pre) p q` by
        (irule mm_local_mode_no_output_recognition >> metis_tac[]) >>
      `same_after_assigns (REVERSE xs) p q` by
        (Cases_on `p` >> Cases_on `q` >>
         gvs[REVERSE_APPEND, contextCodegenRelTheory.same_after_assigns_def,
             contextCodegenRelTheory.step_back_assign_def]) >>
      gvs[REVERSE_APPEND] >> first_x_assum irule >> metis_tac[]) >>
  `ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed) x.inst_id = NONE` by
    (Cases_on `ALOOKUP (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) x.inst_id` >> simp[] >>
     drule_all mm_local_prefix_rep_write >>
     disch_then (strip_assume_tac o REWRITE_RULE
       [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
     gvs[inst_wf_def]) >>
  Cases_on `MEM x.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode
    bb.bb_instructions (scan_block (dfg_build_function fn0) mode bb).ss_flushed)`
  >- (`x.inst_opcode <> ASSIGN` by
        (strip_tac >>
         `!r. f r x = ([x],r)` by
           (gvs[] >> irule mm_local_prefix_nonselected_unchanged >>
            simp[mode_copy_opcode_def, mode_load_opcode_def] >>
            Cases_on `mode` >> gvs[mode_copy_opcode_def, mode_load_opcode_def] >> metis_tac[]) >>
         `f sm x = ([mk_nop_from x],sm)` by
           (qpat_assum `f = _` (fn th => pure_once_rewrite_tac[th]) >>
            simp[apply_groups_inst_supply_def]) >>
         `mk_nop_from x = x` by metis_tac[pairTheory.PAIR_EQ, listTheory.CONS_11] >>
         pop_assum (mp_tac o AP_TERM ``\i:instruction. i.inst_opcode``) >>
         simp[mk_nop_from_def]) >>
      `chunk = [mk_nop_from x]` by gvs[apply_groups_inst_supply_def] >>
      `same_after_assigns (REVERSE xs) p q` by
        (Cases_on `p` >> Cases_on `q` >>
         gvs[REVERSE_APPEND, contextCodegenRelTheory.same_after_assigns_def,
             contextCodegenRelTheory.step_back_assign_def, AllCaseEqs()] >>
         BasicProvers.EVERY_CASE_TAC >> gvs[]) >>
      `same_after_assigns (REVERSE chunk ++ REVERSE pre) p q =
       same_after_assigns (REVERSE pre) p q` by
        (Cases_on `p` >> Cases_on `q` >>
         gvs[mk_nop_from_def, contextCodegenRelTheory.same_after_assigns_def,
           contextCodegenRelTheory.step_back_assign_def]) >>
      gvs[REVERSE_APPEND] >> first_x_assum irule >> metis_tac[]) >>
  `chunk = [x] /\ se = sm` by gvs[apply_groups_inst_supply_def] >>
  gvs[REVERSE_APPEND, contextCodegenRelTheory.same_after_assigns_def] >>
  Cases_on `step_back_assign x p` >- gvs[] >>
  Cases_on `step_back_assign x q` >- gvs[] >> gvs[] >>
  rename1 `step_back_assign x p = SOME p1` >>
  rename1 `step_back_assign x q = SOME q1` >>
  `(!v. p1 = Var v ==> v IN P) /\
   (!v. q1 = Var v ==> v IN P)` by
    (qpat_x_assum `!s out s' P p q. _` kall_tac >>
     metis_tac[contextCodegenRelPropsTheory.step_back_assign_preserves_vars]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem mm_local_mode_same_after_assigns_prefix[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  f = apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) /\
  EVERY (\i. inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) bb.bb_instructions /\
  (!v. v IN P ==> MEM v sk.irs_used_vars) /\
  (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
  mm_flat_map_supply f sk (TAKE n bb.bb_instructions) = (out,s') /\
  same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) p q ==>
  same_after_assigns (REVERSE out) p q
Proof
  strip_tac >>
  `EVERY (\i. MEM i bb.bb_instructions /\ inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P)
    (TAKE n bb.bb_instructions)` by
    (gvs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  drule_all mm_local_mode_same_after_assigns_list >> simp[]
QED

Theorem mm_local_mode_in_revert_forward_transport[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  index < LENGTH fn.fn_blocks /\ bb = EL index fn.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  f = apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) /\
  EVERY (\i. inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) bb.bb_instructions /\
  (!v. v IN P ==> MEM v sk.irs_used_vars) /\
  mm_flat_map_supply f sk (TAKE n bb.bb_instructions) = (pre,sn) /\
  mm_flat_map_supply f sk bb.bb_instructions = (bb'.bb_instructions,supply') /\
  bb'.bb_label = bb.bb_label /\
  s.vs_current_bb = bb.bb_label /\ s.vs_inst_idx = n /\
  t.vs_current_bb = bb.bb_label /\ t.vs_inst_idx = LENGTH pre /\
  in_revert_forward fn s ==>
  in_revert_forward (fn with fn_blocks := LUPDATE bb' index fn.fn_blocks) t
Proof
  strip_tac >>
  `!x es. MEM x bb.bb_instructions /\
    x.inst_opcode IN {ASSIGN; RETURNDATACOPY; REVERT} ==>
    f es x = ([x],es)` by
    (rpt strip_tac >>
     qpat_assum `f = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule mm_local_prefix_nonselected_unchanged >>
     Cases_on `mode` >>
     gvs[mode_copy_opcode_def,mode_load_opcode_def,
       pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] >>
     metis_tac[]) >>
  `!n pre sn p q.
    (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
    mm_flat_map_supply f sk (TAKE n bb.bb_instructions) = (pre,sn) /\
    same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) p q ==>
    same_after_assigns (REVERSE pre) p q` by
    (rpt strip_tac >> drule_all mm_local_mode_same_after_assigns_prefix >> simp[]) >>
  drule_all mm_local_in_revert_forward_transport >> simp[]
QED

Theorem mm_local_prefix_in_revert_forward:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  f = apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) /\
  transform_block_mode_supply (dfg_build_function fn0) mode sk bb = (bb',sk') /\
  mm_flat_map_supply f sk (TAKE n bb.bb_instructions) = (pre,sn) /\
  s.vs_current_bb = bb.bb_label /\ s.vs_inst_idx = n /\
  t.vs_current_bb = bb.bb_label /\ t.vs_inst_idx = LENGTH pre /\
  in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) s ==>
  in_revert_forward (fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks) t
Proof
  strip_tac >>
  `wf_function (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (irule mm_local_prefix_function_wf >> metis_tac[wf_ssa_def]) >>
  `fn_inst_wf (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (irule mm_local_prefix_inst_wf >> metis_tac[]) >>
  `ir_supply_covers_fn sk (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (irule mm_local_prefix_supply_covers >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by simp[MEM_LUPDATE] >>
  `EVERY (\i. inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> MEM v sk.irs_used_vars) bb.bb_instructions` by
    (gvs[fn_inst_wf_def,mm_local_supply_coverage,EVERY_MEM] >>
     rpt strip_tac >- metis_tac[] >>
     `mm_local_inst_covered sk i` by metis_tac[] >>
     gvs[mm_local_inst_covered_def,irSupplyTheory.inst_ir_vars_def,
       list_subset_def,EVERY_MEM,venomInstTheory.inst_uses_def,
       passSharedDefsTheory.MEM_operand_vars_eq_Var] >> metis_tac[]) >>
  `mm_flat_map_supply f sk bb.bb_instructions = (bb'.bb_instructions,sk') /\
    bb'.bb_label = bb.bb_label` by
    (qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
     simp[transform_block_mode_supply_def] >> gvs[] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `LUPDATE bb' index (LUPDATE bb index fn0.fn_blocks) =
    LUPDATE bb' index fn0.fn_blocks` by
    (irule LIST_EQ >> simp[EL_LUPDATE]) >>
  mp_tac (Q.INST [`fn` |-> `fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks`,
    `P` |-> `set sk.irs_used_vars`, `supply'` |-> `sk'`] mm_local_mode_in_revert_forward_transport) >>
  (impl_tac >- (simp[EL_LUPDATE] >> gvs[wf_function_def,venomInstTheory.fn_labels_def])) >>
  simp[]
QED

Theorem mm_local_representative_static_bounds[local]:
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
  g.cg_length = 0 \/
  (g.cg_dst + g.cg_length <= eom /\ g.cg_src + g.cg_length <= eom)
Proof
  strip_tac >> Cases_on `g.cg_length = 0` >- simp[] >> simp[] >>
  qabbrev_tac `due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r)` >>
  `mm_local_group_coverage is (LENGTH is)
    (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
      (mm_local_write_footprint (EL p is))) g` by
    (`MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
     drule_all (Q.INST [`cap` |-> `\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
      (mm_local_write_footprint (EL p is))`] mm_local_final_footprint_extent |> SRULE []) >> simp[]) >>
  `?j dj lj. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    mm_local_write_footprint (EL j is) = SOME (dj,lj) /\
    dj <= g.cg_dst + g.cg_length - 1 /\
    g.cg_dst + g.cg_length - 1 < dj + lj` by
    (qpat_x_assum `mm_local_group_coverage _ _ _ _` mp_tac >>
     pure_rewrite_tac[mm_local_group_coverage_def] >>
     disch_then (qspec_then `g.cg_dst + g.cg_length - 1` mp_tac) >>
     `g.cg_dst <= g.cg_dst + g.cg_length - 1 /\
       g.cg_dst + g.cg_length - 1 < g.cg_dst + g.cg_length` by decide_tac >>
     simp[] >> strip_tac >>
     rename1 `mm_local_write_footprint (EL j bb.bb_instructions) = SOME pair` >>
     PairCases_on `pair` >>
     qexists_tac `j` >> qexists_tac `pair0` >> qexists_tac `pair1` >>
     gvs[] >> decide_tac) >>
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
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by simp[listTheory.MEM_LUPDATE] >>
  `lookup_block bb.bb_label (LUPDATE bb index fn0.fn_blocks) = SOME bb` by
    (mp_tac (Q.SPECL [`fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks`, `bb`]
       venomExecProofsTheory.wf_lookup_block) >> simp[]) >>
  ` (H j).vs_inst_idx = j /\ (H j).vs_current_bb = bb.bb_label /\
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL j is) (H j) /\ ?u. step_inst fuel ctx (EL j is) (H j) = OK u` by metis_tac[] >>
  drule_all (Q.INST [`j` |-> `j`, `s0` |->
    `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is)`]
    mm_local_canonical_due_birth_geometry |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >> strip_tac >>
  `~in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) (H j)` by
    (simp[contextCodegenRelTheory.in_revert_forward_def] >> strip_tac >>
     `get_instruction bb j = SOME (EL j is)` by gvs[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
  Cases_on `(EL j is).inst_opcode = MCOPY`
  >- (qpat_x_assum `!q. h <= q /\ q <= r ==> _` kall_tac >>
      qpat_x_assum `static_mem_ok _ _ _ (EL j is) _` mp_tac >>
      simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
        EVERY_APPEND] >> strip_tac >>
      gvs[mm_local_write_footprint_def, contextCodegenRelTheory.source_memory_read_ranges_def,
        codegenRelTheory.source_memory_write_ranges_def,
        codegenRelTheory.sized_source_write_range_def, venomStateTheory.eval_operand_def] >>
      decide_tac) >>
  gvs[] >>
  rename1 `(EL j bb.bb_instructions).inst_operands = [Lit dstw; Var valuev]` >>
  drule mm_local_scan_lookup_origin >> simp[mode_load_opcode_def] >>
  disch_then (qx_choose_then `q` (qx_choose_then `w` strip_assume_tac)) >>
  `?l. l < j /\ l < LENGTH bb.bb_instructions /\ EL l bb.bb_instructions = q` by
    (qpat_x_assum `MEM q (TAKE j bb.bb_instructions)`
       (mp_tac o REWRITE_RULE [MEM_EL]) >>
     disch_then (qx_choose_then `l` strip_assume_tac) >>
     `l < j /\ l < LENGTH bb.bb_instructions` by
       (`j <= LENGTH bb.bb_instructions` by decide_tac >>
        fs[LENGTH_TAKE] >> decide_tac) >>
     qexists_tac `l` >> gvs[EL_TAKE]) >>
  `phi_prefix_length bb.bb_instructions <= l` by
    (CCONTR_TAC >> `l < phi_prefix_length bb.bb_instructions` by decide_tac >>
     qspec_then `bb.bb_instructions` (mp_tac o REWRITE_RULE [EVERY_EL])
       analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     disch_then (qspec_then `l` mp_tac) >>
     simp[LENGTH_TAKE,venomExecProofsTheory.phi_prefix_length_le,EL_TAKE] >> gvs[]) >>
  ` (H l).vs_inst_idx = l /\ (H l).vs_current_bb = bb.bb_label /\
    static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
      (EL l bb.bb_instructions) (H l)` by
    (qpat_assum `!q. phi_prefix_length bb.bb_instructions <= q /\ q <= r ==> _` (qspec_then `l` mp_tac) >> simp[] >>
     `l <= r` by decide_tac >> metis_tac[]) >>
  `~in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) (H l)` by
    (simp[contextCodegenRelTheory.in_revert_forward_def] >> strip_tac >>
     `get_instruction bb l = SOME q` by gvs[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
  `static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
    (EL j bb.bb_instructions) (H j)` by
    (qpat_assum `!q. phi_prefix_length bb.bb_instructions <= q /\ q <= _ ==> _`
       (qspec_then `j` mp_tac) >> simp[]) >>
  qpat_x_assum `!q. phi_prefix_length bb.bb_instructions <= q /\ q <= r ==> _` kall_tac >>
  qpat_x_assum `static_mem_ok _ _ _ (EL l _) _` mp_tac >>
  qpat_x_assum `static_mem_ok _ _ _ (EL j _) _` mp_tac >>
  simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    EVERY_APPEND] >> rpt strip_tac >>
  gvs[mm_local_write_footprint_def, contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def, venomStateTheory.eval_operand_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  asm_simp_tac (srw_ss()) [venomExecSemanticsTheory.step_inst_non_invoke] >>
  with_opcode_clause simp >>
  simp[venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operand_def] >>
  Cases_on `lookup_var valuev (H j)` >> simp[] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem mm_local_retained_static_if_forward[local]:
  mm_local_cut is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  static_mem_ok eom ctx fn i (H n) /\
  (in_revert_forward fn (H n) ==> in_revert_forward fn' t) ==>
  static_mem_ok eom ctx fn' i t
Proof
  strip_tac >>
  `inst_mem_ranges i (H n) = inst_mem_ranges i t` by
    (irule o1ContractCfgNormTheory.supply_inst_mem_ranges_cong >>
     gvs[mm_local_cut_def, mm_local_nonmemory_frame_def] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[venomStateTheory.eval_operand_def]) >>
  gvs[unitMemInvTheory.static_mem_ok_def] >> metis_tac[]
QED

Theorem mm_local_zero_retained_static_if_forward[local]:
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  static_mem_ok eom ctx fn i (H n) /\
  (in_revert_forward fn (H n) ==> in_revert_forward fn' t) ==>
  static_mem_ok eom ctx fn' i t
Proof
  strip_tac >>
  `inst_mem_ranges i (H n) = inst_mem_ranges i t` by
    (irule o1ContractCfgNormTheory.supply_inst_mem_ranges_cong >>
     gvs[mm_local_zero_cut_def, mm_local_nonmemory_frame_def] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[venomStateTheory.eval_operand_def]) >>
  gvs[unitMemInvTheory.static_mem_ok_def] >> metis_tac[]
QED

Definition mm_local_safe_exec_prefix_def:
  (mm_local_safe_exec_prefix P fuel ctx [] s t <=> t = s) /\
  (mm_local_safe_exec_prefix P fuel ctx (i::is) s t <=>
    P i s /\ ~is_terminator i.inst_opcode /\
    ?u. step_inst fuel ctx i s = OK u /\
      mm_local_safe_exec_prefix P fuel ctx is
        (u with vs_inst_idx := SUC s.vs_inst_idx) t)
End

Theorem mm_local_safe_exec_prefix_erase:
  !xs s t. mm_local_safe_exec_prefix P fuel ctx xs s t ==>
    mm_local_exec_prefix fuel ctx xs s t
Proof
  Induct_on `xs` >> simp[mm_local_safe_exec_prefix_def,
    mm_local_exec_prefix_def] >> metis_tac[]
QED

Theorem mm_local_safe_exec_prefix_append:
  !xs ys s t.
    mm_local_safe_exec_prefix P fuel ctx (xs ++ ys) s t <=>
    ?u. mm_local_safe_exec_prefix P fuel ctx xs s u /\
        mm_local_safe_exec_prefix P fuel ctx ys u t
Proof
  Induct_on `xs` >> simp[mm_local_safe_exec_prefix_def] >> metis_tac[]
QED

Theorem mm_local_safe_exec_prefix_universal:
  !xs s t. (!u. EVERY (\i. P i u) xs) /\
    mm_local_exec_prefix fuel ctx xs s t ==>
    mm_local_safe_exec_prefix P fuel ctx xs s t
Proof
  Induct_on `xs` >> simp[mm_local_safe_exec_prefix_def,
    mm_local_exec_prefix_def] >> metis_tac[]
QED

Theorem mm_local_exec_prefix_deterministic[local]:
  !xs s t u. mm_local_exec_prefix fuel ctx xs s t /\
    mm_local_exec_prefix fuel ctx xs s u ==> t = u
Proof
  Induct_on `xs` >> simp[mm_local_exec_prefix_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem mm_local_mem2mem_emission_safe[local]:
  apply_groups_inst_supply Mem2Mem ns rs es i = (chunk,es') /\
  (chunk = [i] ==> static_mem_ok eom ctx fn i t) /\
  (!g. ALOOKUP rs i.inst_id = SOME g ==>
    g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
    g.cg_length < dimword (:256) /\
    (g.cg_length = 0 \/
      (g.cg_dst + g.cg_length <= eom /\ g.cg_src + g.cg_length <= eom))) /\
  mm_local_exec_prefix fuel ctx chunk t t' ==>
  mm_local_safe_exec_prefix (static_mem_ok eom ctx fn) fuel ctx chunk t t'
Proof
  strip_tac >> Cases_on `chunk = [i]`
  >- gvs[mm_local_exec_prefix_def, mm_local_safe_exec_prefix_def] >>
  irule mm_local_safe_exec_prefix_universal >> simp[] >>
  qpat_x_assum `apply_groups_inst_supply _ _ _ _ _ = _` mp_tac >>
  simp[apply_groups_inst_supply_def] >>
  Cases_on `MEM i.inst_id ns`
  >- (simp[] >> strip_tac >> gvs[mk_nop_from_def] >>
      simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
        contextCodegenRelTheory.source_memory_read_ranges_def,
        codegenRelTheory.source_memory_write_ranges_def]) >>
  Cases_on `ALOOKUP rs i.inst_id` >> simp[] >>
  rename1 `ALOOKUP rs i.inst_id = SOME g` >>
  qpat_x_assum `!g'. SOME g = SOME g' ==> _`
    (qspec_then `g` mp_tac) >> asm_rewrite_tac[] >>
  disch_then assume_tac >>
  `g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
    g.cg_length < dimword (:256)` by metis_tac[] >>
  Cases_on `g.cg_length = 32` >> simp[]
  >- (Cases_on `i.inst_opcode = MSTORE` >> simp[] >>
      Cases_on `fresh_inst_id es` >> rename1 `fresh_inst_id es = (lid,es1)` >>
      Cases_on `fresh_ir_var es1` >> rename1 `fresh_ir_var es1 = (v,es2)` >>
      simp[] >> strip_tac >> gvs[] >> qx_gen_tac `st` >>
      simp[mk_load_inst_def, mk_mstore_from_load_def, mode_load_opcode_def,
        unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
        contextCodegenRelTheory.source_memory_read_ranges_def,
        codegenRelTheory.source_memory_write_ranges_def,
        codegenRelTheory.fixed_source_write_range_def,
        venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w, arithmeticTheory.ADD_COMM] >>
      Cases_on `lookup_var v st` >> gvs[]) >>
  strip_tac >> gvs[] >>
  simp[mk_bulk_copy_inst_def, mode_copy_opcode_def,
    unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.sized_source_write_range_def,
    venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w, arithmeticTheory.ADD_COMM]
QED

Theorem mm_local_mem2mem_safe_prefix_if_forward[local]:
  !n fn0 supply index k bb sk is gs ns rs deleted excluded h H fuel ctx eom pre esh out esn t0 fn'.
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
  (!q pref sq tq. h <= q /\ q < n /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE q is) = (pref,sq) /\
    mm_local_cut is gs H q excluded (LENGTH pref) tq ==>
    in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) (H q) ==>
    in_revert_forward fn' tq) /\
  eom < dimword (:256) /\
  state_equiv excluded (H h with vs_inst_idx := LENGTH pre) t0 /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE h is) = (pre,esh) /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
    (TAKE (n-h) (DROP h is)) = (out,esn) ==>
  ?t. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t0 t /\
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
      simp[mm_local_safe_exec_prefix_def, irSupplyFreshPropsTheory.ir_supply_extends_refl] >>
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
  `!q pref sq tq. h <= q /\ q < r /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE q is) = (pref,sq) /\
    mm_local_cut is gs H q excluded (LENGTH pref) tq ==>
    in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) (H q) ==>
    in_revert_forward fn' tq` by
    (rpt gen_tac >> strip_tac >> strip_tac >>
     `q < SUC r` by decide_tac >>
     qpat_assum `!q pref sq tq. h <= q /\ q < SUC r /\ _ ==> _`
       (qspecl_then [`q:num`,`pref:instruction list`,`sq:ir_supply`,`tq:venom_state`] irule) >>
     qexistsl [`pref`,`q`,`sq`] >> gvs[]) >>
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
  `?fin. mm_local_exec_prefix fuel ctx out t0 fin /\
    mm_local_cut is gs H (SUC r) excluded (LENGTH pre + LENGTH out) fin /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE (SUC r) is) =
      (pre ++ out,esn) /\
    ir_supply_extends sk esh /\ ir_supply_extends esh esn /\
    fin.vs_inst_idx = LENGTH pre + LENGTH out` by
    (drule_all (Q.SPEC `SUC r` mm_local_mem2mem_prefix_execution) >> simp[]) >>
  `mm_local_exec_prefix fuel ctx front t0 t` by
    metis_tac[mm_local_safe_exec_prefix_erase] >>
  `mm_local_exec_prefix fuel ctx frag t fin` by
    (qpat_x_assum `mm_local_exec_prefix _ _ out _ _` mp_tac >>
     asm_rewrite_tac[mm_local_exec_prefix_append] >>
     metis_tac[mm_local_exec_prefix_deterministic]) >>
  `(frag = [EL r is] ==> static_mem_ok eom ctx fn' (EL r is) t)` by
    (strip_tac >>
     `apply_groups_inst_supply Mem2Mem ns rs es (EL r is) = ([EL r is],es')` by metis_tac[] >>
     `!v. MEM (Var v) (EL r is).inst_operands ==> v NOTIN excluded` by
       (rpt strip_tac >>
        `MEM (EL r is) bb.bb_instructions` by metis_tac[EL_MEM] >>
        `MEM v (venomInst$inst_uses (EL r is))` by
          gvs[venomInstTheory.inst_uses_def,passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
        `ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
          (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
         rs = rep_map_of_groups bb.bb_instructions
          (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
        qpat_x_assum `is = _` SUBST_ALL_TAC >>
        drule_all mm_local_retained_operand_protected >> simp[]) >>
     `static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
       (EL r is) (H r)` by metis_tac[prim_recTheory.LESS_SUC_REFL] >>
     `(in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) (H r) ==>
       in_revert_forward fn' t)` by
       (strip_tac >>
        qpat_x_assum `!q pref sq tq. h <= q /\ q < SUC r /\ _ ==> _`
          (qspecl_then [`r:num`,`pre ++ front:instruction list`,`es:ir_supply`,`t:venom_state`] mp_tac) >>
        gvs[arithmeticTheory.ADD_COMM]) >>
     drule_all mm_local_retained_static_if_forward >> simp[]) >>
  `!g. ALOOKUP rs (EL r is).inst_id = SOME g ==>
    g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
    g.cg_length < dimword (:256) /\
    (g.cg_length = 0 \/
      (g.cg_dst + g.cg_length <= eom /\ g.cg_src + g.cg_length <= eom))` by
    (qx_gen_tac `g` >> strip_tac >>
     `MEM g gs /\ rep_of_group is g = SOME ((EL r is).inst_id,g)` by
       (drule alistTheory.ALOOKUP_MEM >>
        pure_asm_rewrite_tac[rep_map_of_groups_def,MEM_MAP,MEM_FILTER] >>
        strip_tac >> rename1 `IS_SOME opt` >> Cases_on `opt` >> fs[] >>
        gvs[rep_of_group_def,AllCaseEqs()] >> metis_tac[]) >>
     `!q. h <= q /\ q <= r ==> (H q).vs_inst_idx = q /\
       (H q).vs_current_bb = bb.bb_label /\
       static_mem_ok eom ctx (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
         (EL q is) (H q) /\
       ?u. step_inst fuel ctx (EL q is) (H q) = OK u` by
       (rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_IFF_LESS_SUC]) >>
     `g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
       g.cg_length < dimword (:256)` by
       (drule_all mm_local_representative_finite_bounds >> simp[]) >>
     simp[] >> drule_all mm_local_representative_static_bounds >> simp[]) >>
  `mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx frag t fin` by
    (drule_all mm_local_mem2mem_emission_safe >> simp[]) >>
  qexists `fin` >> simp[] >>
  qpat_assum `out = _` (fn th => pure_once_rewrite_tac[th]) >>
  metis_tac[mm_local_safe_exec_prefix_append]
QED

Theorem mm_local_mem2mem_safe_prefix_execution[local]:
  !n fn0 supply index k bb sk is gs ns rs deleted excluded h H fuel ctx eom pre esh out esn t0 fn' bb' sk'.
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
  transform_block_mode_supply (dfg_build_function fn0) Mem2Mem sk bb = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  eom < dimword (:256) /\
  state_equiv excluded (H h with vs_inst_idx := LENGTH pre) t0 /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE h is) = (pre,esh) /\
  mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) esh
    (TAKE (n-h) (DROP h is)) = (out,esn) ==>
  ?t. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t0 t /\
    mm_local_cut is gs H n excluded (LENGTH pre + LENGTH out) t /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE n is) =
      (pre ++ out,esn) /\
    ir_supply_extends sk esh /\ ir_supply_extends esh esn /\
    t.vs_inst_idx = LENGTH pre + LENGTH out
Proof
  rpt gen_tac >> strip_tac >>
  `!q pref sq tq. h <= q /\ q < n /\
    mm_flat_map_supply (apply_groups_inst_supply Mem2Mem ns rs) sk (TAKE q is) = (pref,sq) /\
    mm_local_cut is gs H q excluded (LENGTH pref) tq ==>
    in_revert_forward (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks) (H q) ==>
    in_revert_forward fn' tq` by
    (rpt gen_tac >> strip_tac >> strip_tac >>
     `(H q).vs_current_bb = bb.bb_label /\ (H q).vs_inst_idx = q` by metis_tac[] >>
     `tq.vs_current_bb = bb.bb_label /\ tq.vs_inst_idx = LENGTH pref` by
       (qpat_assum `mm_local_cut _ _ _ _ _ _ tq` mp_tac >>
        simp[NoAsms,mm_local_cut_def,mm_local_nonmemory_frame_def,
          stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality] >>
        strip_tac >> gvs[] >> metis_tac[]) >>
     qpat_x_assum `fn' = _` SUBST_ALL_TAC >>
     mp_tac (Q.INST [`f` |-> `apply_groups_inst_supply Mem2Mem ns rs`,
       `mode` |-> `Mem2Mem`, `n` |-> `q:num`, `pre` |-> `pref:instruction list`,
       `sn` |-> `sq:ir_supply`, `s` |-> `H (q:num)`, `t` |-> `tq:venom_state`]
       mm_local_prefix_in_revert_forward) >>
     (impl_tac >- gvs[]) >> simp[]) >>
  drule_all mm_local_mem2mem_safe_prefix_if_forward >> simp[]
QED

Theorem mm_local_safe_exec_prefix_trace[local]:
  !xs s t tail.
  reachability_closed Inv ctx /\
  mm_local_safe_exec_prefix (P fn) fuel ctx xs s t /\
  DROP s.vs_inst_idx bb.bb_instructions = xs ++ tail /\
  EVERY (\((p,d',id),f,i,u). p = [] ==> P f i u)
    (trace_block [] d fuel ctx fn bb t) ==>
  EVERY (\((p,d',id),f,i,u). p = [] ==> P f i u)
    (trace_block [] d fuel ctx fn bb s)
Proof
  Induct_on `xs` >- simp[mm_local_safe_exec_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[mm_local_safe_exec_prefix_def] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (`s.vs_inst_idx < LENGTH bb.bb_instructions` by
       (qpat_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
        simp[LENGTH_DROP] >> decide_tac) >>
     simp[venomInstTheory.get_instruction_def] >>
     qpat_assum `DROP _ _ = _` (mp_tac o AP_TERM ``EL 0:instruction list -> instruction``) >>
     simp[EL_DROP]) >>
  drule_all venomExecutionReplayPropsTheory.trace_visit_root_every >>
  disch_then (fn th => rewrite_tac[th]) >> simp[] >>
  first_x_assum irule >> reverse conj_tac >- metis_tac[] >>
  qexists `tail` >> simp[] >>
  qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``DROP 1:instruction list -> instruction list``) >>
  simp[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD1, arithmeticTheory.ADD_COMM]
QED

Theorem mm_local_zero_actual_safe_transition_if_forward[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ ~is_terminator (EL n is).inst_opcode /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n /\
  (!dst v len. is_calldatasize_copy dfg (EL n is) /\
    (EL n is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H n) = SOME (n2w (LENGTH (H n).vs_call_ctx.cc_calldata)) /\
    LENGTH (H n).vs_call_ctx.cc_calldata < dimword (:256)) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j d bs. mm_local_zero_capture dfg is (SUC n) j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u) /\
  eom < dimword (:256) /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  static_mem_ok eom ctx fn (EL n is) (H n) /\
  (in_revert_forward fn (H n) ==> in_revert_forward fn' t) /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is) = (chunk,es') ==>
  ?t'. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx chunk t t' /\
    mm_local_zero_cut dfg is gs H (SUC n) excluded (pc + LENGTH chunk) t'
Proof
  strip_tac >>
  Cases_on `is_zero_store (EL n is) \/ is_calldatasize_copy dfg (EL n is)`
  >- (drule_all mm_local_zero_selected_transition >> strip_tac >>
      qexists `t'` >> simp[] >>
      irule mm_local_safe_exec_prefix_universal >> simp[]) >>
  `apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) es (EL n is) = ([EL n is],es)` by
    (qpat_x_assum `apply_memzero_inst_supply _ _ _ _ = _` kall_tac >>
     gvs[] >> irule mm_local_memzero_nonselected_unchanged >> simp[EL_MEM]) >>
  `chunk = [EL n is]` by metis_tac[pairTheory.PAIR_EQ] >>
  `static_mem_ok eom ctx fn' (EL n is) t` by
    (irule mm_local_zero_retained_static_if_forward >> metis_tac[]) >>
  drule_all mm_local_zero_actual_transition >> strip_tac >>
  qexists `t'` >> simp[] >>
  gvs[mm_local_safe_exec_prefix_def, mm_local_exec_prefix_def]
QED

Theorem mm_local_zero_actual_safe_interval_if_forward[local]:
  !m n es t pc out es' pre.
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  transform_block_memzero_supply dfg supply bb = (bb',sk') /\
  h = phi_prefix_length is /\ h <= n /\ n + m <= LENGTH is /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ eom < dimword (:256) /\
  (!j. h <= j /\ j < n + m ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ~is_terminator (EL j is).inst_opcode /\
    (!v. MEM (Var v) (EL j is).inst_operands ==> v NOTIN excluded) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
      H (SUC j) = u with vs_inst_idx := SUC j) /\
  (!j dst v len. h <= j /\ j < n + m /\
    is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  (!j. n <= j /\ j <= n + m ==>
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  (!j pref sj tj. h <= j /\ j < n + m /\
    mm_flat_map_supply f supply (TAKE j is) = (pref,sj) /\
    mm_local_zero_cut dfg is gs H j excluded (LENGTH pref) tj ==>
    in_revert_forward fn (H j) ==> in_revert_forward fn' tj) /\
  mm_flat_map_supply f supply (TAKE n is) = (pre,es) /\ pc = LENGTH pre /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  mm_flat_map_supply f es (TAKE m (DROP n is)) = (out,es') ==>
  ?t'. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t t' /\
    mm_local_zero_cut dfg is gs H (n + m) excluded (pc + LENGTH out) t'
Proof
  Induct_on `m`
  >- (simp[mm_flat_map_supply_def, mm_local_safe_exec_prefix_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `n < LENGTH is` by decide_tac >>
  `TAKE (SUC m) (DROP n is) = EL n is :: TAKE m (DROP (SUC n) is)` by
    simp[rich_listTheory.DROP_CONS_EL] >>
  Cases_on `f es (EL n is)` >> rename1 `f es (EL n is) = (chunk,es1)` >>
  Cases_on `mm_flat_map_supply f es1 (TAKE m (DROP (SUC n) is))` >>
  rename1 `mm_flat_map_supply f es1 _ = (tail,es2)` >>
  `out = chunk ++ tail /\ es' = es2` by gvs[mm_flat_map_supply_def] >>
  `?u. step_inst fuel ctx (EL n is) (H n) = OK u /\
    H (SUC n) = u with vs_inst_idx := SUC n` by
    (qpat_x_assum `!j. h <= j /\ j < n + SUC m ==> _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `(H n).vs_current_bb = bb.bb_label /\ (H n).vs_inst_idx = n /\
    static_mem_ok eom ctx fn (EL n is) (H n) /\
    ~is_terminator (EL n is).inst_opcode /\
    (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded)` by
    (qpat_x_assum `!j. h <= j /\ j < n + SUC m ==> _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_x_assum `!n es t pc out es' pre. _` kall_tac >>
     `LENGTH (H n).vs_call_ctx.cc_calldata < dimword (:256)` by
       (qpat_x_assum `!j. n <= j /\ j <= n + SUC m ==> _`
          (qspec_then `n` mp_tac) >> simp[]) >>
     qpat_assum `mm_local_zero_cut _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, mm_local_zero_cut_def, mm_local_nonmemory_frame_def] >>
     strip_tac >> fs[]) >>
  `!j d bs. mm_local_zero_capture dfg is (SUC n) j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u` by
    (rpt strip_tac >>
     `h <= j /\ j < n + SUC m` by
       (drule mm_local_zero_capture_cases >>
        drule mm_local_zero_capture_after_phis >> gvs[] >> decide_tac) >>
     metis_tac[]) >>
  `!dst v len. is_calldatasize_copy dfg (EL n is) /\
    (EL n is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H n) = SOME (n2w (LENGTH (H n).vs_call_ctx.cc_calldata)) /\
    LENGTH (H n).vs_call_ctx.cc_calldata < dimword (:256)` by
    (rpt strip_tac >>
     qpat_x_assum `!j dst v len. _` (qspec_then `n` mp_tac) >> simp[]) >>
  `(in_revert_forward fn (H n) ==> in_revert_forward fn' t)` by
    (qpat_x_assum `pc = LENGTH pre` SUBST_ALL_TAC >>
     qpat_x_assum `!j pref sj tj. _`
       (qspecl_then [`n`,`pre`,`es`,`t`] mp_tac) >> simp[]) >>
  `?t1. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx chunk t t1 /\
    mm_local_zero_cut dfg is gs H (SUC n) excluded (pc + LENGTH chunk) t1` by
    (qpat_x_assum `f = _` SUBST_ALL_TAC >>
     drule_all mm_local_zero_actual_safe_transition_if_forward >> simp[]) >>
  `!v. v NOTIN excluded ==> MEM v es1.irs_used_vars` by
    (gvs[] >> drule_at (Pat `apply_memzero_inst_supply _ _ _ _ = _`)
       mm_local_memzero_old_use >> strip_tac >> metis_tac[]) >>
  `mm_flat_map_supply f supply (TAKE (SUC n) is) = (pre ++ chunk,es1)` by
    (qpat_x_assum `!n es t pc out es' pre. _` kall_tac >>
     `TAKE (SUC n) is = TAKE n is ++ [EL n is]` by
       simp[rich_listTheory.TAKE_SUC_BY_TAKE, listTheory.SNOC_APPEND] >>
     `mm_flat_map_supply f es [EL n is] = (chunk,es1)` by
       simp[mm_flat_map_supply_def] >>
     qpat_x_assum `TAKE (SUC n) is = _` (fn th => once_rewrite_tac[th]) >>
     irule mm_local_flat_map_supply_append >> qexists `es` >> simp[]) >>
  qpat_x_assum `!n es t pc out es' pre. _`
    (qspecl_then [`SUC n`,`es1`,`t1`,`pc + LENGTH chunk`,`tail`,`es2`,
       `pre ++ chunk`] mp_tac) >>
  (impl_tac >- (gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >>
    rpt strip_tac >> metis_tac[])) >>
  strip_tac >> qexists `t'` >> conj_tac
  >- (asm_rewrite_tac[] >> rewrite_tac[mm_local_safe_exec_prefix_append] >>
      qexists `t1` >> simp[]) >>
  `n + SUC m = SUC n + m` by decide_tac >>
  `pc + LENGTH out = pc + LENGTH chunk + LENGTH tail` by simp[] >>
  metis_tac[]
QED

Theorem mm_local_zero_retained_static[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  index < LENGTH fn.fn_blocks /\ bb = EL index fn.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  EVERY (\i. inst_wf i /\
    !v. MEM (Var v) i.inst_operands ==> v IN P) is /\
  (!v. v IN P ==> MEM v supply.irs_used_vars) /\
  mm_flat_map_supply f supply (TAKE n is) = (pre,sn) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  fn' = fn with fn_blocks := LUPDATE bb' index fn.fn_blocks /\
  (H n).vs_current_bb = bb.bb_label /\ (H n).vs_inst_idx = n /\
  mm_local_zero_cut dfg is gs H n excluded (LENGTH pre) t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  static_mem_ok eom ctx fn i (H n) ==>
  static_mem_ok eom ctx fn' i t
Proof
  strip_tac >> irule mm_local_zero_retained_static_if_forward >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `mm_local_zero_cut _ _ _ _ _ _ _ _`)) >> simp[] >>
  `t.vs_current_bb = bb.bb_label /\ t.vs_inst_idx = LENGTH pre` by
    (qpat_assum `mm_local_zero_cut _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, mm_local_zero_cut_def, mm_local_nonmemory_frame_def] >>
     metis_tac[]) >>
  strip_tac >> gvs[] >> irule mm_local_zero_in_revert_forward_transport >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem mm_local_zero_actual_safe_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  transform_block_memzero_supply dfg supply bb = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  h = phi_prefix_length is /\ h <= n /\ n + m <= LENGTH is /\
  lookup_block bb.bb_label fn0.fn_blocks = SOME bb /\ eom < dimword (:256) /\
  (!j. h <= j /\ j < n + m ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn0 (EL j is) (H j) /\
    ~is_terminator (EL j is).inst_opcode /\
    (!v. MEM (Var v) (EL j is).inst_operands ==> v NOTIN excluded) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
      H (SUC j) = u with vs_inst_idx := SUC j) /\
  (!j dst v len. h <= j /\ j < n + m /\
    is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  (!j. n <= j /\ j <= n + m ==>
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  mm_flat_map_supply f supply (TAKE n is) = (pre,es) /\ pc = LENGTH pre /\
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  mm_flat_map_supply f es (TAKE m (DROP n is)) = (out,es') ==>
  ?t'. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t t' /\
    mm_local_zero_cut dfg is gs H (n + m) excluded (pc + LENGTH out) t'
Proof
  strip_tac >> irule mm_local_zero_actual_safe_interval_if_forward >>
  goal_assum (drule_at (Pat `mm_local_zero_cut _ _ _ _ _ _ _ _`)) >>
  rpt (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `wf_ssa _`)) >>
  goal_assum (drule_at (Pat `transform_block_memzero_supply _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mm_flat_map_supply _ _ (TAKE _ _) = _`)) >>
  simp[] >> qexistsl [`fn0`,`index`] >> simp[] >>
  reverse conj_tac >- (gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `!j. h <= j /\ j < n + m ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j` by metis_tac[] >>
  `tj.vs_current_bb = bb.bb_label /\ tj.vs_inst_idx = LENGTH pref` by
    (qpat_assum `mm_local_zero_cut _ _ _ _ _ _ _ tj` mp_tac >>
     simp[NoAsms, mm_local_zero_cut_def, mm_local_nonmemory_frame_def] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >> gvs[] >> irule mm_local_zero_in_revert_forward_transport >>
  (conj_tac >- gvs[wf_function_def, venomInstTheory.fn_labels_def]) >> (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `transform_block_memzero_supply _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mm_flat_map_supply _ _ _ = _`)) >>
  simp[] >> qexistsl [`set supply.irs_used_vars`,`H j`] >> simp[] >>
  simp[EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >> conj_tac
  >- (gvs[fn_inst_wf_compute, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  rpt strip_tac >>
  `MEM (EL index fn0.fn_blocks) fn0.fn_blocks` by simp[EL_MEM] >>
  gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_vars_def,
      irSupplyTheory.block_ir_vars_def, irSupplyTheory.inst_ir_vars_def,
      list_subset_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  qpat_x_assum `!x. (?l. _) ==> MEM x supply.irs_used_vars` irule >>
  qexists `FLAT (MAP inst_ir_vars (EL index fn0.fn_blocks).bb_instructions)` >>
  conj_tac >- (qexists `EL index fn0.fn_blocks` >> simp[]) >>
  simp[MEM_FLAT, MEM_MAP] >> qexists `inst_ir_vars i` >> conj_tac
  >- (qexists `i` >> simp[]) >>
  simp[irSupplyTheory.inst_ir_vars_def, venomInstTheory.inst_uses_def] >>
  metis_tac[passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

Theorem mm_local_zero_noninvoke_stop[local]:
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  ~(?err. step_inst fuel ctx i (H n) = Error err) /\
  ~(?u. step_inst fuel ctx i (H n) = OK u) ==>
  lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx i (H n)) (step_inst fuel ctx i t)
Proof
  strip_tac >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    gvs[mm_local_zero_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
      stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
      venomStateTheory.venom_state_component_equality] >>
  Cases_on `step_inst fuel ctx i (H n)` >> gvs[lift_result_def]
  >- (drule opcodeClassTheory.step_inst_halt_opcodes >> strip_tac >>
      gvs[venomInstTheory.is_terminator_def])
  >- (drule_all venomExecutionReplayPropsTheory.state_noninvoke_abort >>
      strip_tac >> simp[lift_result_def])
  >- (gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
      drule opcodeClassTheory.step_inst_base_intret_opcodes >> strip_tac >>
      gvs[venomInstTheory.is_terminator_def])
QED

Theorem mm_local_zero_terminator_result[local]:
  mm_local_zero_cut dfg is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  is_terminator i.inst_opcode ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [i] (H n)) (dft_exec_suffix fuel ctx [i] t)
Proof
  strip_tac >> irule venomExecutionReplayPropsTheory.state_terminator_result >>
  metis_tac[mm_local_zero_cut_empty]
QED

Theorem mm_local_zero_nonterminator_stop[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  ~is_terminator (EL n is).inst_opcode /\
  ~(?err. step_inst fuel ctx (EL n is) (H n) = Error err) /\
  ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u) ==>
  lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx (EL n is) (H n)) (step_inst fuel ctx (EL n is) t)
Proof
  strip_tac >> Cases_on `(EL n is).inst_opcode = INVOKE`
  >- (`is_volatile_memory (EL n is) /\ ~is_zero_store (EL n is) /\
       ~is_calldatasize_copy dfg (EL n is)` by
        simp[is_volatile_memory_def, is_zero_store_def, is_calldatasize_copy_def,
          venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
          venomEffectsTheory.all_effects_def] >>
      `mm_local_pending_indices is gs n = []` by
        (irule mm_local_zero_barrier_pending_empty >>
         qexistsl [`bb`,`dfg`,`n`] >> gvs[]) >>
      irule venomExecutionReplayPropsTheory.state_non_ok >> metis_tac[mm_local_zero_cut_empty]) >>
  irule mm_local_zero_noninvoke_stop >> metis_tac[]
QED

Theorem mm_local_zero_terminal_pending_empty[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ SUC n = LENGTH is /\
  is_terminator (EL n is).inst_opcode ==>
  mm_local_pending_indices is gs n = []
Proof
  strip_tac >>
  `~is_zero_store (EL n is) /\ ~is_calldatasize_copy dfg (EL n is)` by
    (Cases_on `(EL n is).inst_opcode` >>
     gvs[venomInstTheory.is_terminator_def, is_zero_store_def,
       is_calldatasize_copy_def]) >>
  `!j. ~MEM j (mm_local_pending_indices is gs n)` suffices_by
    (Cases_on `mm_local_pending_indices is gs n` >> simp[] >> metis_tac[]) >>
  qx_gen_tac `j` >> rewrite_tac[mm_local_pending_indices_mem] >> strip_tac >>
  `r = n` by decide_tac >> gvs[] >>
  `MEM (EL n bb.bb_instructions) bb.bb_instructions` by
    (irule EL_MEM >> decide_tac) >>
  drule mm_local_rep_member >> strip_tac >>
  drule_all mm_local_memzero_group_roles >> strip_tac >>
  `i = EL n bb.bb_instructions` by
    metis_tac[mmWfProofsTheory.all_distinct_map_inv, EL_MEM] >>
  metis_tac[]
QED

Theorem mm_local_zero_stopping_cut[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  h = phi_prefix_length is /\ h <= n /\ n < LENGTH is /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ eom < dimword (:256) /\
  (!j. h <= j /\ j <= n ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    (!v. MEM (Var v) (EL j is).inst_operands ==> v NOTIN excluded)) /\
  (!j. h <= j /\ j < n ==>
    ~is_terminator (EL j is).inst_opcode /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
      H (SUC j) = u with vs_inst_idx := SUC j) /\
  (!j dst v len. h <= j /\ j < n /\
    is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  (!j. h <= j /\ j <= n ==>
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  (is_terminator (EL n is).inst_opcode \/
    ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
  state_equiv excluded (H h with vs_inst_idx := LENGTH pre) t0 /\
  (!v. v NOTIN excluded ==> MEM v esh.irs_used_vars) /\
  mm_flat_map_supply
    (apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
      (rep_map_of_groups is gs)) supply (TAKE h is) = (pre,esh) /\
  mm_flat_map_supply
    (apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
      (rep_map_of_groups is gs)) esh (TAKE (n-h) (DROP h is)) = (out,esn) ==>
  ?t. mm_local_exec_prefix fuel ctx out t0 t /\
    mm_local_zero_cut dfg is gs H n excluded (LENGTH pre + LENGTH out) t /\
    mm_flat_map_supply
      (apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
        (rep_map_of_groups is gs)) supply (TAKE n is) = (pre ++ out,esn) /\
    t.vs_inst_idx = LENGTH pre + LENGTH out
Proof
  strip_tac >>
  `mm_local_zero_cut dfg is gs H h excluded (LENGTH pre) t0` by
    metis_tac[mm_local_zero_cut_post_phi_init] >>
  `h + (n-h) = n` by decide_tac >>
  `?t. mm_local_exec_prefix fuel ctx out t0 t /\
    mm_local_zero_cut dfg is gs H n excluded (LENGTH pre + LENGTH out) t` by
    (mp_tac (Q.SPECL [`n-h`,`h`,`esh`,`t0`,`LENGTH (pre:instruction list)`,`out`,`esn`]
      mm_local_zero_actual_interval) >>
     (impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ])) >>
     simp[]) >>
  `TAKE h is ++ TAKE (n-h) (DROP h is) = TAKE n is` by
    metis_tac[listTheory.TAKE_SUM] >>
  `mm_flat_map_supply
    (apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
      (rep_map_of_groups is gs)) supply (TAKE n is) = (pre ++ out,esn)` by
    (drule_all mm_local_flat_map_supply_append >> simp[]) >>
  qexists `t` >> fs[mm_local_zero_cut_def]
QED

Theorem mm_local_emitted_stopping_result:
  n < LENGTH is /\ t0.vs_inst_idx = LENGTH pre /\
  mm_flat_map_supply f supply (TAKE n is) = (pre ++ out,esn) /\
  (!es. f es (EL n is) = ([EL n is],es)) /\
  mm_flat_map_supply f supply is = (bb'.bb_instructions,fin) /\
  mm_local_exec_prefix fuel ctx out t0 t /\
  ~(?err. dft_exec_suffix fuel ctx [EL n is] s = Error err) /\
  (is_terminator (EL n is).inst_opcode \/
    ~(?u. step_inst fuel ctx (EL n is) s = OK u)) /\
  lift_result rok rhalt rabort
    (dft_exec_suffix fuel ctx [EL n is] s)
    (dft_exec_suffix fuel ctx [EL n is] t) ==>
  lift_result rok rhalt rabort
    (dft_exec_suffix fuel ctx [EL n is] s) (exec_block fuel ctx bb' t0)
Proof
  strip_tac >>
  Cases_on `mm_flat_map_supply f esn (DROP (SUC n) is)` >>
  rename1 `mm_flat_map_supply f esn (DROP (SUC n) is) = (tail,es')` >>
  `mm_flat_map_supply f esn (DROP n is) = (EL n is :: tail,es')` by
    (gvs[arithmeticTheory.ADD1] >>
     simp[rich_listTheory.DROP_EL_CONS, mm_flat_map_supply_def]) >>
  `mm_flat_map_supply f supply is = (pre ++ out ++ EL n is :: tail,es')` by
    (drule_all mm_local_flat_map_supply_append >> simp[TAKE_DROP, APPEND_ASSOC]) >>
  `bb'.bb_instructions = pre ++ out ++ EL n is :: tail` by metis_tac[pairTheory.PAIR_EQ] >>
  `exec_block fuel ctx bb' t0 = dft_exec_suffix fuel ctx (out ++ EL n is :: tail) t0` by
    (irule dft_exec_suffix_boundary >>
     `LENGTH pre - (LENGTH out + LENGTH pre) = 0` by decide_tac >>
     simp[listTheory.DROP_APPEND]) >>
  drule mm_local_exec_prefix_suffix >>
  disch_then (qspec_then `EL n is :: tail` assume_tac) >>
  Cases_on `is_terminator (EL n is).inst_opcode` >- gvs[dft_exec_suffix_def] >>
  Cases_on `step_inst fuel ctx (EL n is) s` >> gvs[dft_exec_suffix_def, lift_result_def] >>
  Cases_on `step_inst fuel ctx (EL n is) t` >> gvs[dft_exec_suffix_def, lift_result_def]
QED

Theorem mm_local_emitted_stopping_trace:
  n < LENGTH is /\ t0.vs_inst_idx = LENGTH pre /\
  mm_flat_map_supply f supply (TAKE n is) = (pre ++ out,esn) /\
  (!es. f es (EL n is) = ([EL n is],es)) /\
  mm_flat_map_supply f supply is = (bb'.bb_instructions,fin) /\
  mm_local_safe_exec_prefix (P fn') fuel ctx out t0 t /\
  P fn' (EL n is) t /\
  (is_terminator (EL n is).inst_opcode \/
    ~(?u. step_inst fuel ctx (EL n is) t = OK u)) /\
  reachability_closed Inv ctx ==>
  EVERY (\((p,d',id),fn,i,u). p = [] ==> P fn i u)
    (trace_block [] d fuel ctx fn' bb' t0)
Proof
  strip_tac >>
  Cases_on `mm_flat_map_supply f esn (DROP (SUC n) is)` >>
  rename1 `mm_flat_map_supply f esn (DROP (SUC n) is) = (tail,es')` >>
  `mm_flat_map_supply f esn (DROP n is) = (EL n is :: tail,es')` by
    (gvs[arithmeticTheory.ADD1] >>
     simp[rich_listTheory.DROP_EL_CONS, mm_flat_map_supply_def]) >>
  `mm_flat_map_supply f supply is = (pre ++ out ++ EL n is :: tail,es')` by
    (drule_all mm_local_flat_map_supply_append >> simp[TAKE_DROP, APPEND_ASSOC]) >>
  `bb'.bb_instructions = pre ++ out ++ EL n is :: tail` by metis_tac[pairTheory.PAIR_EQ] >>
  `mm_local_exec_prefix fuel ctx out t0 t` by metis_tac[mm_local_safe_exec_prefix_erase] >>
  `t.vs_inst_idx = LENGTH pre + LENGTH out` by metis_tac[mm_local_exec_prefix_cursor] >>
  `get_instruction bb' t.vs_inst_idx = SOME (EL n is)` by
    simp[venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
  `EVERY (\((p,d',id),fn,i,u). p = [] ==> P fn i u)
    (trace_block [] d fuel ctx fn' bb' t)` by
    (drule_all venomExecutionReplayPropsTheory.trace_visit_root_every >>
     disch_then (fn th => rewrite_tac[th]) >>
     Cases_on `step_inst fuel ctx (EL n is) t` >> gvs[]) >>
  irule mm_local_safe_exec_prefix_trace >>
  (conj_tac >- metis_tac[]) >>
  qexistsl [`t`,`EL n is :: tail`,`out`] >> simp[] >>
  `LENGTH pre - (LENGTH out + LENGTH pre) = 0 /\
   LENGTH pre - (LENGTH out + (LENGTH pre + 1)) = 0` by decide_tac >>
  simp[DROP_APPEND]
QED

Theorem mm_local_mem2mem_post_phi_trace:
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
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn bb s) /\
  ~(?err. exec_block fuel ctx bb s = Error err) ==>
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn' bb' t0)
Proof
  strip_tac >> qabbrev_tac `h = phi_prefix_length is` >>
  qabbrev_tac `f = apply_groups_inst_supply Mem2Mem ns rs` >>
  `t0.vs_inst_idx = h` by gvs[state_equiv_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `h <= LENGTH is` by simp[Abbr `h`,venomExecProofsTheory.phi_prefix_length_le] >>
  `?n H. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n)` by
    (asm_rewrite_tac[] >> irule venomExecutionReplayPropsTheory.source_stopping_history >>
     simp[Abbr `h`] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `!q. h <= q /\ q <= n ==> (H q).vs_current_bb = bb.bb_label` by
    metis_tac[venomExecutionReplayPropsTheory.source_history_label] >>
  `mm_flat_map_supply f sk (TAKE h is) = (TAKE h is,sk)` by
    (simp[Abbr `f`] >> irule mm_local_mem2mem_phi_emission >>
     qexistsl [`bb`,`fn0`,`gs`,`index`,`k`,`sk`,`supply`] >>
     simp[Abbr `h`,EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
     conj_tac >- metis_tac[MEM_TAKE] >>
     qspec_then `bb.bb_instructions` (mp_tac o REWRITE_RULE[EVERY_MEM])
       analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  Cases_on `mm_flat_map_supply f sk (TAKE (n-h) (DROP h is))` >>
  rename1 `mm_flat_map_supply f sk (TAKE (n-h) (DROP h is)) = (out,esn)` >>
  `LENGTH (TAKE h is) = h` by simp[] >>
  `state_equiv excluded (H h with vs_inst_idx := h) t0` by
    (`s with vs_inst_idx := h = s` by
       simp[Abbr `h`,venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `?t. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t0 t /\
    mm_local_cut is gs H n excluded (h + LENGTH out) t /\
    mm_flat_map_supply f sk (TAKE n is) = (TAKE h is ++ out,esn) /\
    t.vs_inst_idx = h + LENGTH out` by
    (mp_tac (Q.SPECL [`n`,`fn0`,`supply`,`index`,`k`,`bb`,`sk`,`is`,`gs`,
       `ns`,`rs`,`deleted`,`excluded`,`h`,`H`,`fuel`,`ctx`,`eom`,`TAKE h is`,
       `sk`,`out`,`esn`,`t0`,`fn'`,`bb'`,`sk'`] mm_local_mem2mem_safe_prefix_execution) >>
     (impl_tac >- (gvs[Abbr `f`,Abbr `h`] >> rpt strip_tac >>
       metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ])) >>
     disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists `t` >> gvs[Abbr `f`]) >>
  pop_assum strip_assume_tac >>
  `~(?err. dft_exec_suffix fuel ctx [EL n is] (H n) = Error err)` by metis_tac[] >>
  `(!es. f es (EL n is) = ([EL n is],es)) /\
   lift_result
     (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
     (execution_equiv excluded) revert_equiv
     (dft_exec_suffix fuel ctx [EL n is] (H n))
     (dft_exec_suffix fuel ctx [EL n is] t)` by
    (mp_tac (Q.INST [`pc` |-> `h + LENGTH (out:instruction list)`]
       mm_local_mem2mem_stopping_result) >>
     (impl_tac >- asm_rewrite_tac[]) >> simp[Abbr `f`]) >>
  pop_assum strip_assume_tac >>
  `mm_flat_map_supply f sk is = (bb'.bb_instructions,sk')` by
    (qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
     simp[transform_block_mode_supply_def] >> gvs[Abbr `f`] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded` by
    (rpt strip_tac >>
     `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
     `MEM v (venomInst$inst_uses (EL n is))` by
       gvs[venomInstTheory.inst_uses_def,passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     `apply_groups_inst_supply Mem2Mem ns rs esn (EL n is) = ([EL n is],esn)` by
       gvs[Abbr `f`] >>
     `ns = nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
        (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
      rs = rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
     qpat_x_assum `is = _` SUBST_ALL_TAC >>
     drule_all mm_local_retained_operand_protected >> simp[]) >>
  `(H n).vs_inst_idx = n /\ (H n).vs_current_bb = bb.bb_label` by
    metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
  `static_mem_ok eom ctx fn (EL n is) (H n)` by
    (qpat_assum `!q. h <= q /\ q <= n ==> static_mem_ok _ _ _ _ _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `(in_revert_forward fn (H n) ==> in_revert_forward fn' t)` by
    (strip_tac >>
     `t.vs_current_bb = bb.bb_label` by
       (qpat_assum `mm_local_cut _ _ _ _ _ _ t` mp_tac >>
        simp[NoAsms,mm_local_cut_def,mm_local_nonmemory_frame_def,
          stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality] >>
        strip_tac >> gvs[] >> metis_tac[]) >>
     mp_tac (Q.INST [`f` |-> `apply_groups_inst_supply Mem2Mem ns rs`,
       `mode` |-> `Mem2Mem`, `pre` |-> `TAKE h (is:instruction list) ++ out`,
       `sn` |-> `esn:ir_supply`, `s` |-> `H (n:num)`]
       mm_local_prefix_in_revert_forward) >>
     (impl_tac >- gvs[Abbr `f`,arithmeticTheory.ADD_COMM]) >>
     asm_rewrite_tac[]) >>
  `static_mem_ok eom ctx fn' (EL n is) t` by
    (drule_all mm_local_retained_static_if_forward >> simp[]) >>
  `is_terminator (EL n is).inst_opcode \/ ~(?u. step_inst fuel ctx (EL n is) t = OK u)` by
    (qpat_x_assum `is = _` kall_tac >>
     Cases_on `is_terminator (EL n is).inst_opcode` >> simp[] >>
     qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
     simp[dft_exec_suffix_def] >>
     Cases_on `step_inst fuel ctx (EL n is) (H n)` >> fs[] >>
     Cases_on `step_inst fuel ctx (EL n is) t` >> simp[lift_result_def] >>
     qpat_x_assum `!err. dft_exec_suffix _ _ _ _ <> Error err` mp_tac >>
     simp[dft_exec_suffix_def]) >>
  irule (INST_TYPE [alpha |-> ``:ir_supply``] mm_local_emitted_stopping_trace) >>
  (conj_tac
   >- (qexists `\c fn i s. T` >>
       simp[contextCodegenRelTheory.reachability_closed_def,contextCodegenRelTheory.fn_entry_inv_def])) >>
  qexistsl [`esn`,`f`,`sk'`,`is`,`n`,`out`,`TAKE h is`,`sk`,`t`] >>
  simp[] >> gvs[]
QED

Theorem mm_local_zero_stopping_unchanged[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM i bb.bb_instructions /\
  ~(?err. dft_exec_suffix fuel ctx [i] s = Error err) /\
  (is_terminator i.inst_opcode \/ ~(?u. step_inst fuel ctx i s = OK u)) ==>
  !es. apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed)
    es i = ([i],es)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule mm_local_memzero_nonselected_unchanged >> simp[] >>
  `i.inst_opcode <> MSTORE /\ i.inst_opcode <> CALLDATACOPY` suffices_by
    (strip_tac >> gvs[is_zero_store_def, is_calldatasize_copy_def]) >>
  Cases_on `is_terminator i.inst_opcode`
  >- (Cases_on `i.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
  Cases_on `step_inst fuel ctx i s` >> gvs[dft_exec_suffix_def]
  >- (drule opcodeClassTheory.step_inst_halt_opcodes >> strip_tac >> gvs[])
  >- (drule opcodeClassTheory.step_inst_abort_opcodes >> strip_tac >> gvs[])
  >- (Cases_on `i.inst_opcode = INVOKE` >- gvs[] >>
      gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
      drule opcodeClassTheory.step_inst_base_intret_opcodes >> strip_tac >> gvs[])
QED

Theorem mm_local_zero_phi_emission:
  !xs es.
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI) xs ==>
  mm_flat_map_supply
    (apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions gs)
      (rep_map_of_groups bb.bb_instructions gs)) es xs = (xs,es)
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt strip_tac >> fs[] >>
  `!r. apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions gs)
    (rep_map_of_groups bb.bb_instructions gs) r h = ([h],r)` by
    (gvs[] >> irule mm_local_memzero_nonselected_unchanged >>
     simp[is_zero_store_def, is_calldatasize_copy_def]) >>
  simp[mm_flat_map_supply_def] >> gvs[]
QED

Theorem mm_local_zero_stopping_result[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\ bb_well_formed bb /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  n < LENGTH is /\ mm_local_zero_cut dfg is gs H n excluded pc t /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  ~(?err. dft_exec_suffix fuel ctx [EL n is] (H n) = Error err) /\
  (is_terminator (EL n is).inst_opcode \/
    ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [EL n is] (H n))
    (dft_exec_suffix fuel ctx [EL n is] t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_terminator (EL n is).inst_opcode`
  >- (`SUC n = LENGTH is` by
        (qpat_x_assum `bb_well_formed bb` mp_tac >>
         simp[venomWfTheory.bb_well_formed_def] >> strip_tac >>
         `n = PRE (LENGTH is)` by metis_tac[] >> gvs[] >> decide_tac) >>
      `mm_local_pending_indices is gs n = []` by
        (irule mm_local_zero_terminal_pending_empty >> metis_tac[]) >>
      irule mm_local_zero_terminator_result >> metis_tac[]) >>
  `~(?err. step_inst fuel ctx (EL n is) (H n) = Error err)` by
    (Cases_on `step_inst fuel ctx (EL n is) (H n)` >> gvs[dft_exec_suffix_def]) >>
  `lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx (EL n is) (H n)) (step_inst fuel ctx (EL n is) t)` by
    (irule mm_local_zero_nonterminator_stop >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx (EL n is) (H n)` >>
  Cases_on `step_inst fuel ctx (EL n is) t` >>
  gvs[lift_result_def, dft_exec_suffix_def]
QED

Theorem mm_local_zero_post_phi_result:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  h = phi_prefix_length is /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  lookup_block bb.bb_label fn0.fn_blocks = SOME bb /\
  s.vs_inst_idx = h /\ s.vs_current_bb = bb.bb_label /\
  t0.vs_inst_idx = h /\ state_equiv excluded s t0 /\
  (!v. v NOTIN excluded ==> MEM v supply.irs_used_vars) /\
  (!i v. MEM i is /\ MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
    (trace_block [] d fuel ctx fn0 bb s) /\
  ~(?err. exec_block fuel ctx bb s = Error err) /\
  (!n H. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn0 (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n) ==>
    (!j. h <= j /\ j <= n ==>
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
    (!j dst v len. h <= j /\ j < n /\
      is_calldatasize_copy dfg (EL j is) /\
      (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
      lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256))) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (exec_block fuel ctx bb s) (exec_block fuel ctx bb' t0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM bb fn0.fn_blocks` by metis_tac[EL_MEM] >>
  `bb_well_formed bb` by gvs[venomWfTheory.wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule mm_local_prefix_wf_id_distinct >>
     qexistsl [`fn0`,`index`,`0`,`supply`,`supply`] >>
     simp[mm_local_prefix_zero] >> metis_tac[]) >>
  `h <= LENGTH is` by simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `?n H. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn0 (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n)` by
    (asm_rewrite_tac[] >> irule venomExecutionReplayPropsTheory.source_stopping_history >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `!n H. _` (qspecl_then [`n`,`H`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `!q. h <= q /\ q <= n ==> (H q).vs_current_bb = bb.bb_label` by
    metis_tac[venomExecutionReplayPropsTheory.source_history_label] >>
  `mm_flat_map_supply f supply (TAKE h is) = (TAKE h is,supply)` by
    (gvs[] >> irule mm_local_zero_phi_emission >>
     simp[EVERY_MEM] >> gen_tac >> disch_tac >> conj_tac
     >- (drule MEM_TAKE >> simp[]) >>
     qspec_then `(EL index fn0.fn_blocks).bb_instructions` mp_tac analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  Cases_on `mm_flat_map_supply f supply (TAKE (n-h) (DROP h is))` >>
  rename1 `mm_flat_map_supply f supply (TAKE (n-h) (DROP h is)) = (out,esn)` >>
  `LENGTH (TAKE h is) = h` by simp[] >>
  `state_equiv excluded (H h with vs_inst_idx := LENGTH (TAKE h is)) t0` by
    (`s with vs_inst_idx := h = s` by
       simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `?t. mm_local_exec_prefix fuel ctx out t0 t /\
    mm_local_zero_cut dfg is gs H n excluded (h + LENGTH out) t /\
    mm_flat_map_supply f supply (TAKE n is) = (TAKE h is ++ out,esn) /\
    t.vs_inst_idx = h + LENGTH out` by
    (mp_tac (Q.INST [`pre` |-> `TAKE h is`, `esh` |-> `supply`, `fn` |-> `fn0`] mm_local_zero_stopping_cut) >>
     (impl_tac >- (gvs[] >> rpt strip_tac >>
       `MEM (EL j (EL index fn0.fn_blocks).bb_instructions)
         (EL index fn0.fn_blocks).bb_instructions` by
         (irule EL_MEM >> decide_tac) >> metis_tac[])) >>
     gvs[]) >>
  `~(?err. dft_exec_suffix fuel ctx [EL n is] (H n) = Error err)` by metis_tac[] >>
  `!es. f es (EL n is) = ([EL n is],es)` by
    (gvs[] >> irule mm_local_zero_stopping_unchanged >> metis_tac[EL_MEM]) >>
  `mm_flat_map_supply f supply is = (bb'.bb_instructions,supply')` by
    (qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
     simp[transform_block_memzero_supply_def] >> gvs[] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [EL n is] (H n))
    (dft_exec_suffix fuel ctx [EL n is] t)` by
    (irule mm_local_zero_stopping_result >>
     gvs[] >> conj_tac >- metis_tac[EL_MEM] >>
     qexistsl [`EL index fn0.fn_blocks`,`dfg_build_function fn0`,
       `phi_prefix_length (EL index fn0.fn_blocks).bb_instructions + LENGTH out`] >>
     gvs[]) >>
  metis_tac[mm_local_emitted_stopping_result]
QED
Theorem mm_local_zero_post_phi_trace:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  h = phi_prefix_length is /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  lookup_block bb.bb_label fn0.fn_blocks = SOME bb /\
  s.vs_inst_idx = h /\ s.vs_current_bb = bb.bb_label /\
  t0.vs_inst_idx = h /\ state_equiv excluded s t0 /\
  (!v. v NOTIN excluded ==> MEM v supply.irs_used_vars) /\
  (!i v. MEM i is /\ MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
    (trace_block [] d fuel ctx fn0 bb s) /\
  ~(?err. exec_block fuel ctx bb s = Error err) /\
  (!n H. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn0 (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n) ==>
    (!j. h <= j /\ j <= n ==>
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
    (!j dst v len. h <= j /\ j < n /\
      is_calldatasize_copy dfg (EL j is) /\
      (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
      lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256))) ==>
  EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
    (trace_block [] d fuel ctx fn' bb' t0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM bb fn0.fn_blocks` by metis_tac[EL_MEM] >>
  `bb_well_formed bb` by gvs[venomWfTheory.wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule mm_local_prefix_wf_id_distinct >>
     qexistsl [`fn0`,`index`,`0`,`supply`,`supply`] >>
     simp[mm_local_prefix_zero] >> metis_tac[]) >>
  `h <= LENGTH is` by simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `?n H. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn0 (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n)` by
    (asm_rewrite_tac[] >> irule venomExecutionReplayPropsTheory.source_stopping_history >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `!n H. _` (qspecl_then [`n`,`H`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `!q. h <= q /\ q <= n ==> (H q).vs_current_bb = bb.bb_label` by
    metis_tac[venomExecutionReplayPropsTheory.source_history_label] >>
  `mm_flat_map_supply f supply (TAKE h is) = (TAKE h is,supply)` by
    (gvs[] >> irule mm_local_zero_phi_emission >>
     simp[EVERY_MEM] >> gen_tac >> disch_tac >> conj_tac
     >- (drule MEM_TAKE >> simp[]) >>
     qspec_then `(EL index fn0.fn_blocks).bb_instructions` mp_tac analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  Cases_on `mm_flat_map_supply f supply (TAKE (n-h) (DROP h is))` >>
  rename1 `mm_flat_map_supply f supply (TAKE (n-h) (DROP h is)) = (out,esn)` >>
  `LENGTH (TAKE h is) = h` by simp[] >>
  `state_equiv excluded (H h with vs_inst_idx := h) t0` by
    (`s with vs_inst_idx := h = s` by
       simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `mm_local_zero_cut dfg is gs H h excluded h t0` by
    metis_tac[mm_local_zero_cut_post_phi_init] >>
  `h + (n-h) = n` by decide_tac >>
  `?t. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t0 t /\
    mm_local_zero_cut dfg is gs H n excluded (h + LENGTH out) t` by
    (mp_tac (Q.INST [`m` |-> `n-h`, `n` |-> `h`, `es` |-> `supply`,
       `es'` |-> `esn`, `pre` |-> `TAKE h is`, `pc` |-> `h`, `t` |-> `t0`,
       `sk'` |-> `supply'`] mm_local_zero_actual_safe_interval) >>
     (impl_tac >- (gvs[] >> rpt strip_tac >>
       `j < LENGTH (EL index fn0.fn_blocks).bb_instructions` by decide_tac >>
       metis_tac[EL_MEM])) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `TAKE h is ++ TAKE (n-h) (DROP h is) = TAKE n is` by metis_tac[TAKE_SUM] >>
  `mm_flat_map_supply f supply (TAKE n is) = (TAKE h is ++ out,esn)` by
    (drule_all mm_local_flat_map_supply_append >> simp[]) >>
  `~(?err. dft_exec_suffix fuel ctx [EL n is] (H n) = Error err)` by metis_tac[] >>
  `!es. f es (EL n is) = ([EL n is],es)` by
    (gvs[] >> irule mm_local_zero_stopping_unchanged >> metis_tac[EL_MEM]) >>
  `mm_flat_map_supply f supply is = (bb'.bb_instructions,supply')` by
    (qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
     simp[transform_block_memzero_supply_def] >> gvs[] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `static_mem_ok eom ctx fn' (EL n is) t` by
    (irule mm_local_zero_retained_static >>
     qexistsl [`H`, `{v | v NOTIN excluded}`, `bb`, `bb'`, `dfg`,
       `excluded`, `f`, `fn0`, `gs`, `index`, `is`, `n`,
       `TAKE h is ++ out`, `esn`, `supply`, `supply'`] >>
     simp[] >> gvs[] >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     gvs[fn_inst_wf_compute, EVERY_MEM, wf_function_def, venomInstTheory.fn_labels_def] >>
     metis_tac[EL_MEM]) >>
  `lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [EL n is] (H n))
    (dft_exec_suffix fuel ctx [EL n is] t)` by
    (irule mm_local_zero_stopping_result >> metis_tac[EL_MEM]) >>
  `is_terminator (EL n is).inst_opcode \/ ~(?u. step_inst fuel ctx (EL n is) t = OK u)` by
    (qpat_x_assum `is = _` kall_tac >>
     Cases_on `is_terminator (EL n is).inst_opcode` >> simp[] >>
     qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
     simp[dft_exec_suffix_def] >>
     Cases_on `step_inst fuel ctx (EL n is) (H n)` >> fs[] >>
     Cases_on `step_inst fuel ctx (EL n is) t` >> simp[lift_result_def] >>
     qpat_x_assum `!err. dft_exec_suffix _ _ _ _ <> Error err` mp_tac >>
     simp[dft_exec_suffix_def]) >>
  irule (INST_TYPE [alpha |-> ``:ir_supply``] mm_local_emitted_stopping_trace) >>
  (conj_tac
   >- (qexists `\c fn i s. T` >>
       simp[contextCodegenRelTheory.reachability_closed_def, contextCodegenRelTheory.fn_entry_inv_def])) >>
  qexistsl [`esn`, `f`, `supply'`, `is`, `n`, `out`, `TAKE h is`, `supply`, `t`] >>
  simp[] >> gvs[]
QED


Theorem mm_local_zero_run_block_result[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  h = phi_prefix_length is /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  s.vs_current_bb = bb.bb_label /\
  lookup_block s.vs_current_bb fn0.fn_blocks = SOME bb /\
  (!v. v NOTIN excluded ==> MEM v supply.irs_used_vars) /\
  (!i v. MEM i is /\ MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
    (trace_blocks [] d (SUC fuel) ctx fn0 s) /\
  ~(?err. run_block fuel ctx bb s = Error err) /\
  (!sp n H. eval_phis s is = OK sp /\
    h <= n /\ n < LENGTH is /\ H h = sp with vs_inst_idx := h /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn0 (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb (sp with vs_inst_idx := h) =
      dft_exec_suffix fuel ctx [EL n is] (H n) ==>
    (!j. h <= j /\ j <= n ==>
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
    (!j dst v len. h <= j /\ j < n /\
      is_calldatasize_copy dfg (EL j is) /\
      (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
      lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256))) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (run_block fuel ctx bb s) (run_block fuel ctx bb' s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bb_well_formed bb` by
    (gvs[venomWfTheory.wf_function_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (asm_rewrite_tac[] >> irule mm_local_prefix_wf_id_distinct >>
     qexistsl [`fn0`,`index`,`0`,`supply`,`supply`] >>
     simp[mm_local_prefix_zero] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (DROP h is)` by
    (asm_rewrite_tac[] >> irule simplifyCfgFixupStaticTheory.scfg_phi_suffix_nonphi >>
     gvs[venomWfTheory.bb_well_formed_def]) >>
  `mm_flat_map_supply f supply (TAKE h is) = (TAKE h is,supply)` by
    (gvs[] >> irule mm_local_zero_phi_emission >>
     simp[EVERY_MEM] >> gen_tac >> disch_tac >> conj_tac
     >- (drule MEM_TAKE >> simp[]) >>
     qspec_then `(EL index fn0.fn_blocks).bb_instructions` mp_tac
       analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  Cases_on `mm_flat_map_supply f supply (DROP h is)` >>
  rename1 `mm_flat_map_supply f supply (DROP h is) = (out,es)` >>
  `EVERY (\i. i.inst_opcode <> PHI) out` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM i (DROP h is)` by
       (irule (Q.ISPECL [`f:ir_supply -> instruction -> instruction list # ir_supply`,
         `\i:instruction. i.inst_opcode = PHI`]
         mmSupplyWfProofsTheory.mm_flat_map_supply_origin) >>
        metis_tac[mmSupplyWfProofsTheory.apply_memzero_inst_supply_phi_origin]) >>
     gvs[EVERY_MEM]) >>
  `bb'.bb_instructions = TAKE h is ++ out` by
    (drule_all mm_local_flat_map_supply_append >>
     simp[TAKE_DROP] >> strip_tac >>
     qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
     simp[transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `phi_prefix_length bb'.bb_instructions = h /\
    eval_phis s bb'.bb_instructions = eval_phis s is` by
    (gvs[] >> metis_tac[dftIndexedExecTheory.dft_phi_prefix_append,
      dftIndexedExecTheory.dft_eval_phis_append,
      analysisSimProofsBaseTheory.phi_prefix_all_phi, TAKE_DROP]) >>
  mp_tac (Q.SPECL [`s`,`is`] venomExecSemanticsTheory.eval_phis_ok_or_error_defs) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (rename1 `eval_phis s is = OK sp` >>
      `eval_phis s bb.bb_instructions = OK sp` by metis_tac[] >>
      drule_all dftGasFromListTraceDefsTheory.trace_blocks_enter >>
      disch_then (fn th => fs[th, EVERY_APPEND]) >>
      `sp.vs_current_bb = bb.bb_label` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
      `lift_result
        (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
        (execution_equiv excluded) revert_equiv
        (exec_block fuel ctx bb (sp with vs_inst_idx := h))
        (exec_block fuel ctx bb' (sp with vs_inst_idx := h))` by
        (irule mm_local_zero_post_phi_result >>
         conj_tac
         >- (gvs[venomExecSemanticsTheory.run_block_def]) >>
         conj_tac >- simp[] >>
         reverse conj_tac >- irule stateEquivProofsTheory.state_equiv_refl >>
         qexistsl [`SUC d`,`dfg`,`eom`,`f`,`fn0`,`gs`,`h`,`index`,`is`,`supply`,`supply'`] >>
         qpat_x_assum `h = phi_prefix_length is` SUBST_ALL_TAC >>
         qpat_x_assum `is = bb.bb_instructions` SUBST_ALL_TAC >>
         qpat_x_assum `bb = EL index fn0.fn_blocks` SUBST_ALL_TAC >>
         qpat_x_assum `dfg = dfg_build_function fn0` SUBST_ALL_TAC >>
         simp[stateEquivProofsTheory.state_equiv_refl] >>
         rpt conj_tac >>
         asm_simp_tac (srw_ss()) [] >>
         qpat_assum `s.vs_current_bb = _` (fn th => rewrite_tac[GSYM th]) >>
         first_assum MATCH_ACCEPT_TAC) >>
      gvs[venomExecSemanticsTheory.run_block_def]) >>
  gvs[venomExecSemanticsTheory.run_block_def]
QED

Theorem mm_local_zero_run_block_correct[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  h = phi_prefix_length is /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  s.vs_current_bb = bb.bb_label /\
  lookup_block s.vs_current_bb fn0.fn_blocks = SOME bb /\
  (!v. v NOTIN excluded ==> MEM v supply.irs_used_vars) /\
  (!i v. MEM i is /\ MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
    (trace_blocks [] d (SUC fuel) ctx fn0 s) /\
  ~(?err. run_block fuel ctx bb s = Error err) /\
  (!sp n H. eval_phis s is = OK sp /\
    h <= n /\ n < LENGTH is /\ H h = sp with vs_inst_idx := h /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==> static_mem_ok eom ctx fn0 (EL q is) (H q)) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb (sp with vs_inst_idx := h) =
      dft_exec_suffix fuel ctx [EL n is] (H n) ==>
    (!j. h <= j /\ j <= n ==>
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
    (!j dst v len. h <= j /\ j < n /\
      is_calldatasize_copy dfg (EL j is) /\
      (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
      lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256))) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (run_block fuel ctx bb s) (run_block fuel ctx bb' s) /\
  (!sp'. eval_phis s bb'.bb_instructions = OK sp' ==>
    EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
      (trace_block [] (SUC d) fuel ctx fn' bb'
        (sp' with vs_inst_idx := phi_prefix_length bb'.bb_instructions))) /\
  EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
    (case eval_phis s bb'.bb_instructions of
       OK sp' => trace_block [] (SUC d) fuel ctx fn' bb'
         (sp' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | _ => [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule mm_local_zero_run_block_result >>
      (conj_tac >- asm_rewrite_tac[]) >>
      (conj_tac >- asm_rewrite_tac[]) >>
      qexistsl [`d`,`dfg`,`eom`,`f`,`fn0`,`gs`,`h`,`index`,`is`,`supply`,`supply'`] >>
      asm_rewrite_tac[]) >>
  conj_asm1_tac >- (
  `bb_well_formed bb` by
    (gvs[venomWfTheory.wf_function_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (asm_rewrite_tac[] >> irule mm_local_prefix_wf_id_distinct >>
     qexistsl [`fn0`,`index`,`0`,`supply`,`supply`] >>
     simp[mm_local_prefix_zero] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (DROP h is)` by
    (asm_rewrite_tac[] >> irule simplifyCfgFixupStaticTheory.scfg_phi_suffix_nonphi >>
     gvs[venomWfTheory.bb_well_formed_def]) >>
  `mm_flat_map_supply f supply (TAKE h is) = (TAKE h is,supply)` by
    (gvs[] >> irule mm_local_zero_phi_emission >>
     simp[EVERY_MEM] >> gen_tac >> disch_tac >> conj_tac
     >- (drule MEM_TAKE >> simp[]) >>
     qspec_then `(EL index fn0.fn_blocks).bb_instructions` mp_tac
       analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  Cases_on `mm_flat_map_supply f supply (DROP h is)` >>
  rename1 `mm_flat_map_supply f supply (DROP h is) = (out,es)` >>
  `EVERY (\i. i.inst_opcode <> PHI) out` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM i (DROP h is)` by
       (irule (Q.ISPECL [`f:ir_supply -> instruction -> instruction list # ir_supply`,
         `\i:instruction. i.inst_opcode = PHI`]
         mmSupplyWfProofsTheory.mm_flat_map_supply_origin) >>
        metis_tac[mmSupplyWfProofsTheory.apply_memzero_inst_supply_phi_origin]) >>
     gvs[EVERY_MEM]) >>
  `bb'.bb_instructions = TAKE h is ++ out` by
    (drule_all mm_local_flat_map_supply_append >>
     simp[TAKE_DROP] >> strip_tac >>
     qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
     simp[transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `phi_prefix_length bb'.bb_instructions = h /\
    eval_phis s bb'.bb_instructions = eval_phis s is` by
    (gvs[] >> metis_tac[dftIndexedExecTheory.dft_phi_prefix_append,
      dftIndexedExecTheory.dft_eval_phis_append,
      analysisSimProofsBaseTheory.phi_prefix_all_phi, TAKE_DROP]) >>
  gen_tac >> disch_tac >>
  `eval_phis s bb.bb_instructions = OK sp'` by metis_tac[] >>
  drule_all dftGasFromListTraceDefsTheory.trace_blocks_enter >>
  disch_then (fn th => fs[th, EVERY_APPEND]) >>
  `sp'.vs_current_bb = bb.bb_label` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  irule mm_local_zero_post_phi_trace >>
  (conj_tac >- simp[]) >>
  qexistsl [`bb`,`dfg`,`excluded`,`f`,`fn0`,`gs`,`h`,`index`,`is`,
    `sp' with vs_inst_idx := h`,`supply`,`supply'`] >>
  asm_rewrite_tac[stateEquivProofsTheory.state_equiv_refl] >>
  qpat_x_assum `bb'.bb_instructions = _` kall_tac >>
  qpat_x_assum `EVERY _ (case run_block_non_phis _ _ _ _ of OK _ => _ | _ => _ | _ => _ | _ => _ | _ => _)` kall_tac >>
  qpat_assum `bb = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `is = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `h = _` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `!sp n H. _` (qspecl_then [`sp'`,`n`,`H`] mp_tac) >>
      qpat_assum `dfg = _` (fn th => rewrite_tac[GSYM th]) >>
      asm_rewrite_tac[] >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `!err. run_block_entry _ _ _ _ <> Error err` mp_tac >>
      pure_rewrite_tac[venomExecSemanticsTheory.run_block_def] >>
      qpat_assum `eval_phis s bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
      qpat_assum `bb = _` (fn th => rewrite_tac[GSYM th]) >>
      qpat_assum `is = _` (fn th => rewrite_tac[GSYM th]) >>
      qpat_assum `h = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >> metis_tac[]) >>
  Cases_on `eval_phis s bb'.bb_instructions` >> simp[] >>
  qpat_x_assum `!sp'. _` (qspec_then `v` mp_tac) >>
  asm_rewrite_tac[]
QED

