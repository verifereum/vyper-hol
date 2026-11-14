(* Local memmerging phase: calldata and DLOAD execution. *)
Theory mmLocalPayloadExecutionProofs
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
  mmLocalSafeExecutionProofs
  venomTransformStructureProps venomWriteReplayProps venomExecutionReplayProps irSupplyFreshProps
Libs
  wordsLib finite_mapLib stepInstBaseLib

Theorem mm_local_payload_opcodes[local,simp]:
  mode IN {CalldataMerge; DloadMerge} ==>
  mode_copy_opcode mode <> MSTORE /\
  mode_load_opcode mode <> MSTORE /\
  mode_load_opcode mode <> mode_copy_opcode mode /\
  mode_allows_overlap mode
Proof
  Cases_on `mode` >> simp[mode_copy_opcode_def, mode_load_opcode_def,
    mode_allows_overlap_def]
QED

Theorem mm_local_payload_bulk_step[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  i.inst_opcode = mode_copy_opcode mode /\
  i.inst_operands = [Lit dst; Lit src; Lit len] ==>
  step_inst fuel ctx i t =
    OK (write_memory_with_expansion (w2n dst)
      (TAKE (w2n len) (DROP (w2n src) (if mode = CalldataMerge then t.vs_call_ctx.cc_calldata else t.vs_data_section) ++
        REPLICATE (w2n len) 0w)) t)
Proof
  Cases_on `mode` >> simp[mode_copy_opcode_def] >> strip_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomStateTheory.eval_operand_def]
QED

Theorem mm_local_payload_store_step[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  i.inst_opcode = MSTORE /\ i.inst_operands = [Lit dst; Var v] /\
  lookup_var v t = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n src) (if mode = CalldataMerge then t.vs_call_ctx.cc_calldata else t.vs_data_section) ++ REPLICATE 32 0w))) ==>
  step_inst fuel ctx i t =
    OK (write_memory_with_expansion (w2n dst)
      (TAKE 32 (DROP (w2n src) (if mode = CalldataMerge then t.vs_call_ctx.cc_calldata else t.vs_data_section) ++ REPLICATE 32 0w)) t)
Proof
  strip_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_write2_def,
    venomStateTheory.eval_operand_def, venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def,
    venomMemPropsTheory.word_bytes_roundtrip_256,
    copyFwdEquivTheory.mcopy_data_length]
QED

Theorem mm_local_payload_word_steps[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  dst < dimword (:256) /\ src < dimword (:256) /\
  bs = TAKE 32 (DROP src
    (if mode = CalldataMerge then t.vs_call_ctx.cc_calldata else t.vs_data_section)
      ++ REPLICATE 32 0w) /\
  w = word_of_bytes T (0w:bytes32) bs ==>
  step_inst fuel ctx (mk_load_inst mode inst src v) t = OK (update_var v w t) /\
  step_inst fuel ctx (mk_mstore_from_load inst dst v) (update_var v w t) =
    OK (update_var v w (write_memory_with_expansion dst bs t))
Proof
  strip_tac >> conj_tac
  >- (Cases_on `mode` >> fs[] >>
      gvs[mk_load_inst_def, mode_load_opcode_def,
        venomExecSemanticsTheory.step_inst_non_invoke] >>
      simp[stepInstBaseLib.opcode_clause ``CALLDATALOAD``,
        stepInstBaseLib.opcode_clause ``DLOAD``] >>
      simp[venomExecSemanticsTheory.exec_read1_def,
        venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w]) >>
  simp[mk_mstore_from_load_def, venomExecSemanticsTheory.step_inst_non_invoke,
    stepInstBaseLib.opcode_clause ``MSTORE``,
    venomExecSemanticsTheory.exec_write2_def,
    venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w,
    venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def,
    venomMemPropsTheory.word_bytes_roundtrip_256,
    copyFwdEquivTheory.mcopy_data_length]
QED

Definition mm_local_payload_capture_def:
  mm_local_payload_capture mode is H n j =
    if j < n /\ j < LENGTH is then
      if (EL j is).inst_opcode = mode_copy_opcode mode then
        (case (EL j is).inst_operands of
           [a;b;c] =>
             (case (eval_operand a (H j), eval_operand b (H j),
                    eval_operand c (H j)) of
                (SOME dst,SOME src,SOME len) =>
                  SOME (w2n dst, TAKE (w2n len)
                    (DROP (w2n src) (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) ++
                     REPLICATE (w2n len) 0w))
              | _ => NONE)
         | _ => NONE)
      else if (EL j is).inst_opcode = MSTORE then
        mm_local_write_capture is H n j
      else NONE
    else NONE
End

Theorem mm_local_payload_capture_past[local]:
  j < n /\ n <= m ==>
  mm_local_payload_capture mode is H n j = mm_local_payload_capture mode is H m j
Proof
  simp[mm_local_payload_capture_def, mm_local_payload_opcodes, mm_local_write_capture_def]
QED

Theorem mm_local_payload_capture_future[local]:
  n <= j ==> mm_local_payload_capture mode is H n j = NONE
Proof
  simp[mm_local_payload_capture_def, mm_local_payload_opcodes]
QED

Theorem mm_local_payload_capture_sound[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  mm_local_history is H n /\
  mm_local_payload_capture mode is H n j = SOME (d,bs) ==>
  (H (SUC j)).vs_memory = (write_memory_with_expansion d bs (H j)).vs_memory
Proof
  Cases_on `mode` >> simp[mode_copy_opcode_def] >>
  simp[mm_local_payload_capture_def, mode_copy_opcode_def] >>
  rpt IF_CASES_TAC >> gvs[AllCaseEqs()] >> strip_tac
  >- (`step_inst_base (EL j is) (H j) = OK (H (SUC j))` by
        metis_tac[mm_local_history_def] >>
      gvs[venomExecSemanticsTheory.step_inst_base_def])
  >- metis_tac[mm_local_write_capture_sound]
  >- (`step_inst_base (EL j is) (H j) = OK (H (SUC j))` by
        metis_tac[mm_local_history_def] >>
      gvs[venomExecSemanticsTheory.step_inst_base_def]) >>
  metis_tac[mm_local_write_capture_sound]
QED

Theorem mm_local_payload_capture_actual_step[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  mm_local_payload_capture mode is H n j = SOME (d,bs) /\
  step_inst fuel ctx (EL j is) (H j) = OK u ==>
  (u with vs_inst_idx := SUC j).vs_memory =
    (write_memory_with_expansion d bs (H j)).vs_memory /\
  mm_local_nonmemory_frame (u with vs_inst_idx := SUC j) =
    mm_local_nonmemory_frame (H j) /\
  (!v. lookup_var v (u with vs_inst_idx := SUC j) = lookup_var v (H j))
Proof
  strip_tac >>
  `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (Cases_on `mode` >> gvs[mm_local_payload_capture_def,
      mode_copy_opcode_def, AllCaseEqs()]) >>
  `mm_local_nonmemory_frame u = mm_local_nonmemory_frame (H j) /\
    (!v. lookup_var v u = lookup_var v (H j))` by
    metis_tac[mm_local_write_runtime_frame] >>
  reverse conj_tac
  >- gvs[mm_local_nonmemory_frame_def, venomStateTheory.lookup_var_def] >>
  Cases_on `mode` >>
  gvs[mm_local_payload_capture_def, mm_local_write_capture_def,
      mode_copy_opcode_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  with_opcode_clause simp >>
  simp[venomExecSemanticsTheory.exec_write2_def,
    venomMemPropsTheory.mstore_eq_write_mem] >> strip_tac >> gvs[]
QED

Definition mm_local_payload_cut_def:
  mm_local_payload_cut cap is gs H n excluded pc t <=>
    t.vs_inst_idx = pc /\
    mm_local_nonmemory_frame (H n) = mm_local_nonmemory_frame t /\
    (!v. v NOTIN excluded ==> lookup_var v (H n) = lookup_var v t) /\
    mm_local_pending cap (mm_local_pending_indices is gs n) (H n) t
End

Theorem mm_local_payload_cut_init[local]:
  h = phi_prefix_length is /\
  state_equiv excluded (H h with vs_inst_idx := pc) t ==>
  mm_local_payload_cut cap is gs H h excluded pc t
Proof
  strip_tac >>
  `mm_local_pending_indices is gs h = []` by
    (Cases_on `mm_local_pending_indices is gs h` >> simp[] >>
     rename1 `mm_local_pending_indices is gs h = j::js` >>
     `MEM j (mm_local_pending_indices is gs h)` by simp[] >>
     drule mm_local_pending_indices_after_phis >>
     gvs[mm_local_pending_indices_mem]) >>
  gvs[mm_local_payload_cut_def, mm_local_pending_empty, state_equiv_frame,
    mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.lookup_var_def, venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_payload_cut_empty[local]:
  mm_local_payload_cut cap is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] ==>
  state_equiv excluded ((H n) with vs_inst_idx := pc) t
Proof
  strip_tac >> gvs[mm_local_payload_cut_def, mm_local_pending_empty] >>
  gvs[state_equiv_frame, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
    venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_calldata_bytes[local]:
  mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w) src len =
  TAKE len (DROP src cd ++ REPLICATE len 0w)
Proof
  irule LIST_EQ >> simp[mm_local_bytes_def,
    copyFwdEquivTheory.mcopy_data_length] >> rpt strip_tac >>
  simp[copyFwdEquivTheory.take_drop_replicate_el,
    allocaRemapDefsTheory.mem_byte_at_def]
QED

Theorem mm_local_payload_capture_literal[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  j < n /\ j < LENGTH is /\
  (EL j is).inst_opcode = mode_copy_opcode mode /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] ==>
  mm_local_payload_capture mode is H n j =
    SOME (w2n dst, mm_local_bytes
      (\a. if a < LENGTH (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section)
           then EL a (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) else 0w)
      (w2n src) (w2n len))
Proof
  simp[mm_local_payload_capture_def, mm_local_payload_opcodes, venomStateTheory.eval_operand_def,
    mm_local_calldata_bytes]
QED

Theorem mm_local_payload_capture_store[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  j < n /\ j < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP src (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) ++ REPLICATE 32 0w))) ==>
  mm_local_payload_capture mode is H n j = SOME (w2n dst, mm_local_bytes
    (\a. if a < LENGTH (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section)
         then EL a (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) else 0w) src 32)
Proof
  strip_tac >>
  simp[mm_local_payload_capture_def, mm_local_payload_opcodes, mm_local_write_capture_def,
    venomStateTheory.eval_operand_def, mm_local_calldata_bytes] >>
  irule venomMemPropsTheory.word_bytes_roundtrip_256 >> simp[LENGTH_TAKE_EQ]
QED

Theorem mm_local_payload_bulk_group_captures[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  j < n /\ j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  (EL j is).inst_opcode = mode_copy_opcode mode /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id] |> ==>
  mm_local_group_captures is (mm_local_payload_capture mode is H n)
    (\a. if a < LENGTH (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section)
         then EL a (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) else 0w) c
Proof
  strip_tac >> irule mm_local_group_captures_birth >>
  conj_tac >- simp[] >> qexists `j` >>
  simp[] >> metis_tac[mm_local_payload_capture_literal]
QED

Theorem mm_local_payload_store_group_captures[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  j < n /\ j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP src (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) ++ REPLICATE 32 0w))) /\
  (!q. q < LENGTH is /\ MEM (EL q is).inst_id lids ==>
    (EL q is).inst_opcode = mode_load_opcode mode) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++ lids |> ==>
  mm_local_group_captures is (mm_local_payload_capture mode is H n)
    (\a. if a < LENGTH (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section)
         then EL a (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) else 0w) c
Proof
  strip_tac >>
  `mm_local_payload_capture mode is H n j = SOME (w2n dst, mm_local_bytes
    (\a. if a < LENGTH (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section)
         then EL a (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) else 0w) src 32)` by
    metis_tac[mm_local_payload_capture_store] >>
  qpat_x_assum `mode IN {CalldataMerge; DloadMerge}`
    (assume_tac o MATCH_MP mm_local_payload_opcodes) >>
  gvs[mm_local_group_captures_def] >> rpt gen_tac >> strip_tac
  >- (`j' = j` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
      gvs[]) >>
  qpat_x_assum `!q. q < LENGTH is /\ _ ==> _`
    (qspec_then `j'` mp_tac) >> simp[] >> strip_tac >>
  gvs[mm_local_payload_capture_def, mode_copy_opcode_def,
      mode_load_opcode_def]
QED

Theorem mm_local_payload_cached_ids_opcode[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  q <= LENGTH bb.bb_instructions /\
  FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state (TAKE q bb.bb_instructions)).ss_loads v = SOME src /\
  p < LENGTH bb.bb_instructions /\
  MEM (EL p bb.bb_instructions).inst_id
    (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id]) ==>
  (EL p bb.bb_instructions).inst_opcode = mode_load_opcode mode
Proof
  strip_tac >> Cases_on `dfg_get_def (dfg_build_function fn0) v` >> gvs[] >>
  `bb.bb_instructions = TAKE q bb.bb_instructions ++ DROP q bb.bb_instructions` by simp[] >>
  drule_all mm_local_prefix_cached_def_before_cut >> strip_tac >>
  `MEM x bb.bb_instructions` by metis_tac[MEM_APPEND] >>
  gvs[MEM_EL, mode_load_opcode_def] >>
  metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]
QED

Theorem mm_local_payload_scan_captures[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  n <= LENGTH bb.bb_instructions /\
  (!j. j < n ==> (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) = cd) /\
  (!j dst v src. j < n /\ (EL j bb.bb_instructions).inst_opcode = MSTORE /\
    (EL j bb.bb_instructions).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) ==>
  !t. t <= n ==>
    mm_local_scan_every
      (mm_local_group_captures bb.bb_instructions
        (mm_local_payload_capture mode bb.bb_instructions H n)
        (\a. if a < LENGTH cd then EL a cd else 0w))
      (FOLDL (scan_inst (dfg_build_function fn0) mode)
        empty_scan_state (TAKE t bb.bb_instructions))
Proof
  strip_tac >> Induct
  >- simp[mm_local_scan_every_def, empty_scan_state_def] >>
  strip_tac >> `t < n /\ t < LENGTH bb.bb_instructions /\ t <= n` by decide_tac >>
  simp[rich_listTheory.TAKE_SUC, FOLDL_APPEND] >>
  irule mm_local_inst_ordered_every >> conj_tac
  >- metis_tac[mm_local_group_captures_merge] >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst)
    (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE t bb.bb_instructions)).ss_copies` by
    (irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `(if mode = CalldataMerge then (H t).vs_call_ctx.cc_calldata else (H t).vs_data_section) = cd` by metis_tac[] >>
      pop_assum (fn th => pure_rewrite_tac[GSYM th]) >>
      irule mm_local_payload_store_group_captures >> simp[] >>
      rpt strip_tac >> `t <= LENGTH bb.bb_instructions` by decide_tac >>
      drule_all mm_local_payload_cached_ids_opcode >> simp[]) >>
  rpt strip_tac >>
  `(if mode = CalldataMerge then (H t).vs_call_ctx.cc_calldata else (H t).vs_data_section) = cd` by metis_tac[] >>
  pop_assum (fn th => pure_rewrite_tac[GSYM th]) >>
  irule mm_local_payload_bulk_group_captures >> simp[] >>
  qexists `t` >> simp[]
QED

Theorem mm_local_payload_store_extent[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  j < n /\ j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP src (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) ++ REPLICATE 32 0w))) /\
  (!q. q < LENGTH is /\ MEM (EL q is).inst_id lids ==>
    (EL q is).inst_opcode = mode_load_opcode mode) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++ lids |> ==>
  mm_local_group_coverage is n (mm_local_payload_capture mode is H n) c /\
  mm_local_group_endpoint is n (mm_local_payload_capture mode is H n) c
Proof
  strip_tac >>
  `mm_local_payload_capture mode is H n j = SOME (w2n dst, mm_local_bytes
    (\a. if a < LENGTH (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section)
         then EL a (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) else 0w) src 32)` by
    metis_tac[mm_local_payload_capture_store] >>
  `!q d bs. q < n /\ q < LENGTH is /\ MEM (EL q is).inst_id lids ==>
    mm_local_payload_capture mode is H n q <> SOME (d,bs)` by
    (rpt strip_tac >> `(EL q is).inst_opcode = mode_load_opcode mode` by metis_tac[] >>
     gvs[mm_local_payload_capture_def, mode_copy_opcode_def, mode_load_opcode_def]) >>
  gnvs[] >> conj_tac
  >- (irule mm_local_group_coverage_birth_extra >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule mm_local_group_endpoint_birth_extra >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem mm_local_payload_bulk_extent[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  j < n /\ j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  (EL j is).inst_opcode = mode_copy_opcode mode /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id] |> ==>
  mm_local_group_coverage is n (mm_local_payload_capture mode is H n) c /\
  mm_local_group_endpoint is n (mm_local_payload_capture mode is H n) c
Proof
  strip_tac >>
  `mm_local_payload_capture mode is H n j = SOME (w2n dst, mm_local_bytes
    (\a. if a < LENGTH (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section)
         then EL a (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) else 0w) (w2n src) (w2n len))` by
    metis_tac[mm_local_payload_capture_literal] >>
  gnvs[] >> conj_tac
  >- (irule mm_local_group_coverage_birth_extra >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule mm_local_group_endpoint_birth_extra >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem mm_local_payload_scan_extent[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  n <= LENGTH bb.bb_instructions /\
  (!j. j < n ==> (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) = cd) /\
  (!j dst v src. j < n /\ (EL j bb.bb_instructions).inst_opcode = MSTORE /\
    (EL j bb.bb_instructions).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) ==>
  !t. t <= n ==>
    mm_local_scan_every
      (\g. mm_local_group_coverage bb.bb_instructions n
          (mm_local_payload_capture mode bb.bb_instructions H n) g /\
        mm_local_group_endpoint bb.bb_instructions n
          (mm_local_payload_capture mode bb.bb_instructions H n) g)
      (FOLDL (scan_inst (dfg_build_function fn0) mode)
        empty_scan_state (TAKE t bb.bb_instructions))
Proof
  strip_tac >> Induct
  >- simp[mm_local_scan_every_def, empty_scan_state_def] >>
  strip_tac >> `t < n /\ t < LENGTH bb.bb_instructions /\ t <= n` by decide_tac >>
  simp[rich_listTheory.TAKE_SUC, FOLDL_APPEND] >>
  irule mm_local_inst_ordered_every >> conj_tac
  >- metis_tac[mm_local_group_coverage_merge, mm_local_group_endpoint_merge] >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst)
    (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE t bb.bb_instructions)).ss_copies` by
    (irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule mm_local_payload_store_extent >> simp[] >>
      qexistsl [`t`,`v`] >> simp[] >>
      rpt strip_tac >> `t <= LENGTH bb.bb_instructions` by decide_tac >>
      drule_all mm_local_payload_cached_ids_opcode >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule mm_local_payload_bulk_extent >> simp[] >>
  qexists `t` >> simp[]
QED

Theorem mm_local_payload_prefix_extend[local]:
  (!j. j <= r ==>
    (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
     else (H j).vs_data_section) = cd) /\
  (!j dst v src. j <= r /\ j < LENGTH is /\
    (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst dfg mode) empty_scan_state
      (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) ==>
  ?H'. (!j. j <= r ==> H' j = H j) /\
    (!j. (if mode = CalldataMerge then (H' j).vs_call_ctx.cc_calldata
          else (H' j).vs_data_section) = cd) /\
    (!j dst v src. j < LENGTH is /\
      (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP (FOLDL (scan_inst dfg mode) empty_scan_state
        (TAKE j is)).ss_loads v = SOME src ==>
      lookup_var v (H' j) = SOME (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP src cd ++ REPLICATE 32 0w))))
Proof
  strip_tac >>
  qexists `\j. if j <= r then H j else
    update_var (THE (operand_var (EL 1 (EL j is).inst_operands)))
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (THE (FLOOKUP
          (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE j is)).ss_loads
          (THE (operand_var (EL 1 (EL j is).inst_operands))))) cd ++ REPLICATE 32 0w)))
      (H r)` >>
  simp[] >> conj_tac
  >- (gen_tac >> Cases_on `j <= r`
      >- (simp[] >> metis_tac[]) >>
      `(if mode = CalldataMerge then (H r).vs_call_ctx.cc_calldata
        else (H r).vs_data_section) = cd` by
        (qpat_x_assum `!j. j <= r ==> _` (qspec_then `r` mp_tac) >> simp[]) >>
      simp[venomStateTheory.update_var_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `j <= r` >- (simp[] >> metis_tac[]) >>
  simp[operand_var_def, venomStateTheory.lookup_var_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem mm_local_payload_capture_history_cong[local]:
  (!j. j < n ==> H' j = H j) ==>
  mm_local_payload_capture mode is H' n = mm_local_payload_capture mode is H n
Proof
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `j` >>
  Cases_on `j < n /\ j < LENGTH is` >>
  simp[mm_local_payload_capture_def, mm_local_write_capture_def]
QED

Theorem mm_local_payload_final_extent[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  (!j. j < LENGTH bb.bb_instructions ==> (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata else (H j).vs_data_section) = cd) /\
  (!j dst v src. j < LENGTH bb.bb_instructions /\
    (EL j bb.bb_instructions).inst_opcode = MSTORE /\
    (EL j bb.bb_instructions).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed ==>
  mm_local_group_coverage bb.bb_instructions (LENGTH bb.bb_instructions)
    (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions)) g /\
  mm_local_group_endpoint bb.bb_instructions (LENGTH bb.bb_instructions)
    (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions)) g
Proof
  strip_tac >>
  `!t. t <= LENGTH bb.bb_instructions ==>
    mm_local_scan_every
      (\g. mm_local_group_coverage bb.bb_instructions (LENGTH bb.bb_instructions)
        (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions)) g /\
      mm_local_group_endpoint bb.bb_instructions (LENGTH bb.bb_instructions)
        (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions)) g)
      (FOLDL (scan_inst (dfg_build_function fn0) mode)
        empty_scan_state (TAKE t bb.bb_instructions))` by
    (gen_tac >> strip_tac >> irule mm_local_payload_scan_extent >>
     simp[] >> conj_tac >- (qexists `cd` >> simp[]) >>
     qexistsl [`index`,`k`,`sk`,`supply`] >> simp[]) >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions` mp_tac) >>
  gvs[scan_block_def, hard_barrier_def, mm_local_scan_every_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem mm_local_payload_final_certificate[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  (!j. j < LENGTH bb.bb_instructions ==>
    (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
     else (H j).vs_data_section) = cd) /\
  (!j dst v src. j < LENGTH bb.bb_instructions /\
    (EL j bb.bb_instructions).inst_opcode = MSTORE /\
    (EL j bb.bb_instructions).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed ==>
  mm_local_group_captures bb.bb_instructions
    (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions))
    (\a. if a < LENGTH cd then EL a cd else 0w) g /\
  mm_local_group_coverage bb.bb_instructions (LENGTH bb.bb_instructions)
    (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions)) g /\
  mm_local_group_endpoint bb.bb_instructions (LENGTH bb.bb_instructions)
    (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions)) g
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse conj_tac >- metis_tac[mm_local_payload_final_extent] >>
  `mm_local_scan_every
      (mm_local_group_captures bb.bb_instructions
        (mm_local_payload_capture mode bb.bb_instructions H (LENGTH bb.bb_instructions))
        (\a. if a < LENGTH cd then EL a cd else 0w))
      (FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state
        (TAKE (LENGTH bb.bb_instructions) bb.bb_instructions))` by
    (irule mm_local_payload_scan_captures >> simp[] >> metis_tac[]) >>
  fs[scan_block_def, hard_barrier_def, mm_local_scan_every_def, EVERY_MEM] >> metis_tac[]
QED

Theorem mm_local_payload_due_capture_indices[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  r < N /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r) ==>
  !j d bs.
    (MEM j (due ++ [r]) /\ mm_local_payload_capture mode is H N j = SOME (d,bs)) <=>
    (j < N /\ j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      mm_local_payload_capture mode is H N j = SOME (d,bs))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `due = FILTER (\j. j < r /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM (EL j is).inst_id g.cg_inst_ids) (COUNT_LIST r)` by
    (irule mm_local_canonical_due_group >> metis_tac[]) >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  rpt gen_tac >>
  Cases_on `mm_local_payload_capture mode is H N j` >> simp[] >>
  rename1 `mm_local_payload_capture mode is H N j = SOME w` >>
  `j < N /\ j < LENGTH is /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (Cases_on `j < N /\ j < LENGTH is` >>
     Cases_on `(EL j is).inst_opcode = mode_copy_opcode mode` >>
     Cases_on `(EL j is).inst_opcode = MSTORE` >>
     gvs[mm_local_payload_capture_def, mode_copy_opcode_def, mode_load_opcode_def]) >>
  Cases_on `MEM (EL j is).inst_id g.cg_inst_ids`
  >- (`j <= r` by metis_tac[mm_local_rep_position_max] >>
      Cases_on `j = r` >> gvs[MEM_APPEND, MEM_FILTER, MEM_COUNT_LIST] >> decide_tac) >>
  Cases_on `j = r` >> gvs[MEM_APPEND, MEM_FILTER, MEM_COUNT_LIST]
QED

Theorem mm_local_payload_due_captures_some[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  r < N /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r) /\
  (!j dst v src. j <= r /\ j < LENGTH is /\
    (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    IS_SOME (lookup_var v (H j))) ==>
  !j. MEM j (due ++ [r]) ==> IS_SOME (mm_local_payload_capture mode is H N j)
Proof
  strip_tac >>
  `due = FILTER (\j. j < r /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM (EL j is).inst_id g.cg_inst_ids) (COUNT_LIST r)` by
    (irule mm_local_canonical_due_group >> metis_tac[]) >>
  qpat_x_assum `due = FILTER (\j. mm_local_rep_index _ _ j = _) _` kall_tac >>
  drule_all mm_local_canonical_rep_write >> strip_tac >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  gen_tac >> strip_tac >>
  `j <= r /\ j < N /\ j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (Cases_on `j = r` >> gvs[MEM_APPEND, MEM_FILTER, MEM_COUNT_LIST] >> decide_tac) >>
  `MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed` by metis_tac[] >>
  drule_all mm_local_final_write_birth >> strip_tac
  >- simp[mm_local_payload_capture_def, mm_local_payload_opcodes, venomStateTheory.eval_operand_def] >>
  `IS_SOME (lookup_var v (H j))` by metis_tac[] >>
  Cases_on `lookup_var v (H j)` >> gvs[] >>
  simp[mm_local_payload_capture_def, mm_local_payload_opcodes, mm_local_write_capture_def,
    venomStateTheory.eval_operand_def]
QED

Theorem mm_local_payload_selected_capture_birth[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\ is = bb.bb_instructions /\
  j < N /\ j < LENGTH is /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
   else (H j).vs_data_section) = cd /\
  (!dst v src. (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\ FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) ==>
  ?c. mm_local_payload_capture mode is H N j = SOME
      (c.cg_dst, mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w)
        c.cg_src c.cg_length) /\
    ((?dst src len. (EL j is).inst_opcode = mode_copy_opcode mode /\
       (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
       c = <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
              cg_inst_ids := [(EL j is).inst_id]|>) \/
     (?dst v src. (EL j is).inst_opcode = MSTORE /\
       (EL j is).inst_operands = [Lit dst; Var v] /\
       FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
         empty_scan_state (TAKE j is)).ss_loads v = SOME src /\
       c = <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of
              NONE => [] | SOME li => [li.inst_id])|>))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all mm_local_final_write_birth >> strip_tac
  >- (qexists `<|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
          cg_inst_ids := [(EL j is).inst_id]|>` >> simp[] >>
      mp_tac (Q.INST [`n` |-> `N`]
        (SPEC_ALL mm_local_payload_capture_literal)) >> simp[]) >>
  qexists `<|cg_dst := w2n dst; cg_src := src; cg_length := 32;
    cg_inst_ids := [(EL j is).inst_id] ++
      (case dfg_get_def (dfg_build_function fn0) v of
         NONE => [] | SOME li => [li.inst_id])|>` >> simp[] >>
  mp_tac (Q.INST [`n` |-> `N`]
    (SPEC_ALL mm_local_payload_capture_store)) >> simp[] >> gvs[]
QED

Theorem mm_local_payload_capture_finite[local]:
  mode IN {CalldataMerge; DloadMerge} /\ is = bb.bb_instructions /\
  mm_local_payload_capture mode is H n j = SOME (d,bs) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
  static_mem_ok eom ctx fn (EL j is) (H j) /\ eom < dimword (:256) ==>
  d + LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ d + LENGTH bs <= eom)
Proof
  strip_tac >>
  `j < LENGTH is /\
   (EL j is).inst_opcode IN {MSTORE; CALLDATACOPY; DLOADBYTES}` by
    (Cases_on `mode` >> gvs[mm_local_payload_capture_def,
      mode_copy_opcode_def, AllCaseEqs()]) >>
  `~in_revert_forward fn (H j)` by
    (simp[contextCodegenRelTheory.in_revert_forward_def] >> strip_tac >>
     `get_instruction bb j = SOME (EL j is)` by
       gvs[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >>
     gvs[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  Cases_on `mode` >>
  gvs[mm_local_payload_capture_def, mode_copy_opcode_def,
    mm_local_write_capture_def, AllCaseEqs()] >>
  qpat_x_assum `static_mem_ok _ _ _ _ _` mp_tac >>
  simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    codegenRelTheory.sized_source_write_range_def,
    EVERY_APPEND, copyFwdEquivTheory.mcopy_data_length] >>
  strip_tac >> gvs[] >>
  mp_tac (Q.ISPEC `dst:256 word` wordsTheory.w2n_lt) >> simp[]
QED

Theorem mm_local_group_source_finite[local]:
  MEM g (scan_block dfg mode bb).ss_flushed ==> g.cg_src < dimword (:256)
Proof
  strip_tac >>
  `!n. n <= LENGTH bb.bb_instructions ==>
    mm_local_scan_every (\g. g.cg_src < dimword (:256))
      (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE n bb.bb_instructions))` by
    (Induct
     >- simp[mm_local_scan_every_def, empty_scan_state_def] >>
     strip_tac >>
     `n < LENGTH bb.bb_instructions /\ n <= LENGTH bb.bb_instructions` by decide_tac >>
     qpat_x_assum `n <= LENGTH bb.bb_instructions ==> _` mp_tac >>
     simp[] >> strip_tac >>
     simp[rich_listTheory.TAKE_SUC, FOLDL_APPEND] >>
     irule mm_local_inst_birth_every >> simp[copy_merge_def] >> conj_tac
     >- (rpt strip_tac >> drule mm_local_scan_lookup_origin >>
         disch_then (qx_choose_then `q` (qx_choose_then `w` strip_assume_tac)) >>
         gvs[] >> mp_tac (Q.ISPEC `w:256 word` wordsTheory.w2n_lt) >> simp[]) >>
     rpt strip_tac >> mp_tac (Q.ISPEC `src:256 word` wordsTheory.w2n_lt) >> simp[]) >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions` mp_tac) >>
  gvs[scan_block_def, hard_barrier_def, mm_local_scan_every_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem mm_local_payload_group_finite[local]:
  mm_local_group_coverage is n cap g /\ mm_local_group_endpoint is n cap g /\
  (!j d bs. j < n /\ j < LENGTH is /\
    MEM (EL j is).inst_id g.cg_inst_ids /\ cap j = SOME (d,bs) ==>
    d + LENGTH bs < dimword (:256) /\
    (LENGTH bs = 0 \/ d + LENGTH bs <= eom)) ==>
  g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
  (g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom)
Proof
  strip_tac >>
  `g.cg_dst + g.cg_length < dimword (:256)` by
    (fs[mm_local_group_endpoint_def] >> metis_tac[]) >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  Cases_on `g.cg_length = 0` >- simp[] >> simp[] >>
  `?j d bs. j < n /\ j < LENGTH is /\
    MEM (EL j is).inst_id g.cg_inst_ids /\ cap j = SOME (d,bs) /\
    d <= g.cg_dst + g.cg_length - 1 /\
    g.cg_dst + g.cg_length - 1 < d + LENGTH bs` by
    (qpat_x_assum `mm_local_group_coverage _ _ _ _` mp_tac >>
     pure_rewrite_tac[mm_local_group_coverage_def] >>
     disch_then (qspec_then `g.cg_dst + g.cg_length - 1` mp_tac) >>
     `g.cg_dst <= g.cg_dst + g.cg_length - 1 /\
       g.cg_dst + g.cg_length - 1 < g.cg_dst + g.cg_length` by decide_tac >>
     simp[] >> metis_tac[]) >>
  `LENGTH bs = 0 \/ d + LENGTH bs <= eom` by metis_tac[] >> decide_tac
QED

Theorem mm_local_payload_bytes_compatible[local]:
  (~copy_overwrites c (copy_dst_interval h) \/
    c.cg_src + h.cg_dst = c.cg_dst + h.cg_src) ==>
  mm_local_write_compatible c.cg_dst (mm_local_bytes B c.cg_src c.cg_length)
    h.cg_dst (mm_local_bytes B h.cg_src h.cg_length)
Proof
  strip_tac
  >- (gvs[copy_overwrites_def, copy_dst_interval_def,
        mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
        mmIntervalTheory.interval_end_def, arithmeticTheory.MAX_DEF,
        arithmeticTheory.MIN_DEF, mm_local_write_compatible_def,
        mm_local_bytes_length] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  simp[mm_local_write_compatible_def, mm_local_bytes_length] >>
  rpt strip_tac >> simp[mm_local_bytes_def, EL_GENLIST] >>
  AP_TERM_TAC >> decide_tac
QED

Theorem mm_local_payload_selected_captures_compatible[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\ r < N /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  MEM g2 (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL l is).inst_id g2.cg_inst_ids /\
  (!q. q <= r ==>
    (if mode = CalldataMerge then (H q).vs_call_ctx.cc_calldata
     else (H q).vs_data_section) = cd) /\
  (!q dst v src. q <= r /\ (EL q is).inst_opcode = MSTORE /\
    (EL q is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE q is)).ss_loads v = SOME src ==>
    lookup_var v (H q) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) /\
  mm_local_payload_capture mode is H N j = SOME (d,bs) /\
  mm_local_payload_capture mode is H N l = SOME (a,cs) ==>
  mm_local_write_compatible d bs a cs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `j < N /\ l < N /\ j < LENGTH is /\ l < LENGTH is /\ j <= r` by decide_tac >>
  `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
   (EL l is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (Cases_on `mode` >> gvs[mm_local_payload_capture_def,
      mode_copy_opcode_def, AllCaseEqs()]) >>
  mp_tac (SPEC_ALL mm_local_payload_selected_capture_birth) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `c` (CONJUNCTS_THEN assume_tac)) >>
  mp_tac (Q.INST [`j` |-> `l`,`g` |-> `g2`]
    (SPEC_ALL mm_local_payload_selected_capture_birth)) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `h` (CONJUNCTS_THEN assume_tac)) >>
  `d = c.cg_dst /\ bs = mm_local_bytes
     (\a. if a < LENGTH cd then EL a cd else 0w) c.cg_src c.cg_length` by
    (qpat_x_assum `mm_local_payload_capture mode is H N j = SOME (d,bs)` mp_tac >> simp[]) >>
  `a = h.cg_dst /\ cs = mm_local_bytes
     (\a. if a < LENGTH cd then EL a cd else 0w) h.cg_src h.cg_length` by
    (qpat_x_assum `mm_local_payload_capture mode is H N l = SOME (a,cs)` mp_tac >> simp[]) >>
  mp_tac (Q.INST
    [`s0` |-> `FOLDL (scan_inst (dfg_build_function fn0) mode)
        empty_scan_state (TAKE j is)`,
     `ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) mode)
        empty_scan_state (TAKE l is)`]
    (SPEC_ALL mm_local_indexed_selected_hazard_geometry)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  asm_rewrite_tac[] >> irule mm_local_payload_bytes_compatible >> simp[]
QED

Theorem mm_local_payload_pending_compatible[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  cap = mm_local_payload_capture mode is H (LENGTH is) /\
  MEM j (mm_local_pending_indices is gs n) /\ j < l /\ l <= n /\
  MEM h gs /\ MEM (EL l is).inst_id h.cg_inst_ids /\
  (!q. (if mode = CalldataMerge then (H q).vs_call_ctx.cc_calldata
         else (H q).vs_data_section) = cd) /\
  (!q dst v src. q < LENGTH is /\ (EL q is).inst_opcode = MSTORE /\
    (EL q is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE q is)).ss_loads v = SOME src ==>
    lookup_var v (H q) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) /\
  cap j = SOME (d,bs) /\ cap l = SOME (a,cs) ==>
  mm_local_write_compatible d bs a cs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `l <= r` by decide_tac >>
  mp_tac (Q.INST [`g2` |-> `h`, `N` |-> `LENGTH is`]
    (SPEC_ALL mm_local_payload_selected_captures_compatible)) >>
  impl_tac >- (simp[] >> rpt strip_tac >>
    metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  simp[]
QED

Theorem mm_local_payload_representative_pending_suc[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  (EL r is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  mm_local_pending_indices is gs (SUC r) =
    FILTER (\j. mm_local_rep_index is gs j <> r) (mm_local_pending_indices is gs r)
Proof
  strip_tac >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `!j h q. j < LENGTH is /\
      (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\ MEM h gs /\ MEM (EL j is).inst_id h.cg_inst_ids /\
      q < LENGTH is /\ rep_of_group is h = SOME ((EL q is).inst_id,h) ==>
      mm_local_rep_index is gs j = q` by
    (rpt strip_tac >> qpat_assum `is = _` SUBST1_TAC >>
     irule mm_local_rep_index_eq >> metis_tac[]) >>
  `~MEM r (mm_local_pending_indices is gs (SUC r))` by
    (strip_tac >>
     qpat_x_assum `MEM r (mm_local_pending_indices _ _ _)`
       (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
     rename1 `rep_of_group is h = SOME ((EL rr is).inst_id,h)` >>
     `mm_local_rep_index is gs r = r` by metis_tac[] >>
     `mm_local_rep_index is gs r = rr` by metis_tac[] >> decide_tac) >>
  `mm_local_pending_indices is gs (SUC r) =
    FILTER (\j. j < r) (mm_local_pending_indices is gs (SUC r))` by
    (sym_tac >> rewrite_tac[FILTER_EQ_ID, EVERY_MEM] >> rpt strip_tac >>
     rename1 `MEM j (mm_local_pending_indices is gs (SUC r))` >>
     `j < SUC r` by (drule (iffLR mm_local_pending_indices_mem) >> simp[]) >>
     `j <> r` by metis_tac[] >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[NoAsms, mm_local_pending_indices_def, FILTER_FILTER,
    rich_listTheory.COUNT_LIST_SNOC, rich_listTheory.SNOC_APPEND, FILTER_APPEND] >>
  IF_CASES_TAC >> simp[NoAsms] >>
  rewrite_tac[rich_listTheory.FILTER_EQ] >> qx_gen_tac `j` >>
  simp[NoAsms, MEM_COUNT_LIST] >> strip_tac >>
  `j < LENGTH is` by decide_tac >>
  eq_tac
  >- (strip_tac >>
      rename1 `rep_of_group is h = SOME ((EL rr is).inst_id,h)` >>
      `mm_local_rep_index is gs j = rr` by
        (qpat_x_assum `!j h q. _` (qspecl_then [`j`,`h`,`rr`] mp_tac) >> simp[]) >>
      `mm_local_rep_index is gs j <> r` by decide_tac >>
      simp[] >> qexistsl [`h`,`rr`] >> gvs[]) >>
  strip_tac >>
  rename1 `rep_of_group is h = SOME ((EL rr is).inst_id,h)` >>
  `mm_local_rep_index is gs j = rr` by
        (qpat_x_assum `!j h q. _` (qspecl_then [`j`,`h`,`rr`] mp_tac) >> simp[]) >>
  `SUC r <= rr` by decide_tac >>
  simp[] >> qexistsl [`h`,`rr`] >>
  qpat_x_assum `is = _` (fn th => SUBST_ALL_TAC (SYM th)) >>
  qpat_x_assum `gs = _` (fn th => SUBST_ALL_TAC (SYM th)) >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem mm_local_memzero_history_producer[local]:
  fn_inst_wf fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  is = bb.bb_instructions /\ dfg = dfg_build_function fn /\
  h <= n /\ n < LENGTH is /\
  LENGTH (H h).vs_call_ctx.cc_calldata < dimword (:256) /\
  (!q. h <= q /\ q < n ==>
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
  (!v producer w.
    dfg_get_def dfg v = SOME producer /\
    producer.inst_opcode = CALLDATASIZE /\ lookup_var v (H h) = SOME w ==>
    w = n2w (LENGTH (H h).vs_call_ctx.cc_calldata)) ==>
  (!j. h <= j /\ j <= n ==>
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  (!j dst v len. h <= j /\ j < n /\
    is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256))
Proof
  strip_tac >>
  `!j. h <= j /\ j <= n ==>
    (H j).vs_call_ctx.cc_calldata = (H h).vs_call_ctx.cc_calldata /\
    (!v producer w.
      dfg_get_def (dfg_build_function fn) v = SOME producer /\
      producer.inst_opcode = CALLDATASIZE /\ lookup_var v (H j) = SOME w ==>
      w = n2w (LENGTH (H j).vs_call_ctx.cc_calldata))` by
    (rpt gen_tac >> strip_tac >>
     irule venomExecutionReplayPropsTheory.cds_history_value >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
  `j <= n` by decide_tac >>
  `LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)` by metis_tac[] >>
  simp[] >>
  `?u. step_inst fuel ctx (EL j is) (H j) = OK u` by metis_tac[] >>
  `(EL j is).inst_opcode = CALLDATACOPY /\
   ?producer. dfg_get_def dfg v = SOME producer /\
              producer.inst_opcode = CALLDATASIZE` by
    (gvs[is_calldatasize_copy_def, operand_var_def,
         operand_lit_val_def, AllCaseEqs()] >>
     Cases_on `dfg_get_def (dfg_build_function fn) v` >> gvs[]) >>
  `?w. lookup_var v (H j) = SOME w` by
    (Cases_on `lookup_var v (H j)` >> simp[] >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     asm_simp_tac (srw_ss())
       [venomExecSemanticsTheory.step_inst_def,
        venomExecSemanticsTheory.step_inst_base_opcode_eqs,
        venomStateTheory.eval_operand_def, AllCaseEqs()]) >>
  metis_tac[]
QED

Theorem mm_local_zero_run_block_pair[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  bb = EL index fn0.fn_blocks /\ dfg = dfg_build_function fn0 /\
  is = bb.bb_instructions /\ gs = (scan_block_memzero dfg bb).mz_flushed /\
  h = phi_prefix_length is /\
  f = apply_memzero_inst_supply (nop_ids_of_groups dfg Mem2Mem is gs)
    (rep_map_of_groups is gs) /\
  transform_block_memzero_supply dfg supply bb = (bb',supply') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  state_equiv excluded (s with vs_inst_idx := 0) (t0 with vs_inst_idx := 0) /\
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
    (run_block fuel ctx bb s) (run_block fuel ctx bb' t0) /\
  EVERY (\((p,d',id),fn,i,t). p = [] ==> static_mem_ok eom ctx fn i t)
    (case eval_phis t0 bb'.bb_instructions of
       OK sp' => trace_block [] (SUC d) fuel ctx fn' bb'
         (sp' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | _ => [])
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
    (!u. eval_phis u bb'.bb_instructions = eval_phis u is)` by
    (gvs[] >> metis_tac[dftIndexedExecTheory.dft_phi_prefix_append,
      dftIndexedExecTheory.dft_eval_phis_append,
      analysisSimProofsBaseTheory.phi_prefix_all_phi, TAKE_DROP]) >>
  irule venomExecutionReplayPropsTheory.run_block_pair >>
  asm_rewrite_tac[] >>
  qx_gen_tac `sp` >> strip_tac >>
  `eval_phis s is = OK sp` by metis_tac[] >>
  `?tp. eval_phis t0 is = OK tp /\
    state_equiv excluded (sp with vs_inst_idx := h) (tp with vs_inst_idx := h)` by
    (irule venomExecutionReplayPropsTheory.phi_entry_pair >> conj_tac
     >- (simp[EVERY_MEM] >> metis_tac[]) >>
     qexists_tac `s` >> asm_rewrite_tac[]) >>
  qexists_tac `tp` >> conj_tac >- metis_tac[] >>
  `sp.vs_current_bb = bb.bb_label` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `eval_phis s bb.bb_instructions = OK sp` by metis_tac[] >>
  drule_all dftGasFromListTraceDefsTheory.trace_blocks_enter >>
  disch_then (fn th => fs[th, EVERY_APPEND]) >>
  `~(?err. exec_block fuel ctx bb (sp with vs_inst_idx := h) = Error err)` by
    (qpat_x_assum `!err. run_block_entry _ _ _ _ <> Error err` mp_tac >>
     simp[venomExecSemanticsTheory.run_block_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `sp with vs_inst_idx := h`,
    `t0` |-> `tp with vs_inst_idx := h`, `d` |-> `SUC d`]
    mm_local_zero_post_phi_result) >>
  impl_tac >- (
    qpat_x_assum `h = _` SUBST_ALL_TAC >>
    qpat_x_assum `is = _` SUBST_ALL_TAC >>
    qpat_x_assum `bb = _` SUBST_ALL_TAC >>
    qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
    asm_simp_tac (srw_ss()) [] >>
    qpat_assum `s.vs_current_bb = _` (fn th => rewrite_tac[GSYM th]) >>
    asm_rewrite_tac[] >> metis_tac[]) >>
  disch_tac >>
  mp_tac (Q.INST [`s` |-> `sp with vs_inst_idx := h`,
    `t0` |-> `tp with vs_inst_idx := h`, `d` |-> `SUC d`]
    mm_local_zero_post_phi_trace) >>
  impl_tac >- (
    qpat_x_assum `h = _` SUBST_ALL_TAC >>
    qpat_x_assum `is = _` SUBST_ALL_TAC >>
    qpat_x_assum `bb = _` SUBST_ALL_TAC >>
    qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
    asm_simp_tac (srw_ss()) [] >>
    qpat_assum `s.vs_current_bb = _` (fn th => rewrite_tac[GSYM th]) >>
    asm_rewrite_tac[] >> metis_tac[]) >>
  strip_tac >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  qpat_x_assum `is = _` SUBST_ALL_TAC >>
  qpat_x_assum `bb = _` SUBST_ALL_TAC >>
  qpat_x_assum `fn' = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[]
QED

Theorem mm_local_zero_trace_history_producer[local]:
  fn_inst_wf fn0 /\ ssa_form fn0 /\
  lookup_block s.vs_current_bb fn0.fn_blocks = SOME bb /\
  is = bb.bb_instructions /\ dfg = dfg_build_function fn0 /\
  h = phi_prefix_length is /\
  EVERY (\((p,d',id),f,i,t). p = [] ==>
    static_mem_ok eom ctx f i t /\
    LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
    (fn_inst_wf f /\ ssa_form f ==>
      !v producer w.
        dfg_get_def (dfg_build_function f) v = SOME producer /\
        producer.inst_opcode = CALLDATASIZE /\ lookup_var v t = SOME w ==>
        w = n2w (LENGTH t.vs_call_ctx.cc_calldata)))
    (trace_blocks [] d (SUC fuel) ctx fn0 s) ==>
  !sp n H. eval_phis s is = OK sp /\
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
      LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM bb fn0.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `h < LENGTH is` by decide_tac >>
  `eval_phis s bb.bb_instructions = OK sp` by metis_tac[] >>
  mp_tac (Q.INST [`p` |-> `[]`, `fn` |-> `fn0`]
    dftGasFromListTraceDefsTheory.trace_blocks_enter) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (fn th =>
    qpat_x_assum `EVERY _ (trace_blocks _ _ _ _ _ _)`
      (mp_tac o REWRITE_RULE [th])) >>
  simp[EVERY_APPEND] >> strip_tac >>
  `get_instruction bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_inst_idx = SOME (EL h is)` by
    (gvs[venomInstTheory.get_instruction_def]) >>
  drule dftGasFromListTraceDefsTheory.trace_block_visit >>
  disch_then (fn th =>
    qpat_x_assum `EVERY _ (trace_block _ _ _ _ _ _ _)`
      (mp_tac o REWRITE_RULE [th])) >>
  simp[EVERY_APPEND] >> strip_tac >>
  `LENGTH (H h).vs_call_ctx.cc_calldata < dimword (:256) /\
   (!v producer w.
     dfg_get_def dfg v = SOME producer /\
     producer.inst_opcode = CALLDATASIZE /\ lookup_var v (H h) = SOME w ==>
     w = n2w (LENGTH (H h).vs_call_ctx.cc_calldata))` by
    (gvs[] >> metis_tac[]) >>
  mp_tac (Q.INST [`fn` |-> `fn0`] mm_local_memzero_history_producer) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >> simp[]
QED

Theorem mm_local_safe_flatmap_interval[local]:
  !m n es t out es' pre.
  n + m <= LENGTH is /\
  (!j pref sj tj chunk sj'. n <= j /\ j < n + m /\
    mm_flat_map_supply f supply (TAKE j is) = (pref,sj) /\
    Inv j (LENGTH pref) sj tj /\ f sj (EL j is) = (chunk,sj') ==>
    ?tj'. mm_local_safe_exec_prefix P fuel ctx chunk tj tj' /\
      Inv (SUC j) (LENGTH pref + LENGTH chunk) sj' tj') /\
  mm_flat_map_supply f supply (TAKE n is) = (pre,es) /\
  Inv n (LENGTH pre) es t /\
  mm_flat_map_supply f es (TAKE m (DROP n is)) = (out,es') ==>
  ?t'. mm_local_safe_exec_prefix P fuel ctx out t t' /\
    Inv (n + m) (LENGTH pre + LENGTH out) es' t'
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
  `?t1. mm_local_safe_exec_prefix P fuel ctx chunk t t1 /\
    Inv (SUC n) (LENGTH pre + LENGTH chunk) es1 t1` by
    (qpat_x_assum `!j pref sj tj chunk sj'. _`
      (qspecl_then [`n`,`pre`,`es`,`t`,`chunk`,`es1`] mp_tac) >> simp[]) >>
  `mm_flat_map_supply f supply (TAKE (SUC n) is) = (pre ++ chunk,es1)` by
    (`TAKE (SUC n) is = TAKE n is ++ [EL n is]` by
       simp[rich_listTheory.TAKE_SUC_BY_TAKE, listTheory.SNOC_APPEND] >>
     qpat_assum `TAKE (SUC n) is = _` (fn th => once_rewrite_tac[th]) >>
     irule mm_local_flat_map_supply_append >> qexists_tac `es` >>
     simp[mm_flat_map_supply_def]) >>
  qpat_x_assum `!n es t out es' pre. _`
    (qspecl_then [`SUC n`,`es1`,`t1`,`tail`,`es2`,`pre ++ chunk`] mp_tac) >>
  (impl_tac >- (gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >>
    rpt strip_tac >> metis_tac[])) >>
  strip_tac >> qexists_tac `t'` >> conj_tac
  >- (asm_rewrite_tac[] >> rewrite_tac[mm_local_safe_exec_prefix_append] >>
      qexists_tac `t1` >> simp[]) >>
  `n + SUC m = SUC n + m` by decide_tac >>
  qpat_x_assum `Inv (SUC n + m) _ _ _` mp_tac >>
  asm_rewrite_tac[LENGTH_APPEND, arithmeticTheory.ADD_ASSOC]
QED

Theorem mm_local_mode_stopping_unchanged[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  (is_terminator (EL n is).inst_opcode \/
    ~(?u. step_inst fuel ctx (EL n is) s = OK u)) /\
  ~(?err. step_inst fuel ctx (EL n is) s = Error err) ==>
  (!es. apply_groups_inst_supply mode ns rs es (EL n is) = ([EL n is],es)) /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(EL n is).inst_opcode <> MSTORE /\
   (EL n is).inst_opcode <> mode_copy_opcode mode /\
   (EL n is).inst_opcode <> mode_load_opcode mode` by
    (Cases_on `is_terminator (EL n is).inst_opcode`
     >- (Cases_on `mode` >>
         gvs[mode_copy_opcode_def, mode_load_opcode_def] >>
         metis_tac[venomInstTheory.is_terminator_def]) >>
     Cases_on `(EL n is).inst_opcode = INVOKE`
     >- (Cases_on `mode` >> gvs[mode_copy_opcode_def, mode_load_opcode_def]) >>
     Cases_on `step_inst fuel ctx (EL n is) s` >> gvs[]
     >- (drule opcodeClassTheory.step_inst_halt_opcodes >> strip_tac >>
         Cases_on `mode` >> gvs[mode_copy_opcode_def, mode_load_opcode_def])
     >- (drule opcodeClassTheory.step_inst_abort_opcodes >> strip_tac >>
         Cases_on `mode` >> gvs[mode_copy_opcode_def, mode_load_opcode_def])
     >- (gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
         drule opcodeClassTheory.step_inst_base_intret_opcodes >> strip_tac >>
         Cases_on `mode` >> gvs[mode_copy_opcode_def, mode_load_opcode_def])) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `!es. apply_groups_inst_supply mode ns rs es (EL n is) = ([EL n is],es)` by
    (gvs[] >> irule mm_local_prefix_nonselected_unchanged >> simp[EL_MEM] >> metis_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >> qx_gen_tac `v` >> disch_tac >>
  irule (cj 3 mm_local_retained_operand_protected) >>
  gvs[] >> metis_tac[EL_MEM, venomWfPropsTheory.operand_var_in_inst_uses]
QED

Theorem mm_local_mode_terminal_pending_empty[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  n < LENGTH is /\ SUC n = LENGTH is /\
  is_terminator (EL n is).inst_opcode ==>
  mm_local_pending_indices is gs n = []
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `(EL n is).inst_opcode <> MSTORE /\
   (EL n is).inst_opcode <> mode_copy_opcode mode /\
   (EL n is).inst_opcode <> mode_load_opcode mode` by
    (Cases_on `mode` >> gvs[mode_copy_opcode_def, mode_load_opcode_def] >>
     metis_tac[venomInstTheory.is_terminator_def]) >>
  `!g. MEM g gs ==> ~MEM (EL n is).inst_id g.cg_inst_ids` by
    metis_tac[mm_local_prefix_nonselected_group_absent] >>
  `!j. ~MEM j (mm_local_pending_indices is gs n)` suffices_by
    (Cases_on `mm_local_pending_indices is gs n` >> simp[] >> metis_tac[]) >>
  qx_gen_tac `j` >> rewrite_tac[mm_local_pending_indices_mem] >> strip_tac >>
  `r = n` by decide_tac >> metis_tac[mm_local_rep_member]
QED

Theorem mm_local_zero_function_correct:
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  transform_block_memzero_supply (dfg_build_function fn0) supply
    (EL index fn0.fn_blocks) = (bb',supply') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  fn_entry_state fn0 s /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eom < dimword (:256) /\
  EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn0 s) /\
  ~(?err. run_function fuel ctx fn0 s = Error err) ==>
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (run_function fuel ctx fn0 s) (run_function fuel ctx fn' s) /\
  EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn' s)
Proof
  strip_tac >>
  qabbrev_tac `excluded = {v | ~MEM v supply.irs_used_vars}` >>
  qabbrev_tac `R = \a b. state_equiv excluded
    (a with vs_inst_idx := 0) (b with vs_inst_idx := 0)` >>
  qabbrev_tac `P = \((p,d,id),f,i,t):list_visit.
    p = [] ==> static_mem_ok eom ctx f i t` >>
  qabbrev_tac `Q = \((p,d,id),f,i,t):list_visit. p = [] ==>
    static_mem_ok eom ctx f i t /\
    LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
    (fn_inst_wf f /\ ssa_form f ==>
      !v producer w.
        dfg_get_def (dfg_build_function f) v = SOME producer /\
        producer.inst_opcode = CALLDATASIZE /\ lookup_var v t = SOME w ==>
        w = n2w (LENGTH t.vs_call_ctx.cc_calldata))` >>
  `EVERY Q (trace_function fuel ctx fn0 s)` by
    (fs[Abbr `Q`, Abbr `P`, EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> gvs[] >>
     drule_all venomExecutionReplayPropsTheory.cds_trace >> strip_tac >> simp[] >> metis_tac[]) >>
  `fn_entry_label fn' = fn_entry_label fn0` by
    (mp_tac (Q.INST [`k` |-> `0`, `bb` |-> `EL index fn0.fn_blocks`,
       `sk` |-> `supply`, `sk'` |-> `supply'`] mm_local_phase_structure) >>
     simp[mm_local_prefix_zero, mm_local_phase_def] >> metis_tac[]) >>
  `bb'.bb_label = (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mmSupplyWfProofsTheory.transform_block_memzero_supply_label] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn0.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `!lbl. lookup_block lbl fn'.fn_blocks =
    if lbl = bb'.bb_label then SOME bb' else lookup_block lbl fn0.fn_blocks` by
    (gen_tac >>
     qspecl_then [`fn0.fn_blocks`,`index`,`bb'`,`lbl`] mp_tac
       venomTransformStructurePropsTheory.lookup_block_lupdate >> simp[]) >>
  `!n d a b. R a b /\ EVERY Q (trace_blocks [] d n ctx fn0 a) /\
    ~(?err. run_blocks n ctx fn0 a = Error err) ==>
    lift_result R (execution_equiv excluded) revert_equiv
      (run_blocks n ctx fn0 a) (run_blocks n ctx fn' b) /\
    EVERY P (trace_blocks [] d n ctx fn' b)` by
    (mp_tac (Q.INST [`fn` |-> `fn0`, `Rt` |-> `execution_equiv excluded`,
       `Ra` |-> `revert_equiv`] venomExecutionReplayPropsTheory.blocks_pair) >>
     (impl_tac >- (conj_tac
     >- (simp[Abbr `R`, state_equiv_def, execution_equiv_def,
           stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def]) >>
     map_every qx_gen_tac [`fuel1`,`d`,`a`,`b`,`bb`] >> strip_tac >>
     `a.vs_current_bb = b.vs_current_bb` by
       fs[Abbr `R`, state_equiv_def] >>
     `MEM bb fn0.fn_blocks /\ bb.bb_label = a.vs_current_bb` by
       metis_tac[venomExecProofsTheory.lookup_block_MEM,
         venomExecProofsTheory.lookup_block_label] >>
     `!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==>
       v NOTIN excluded` by
       (simp[Abbr `excluded`] >> metis_tac[venomTransformStructurePropsTheory.supply_operand]) >>
     `EVERY (\((p,d',id),f,i,t). p=[] ==> static_mem_ok eom ctx f i t)
       (trace_blocks [] d (SUC fuel1) ctx fn0 a)` by
       (fs[Abbr `Q`, Abbr `P`, EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
     Cases_on `a.vs_current_bb = bb'.bb_label`
     >- (`lookup_block a.vs_current_bb fn0.fn_blocks =
            SOME (EL index fn0.fn_blocks)` by
           (irule venomExecProofsTheory.MEM_lookup_block >>
            simp[EL_MEM] >> metis_tac[]) >>
         `bb = EL index fn0.fn_blocks` by metis_tac[optionTheory.SOME_11] >>
         `b.vs_current_bb = bb'.bb_label` by metis_tac[] >>
         qexists_tac `bb'` >> conj_tac >- simp[] >>
         mp_tac (Q.INST [`s` |-> `a`, `fuel` |-> `fuel1`,
           `is` |-> `bb.bb_instructions`, `dfg` |-> `dfg_build_function fn0`,
           `h` |-> `phi_prefix_length bb.bb_instructions`]
           mm_local_zero_trace_history_producer) >>
         (impl_tac >- (fs[Abbr `Q`, wf_ssa_def] >> simp[])) >>
         strip_tac >>
         mp_tac (Q.INST [`s` |-> `a`, `t0` |-> `b`, `fuel` |-> `fuel1`,
           `dfg` |-> `dfg_build_function fn0`, `is` |-> `bb.bb_instructions`,
           `gs` |-> `(scan_block_memzero (dfg_build_function fn0) bb).mz_flushed`,
           `h` |-> `phi_prefix_length bb.bb_instructions`,
           `f` |-> `apply_memzero_inst_supply
             (nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
               (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
             (rep_map_of_groups bb.bb_instructions
               (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)`]
           mm_local_zero_run_block_pair) >>
         (impl_tac >- (asm_rewrite_tac[] >>
           fs[Abbr `R`, Abbr `excluded`] >> metis_tac[])) >>
         simp[Abbr `R`, Abbr `P`]) >>
     `b.vs_current_bb <> bb'.bb_label` by metis_tac[] >>
     `lookup_block b.vs_current_bb fn'.fn_blocks = SOME bb` by
       (qpat_assum `!lbl. lookup_block lbl fn'.fn_blocks = _`
          (qspec_then `b.vs_current_bb` mp_tac) >> simp[] >> metis_tac[]) >>
     qexists_tac `bb` >> simp[] >>
     mp_tac (Q.INST [`s` |-> `a`, `t` |-> `b`, `fuel` |-> `fuel1`, `fn` |-> `fn0`]
       venomExecutionReplayPropsTheory.same_run_block_correct) >>
     (impl_tac >- (asm_rewrite_tac[] >> fs[Abbr `R`])) >>
     simp[Abbr `R`, Abbr `P`])) >> simp[]) >>
  mp_tac (Q.INST [`fn` |-> `fn0`, `Rt` |-> `execution_equiv excluded`,
    `Ra` |-> `revert_equiv`] venomExecutionReplayPropsTheory.function_pair) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    simp[Abbr `R`, state_equiv_def, execution_equiv_def,
      stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def])) >>
  disch_then (qspecl_then [`fuel`,`s`,`s`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    simp[Abbr `R`, state_equiv_def, execution_equiv_def])) >>
  simp[Abbr `P`] >> metis_tac[venomExecutionReplayPropsTheory.function_forget_vars]
QED

Theorem mm_local_mode_entry_operands[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  transform_block_mode_supply (dfg_build_function fn0) mode sk bb = (bb',sk') /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  deleted = {v | ?q. MEM q bb.bb_instructions /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} ==>
  EVERY (\i. i.inst_opcode = PHI ==>
    !v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) bb.bb_instructions /\
  (!cb i v. MEM cb fn0.fn_blocks /\ cb.bb_label <> bb.bb_label /\
    MEM i cb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v NOTIN excluded)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `fn_inst_wf (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    metis_tac[mm_local_prefix_inst_wf] >>
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by
    (simp[MEM_EL] >> qexists `index` >> simp[EL_LUPDATE]) >>
  `!q. MEM q bb.bb_instructions ==> inst_wf q` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM (EL index fn0.fn_blocks) fn0.fn_blocks` by simp[EL_MEM] >>
  `!i v. MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
    MEM (Var v) i.inst_operands ==> MEM v sk.irs_used_vars` by
    (rpt strip_tac >>
     `MEM i (EL index fn0.fn_blocks).bb_instructions` by
       metis_tac[mm_local_prefix_phi_origin] >>
     `MEM v supply.irs_used_vars` by metis_tac[venomTransformStructurePropsTheory.supply_operand] >>
     metis_tac[mm_local_prefix_used_vars_mono]) >>
  conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      `MEM v sk.irs_used_vars` by metis_tac[] >>
      qsuff_tac `v NOTIN deleted` >-
        (qpat_assum `excluded = _` (fn th => simp[th])) >>
      strip_tac >>
      `?q. MEM q bb.bb_instructions /\ MEM q.inst_id ns /\ MEM v q.inst_outputs` by
        (qpat_x_assum `v IN deleted` mp_tac >>
         qpat_assum `deleted = _` (fn th => rewrite_tac[th,pred_setTheory.IN_GSPEC]) >>
         simp[]) >>
      `MEM v (venomInst$inst_uses i)` by
        metis_tac[venomWfPropsTheory.operand_var_in_inst_uses] >>
      `apply_groups_inst_supply mode
        (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
          (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
        (rep_map_of_groups bb.bb_instructions
          (scan_block (dfg_build_function fn0) mode bb).ss_flushed) sk i = ([i],sk)` by
        (mp_tac (Q.INST [`q` |-> `i`] mm_local_prefix_nonselected_unchanged) >>
         (impl_tac >- (Cases_on `mode` >>
           simp[mode_load_opcode_def,mode_copy_opcode_def])) >>
         disch_then (qspec_then `sk` ACCEPT_TAC)) >>
      `~MEM q.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)` by
        (mp_tac (Q.INST [`u` |-> `i`, `s` |-> `sk`, `out` |-> `[i]`, `t` |-> `sk`]
           mm_local_surviving_demand_not_deleted) >> simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `MEM v supply.irs_used_vars` by metis_tac[venomTransformStructurePropsTheory.supply_operand] >>
  `MEM v sk.irs_used_vars` by metis_tac[mm_local_prefix_used_vars_mono] >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def,irSupplyTheory.fn_ir_inst_ids_def,
       irSupplyTheory.block_ir_inst_ids_def,EVERY_MEM,MEM_FLAT,MEM_MAP] >>
     metis_tac[EL_MEM,MEM_MAP]) >>
  `bb.bb_label = (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mm_local_prefix_wf_last,wf_ssa_def] >>
  `~MEM i (EL index fn0.fn_blocks).bb_instructions` by
    (strip_tac >>
     `cb = EL index fn0.fn_blocks` by
       (qspecl_then [`\b. MAP (\inst. inst.inst_id) b.bb_instructions`,
          `fn0.fn_blocks`,`cb`,`EL index fn0.fn_blocks`,`i.inst_id`] mp_tac
          venomWfPropsTheory.all_distinct_flat_map_inj >>
        (impl_tac >- (simp[MEM_MAP,PULL_EXISTS] >>
          fs[wf_function_def,fn_inst_ids_distinct_def] >> metis_tac[])) >> simp[]) >>
     metis_tac[]) >>
  `MEM i (fn_insts fn0)` by
    metis_tac[venomFnInstsProofsTheory.MEM_fn_insts] >>
  `MEM v (venomInst$inst_uses i)` by
    metis_tac[venomWfPropsTheory.operand_var_in_inst_uses] >>
  mp_tac (Q.INST [`cc` |-> `bb'`, `t` |-> `sk'`, `excluded` |-> `deleted`]
    mm_local_mode_demands_exclude_deleted) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `v NOTIN deleted` by metis_tac[] >>
  qpat_assum `excluded = _` (fn th => fs[th])
QED

Theorem mm_local_nop_group_member[local]:
  MEM id (nop_ids_of_groups dfg mode is gs) ==>
  ?g. MEM g gs /\ MEM id g.cg_inst_ids
Proof
  simp[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >> strip_tac >> gvs[] >>
  rename1 `MEM id (nop_ids_of_group dfg mode is g)` >>
  qexists `g` >> simp[] >>
  qpat_x_assum `MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
  simp[nop_ids_of_group_def] >>
  Cases_on `REVERSE (sort_ids_by_block is g.cg_inst_ids)` >>
  simp[MEM_FILTER] >> strip_tac >>
  `MEM id (REVERSE (sort_ids_by_block is g.cg_inst_ids))` by
    (pure_asm_rewrite_tac[MEM] >> simp[]) >>
  gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER]
QED

Theorem mm_local_prefix_retained_write_unselected[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode is gs /\
  rs = rep_map_of_groups is gs /\
  ~MEM (EL n is).inst_id ns /\ ALOOKUP rs (EL n is).inst_id = NONE /\
  (EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
  ~(?g. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids)
Proof
  strip_tac >> strip_tac >>
  `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `!v li. dfg_get_def (dfg_build_function fn0) v = SOME li ==>
    li.inst_id <> (EL n is).inst_id` by metis_tac[mm_local_prefix_write_not_def] >>
  `!rep. rep_pin_id (dfg_build_function fn0) mode rep g <> SOME (EL n is).inst_id` by
    (simp[rep_pin_id_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all mm_local_prefix_write_origin >> strip_tac >>
  rename1 `MEM orig (EL index fn0.fn_blocks).bb_instructions` >>
  `dfg_get_inst_by_id (dfg_build_function fn0) orig.inst_id = SOME orig` by
    (irule venomTransformStructurePropsTheory.function_ids_exact >> simp[] >>
     irule venomFnInstsProofsTheory.MEM_fn_insts >>
     qexists `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
  `~MEM (EL n is).inst_id (nop_ids_of_group (dfg_build_function fn0) mode is g)` by
    (gvs[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `MEM (EL n is).inst_id (sort_ids_by_block is g.cg_inst_ids)` by
    (simp[sort_ids_by_block_def, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  Cases_on `REVERSE (sort_ids_by_block is g.cg_inst_ids)`
  >- metis_tac[MEM_REVERSE, MEM] >>
  rename1 `REVERSE (sort_ids_by_block is g.cg_inst_ids) = rep::earlier` >>
  `rep_of_group is g = SOME (rep,g)` by gvs[rep_of_group_def] >>
  `rep = (EL n is).inst_id` by
    (Cases_on `rep = (EL n is).inst_id` >- simp[] >>
     `MEM (EL n is).inst_id earlier` by metis_tac[MEM_REVERSE, MEM] >>
     qpat_x_assum `~MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
     pure_asm_rewrite_tac[nop_ids_of_group_def, MEM_FILTER, MEM_REVERSE] >>
     gvs[MEM_FILTER, MEM_REVERSE, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  `MEM ((EL n is).inst_id,g) rs` by
    (pure_asm_rewrite_tac[rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
     qexists `SOME ((EL n is).inst_id,g)` >> simp[] >> qexists `g` >> simp[] >> metis_tac[]) >>
  gvs[alistTheory.ALOOKUP_NONE, MEM_MAP] >> metis_tac[pairTheory.FST]
QED

Theorem mm_local_payload_retained_static_if_forward[local]:
  mm_local_payload_cut cap is gs H n excluded pc t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  static_mem_ok eom ctx fn i (H n) /\
  (in_revert_forward fn (H n) ==> in_revert_forward fn' t) ==>
  static_mem_ok eom ctx fn' i t
Proof
  strip_tac >>
  `inst_mem_ranges i (H n) = inst_mem_ranges i t` by
    (irule o1ContractCfgNormTheory.supply_inst_mem_ranges_cong >>
     gvs[mm_local_payload_cut_def, mm_local_nonmemory_frame_def] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[venomStateTheory.eval_operand_def]) >>
  gvs[unitMemInvTheory.static_mem_ok_def] >> metis_tac[]
QED

Theorem mm_local_payload_bulk_static[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
  (g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom) ==>
  static_mem_ok eom ctx fn (mk_bulk_copy_inst mode inst g) t
Proof
  Cases_on `mode` >> simp[] >> strip_tac >>
  simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    mk_bulk_copy_inst_def, mode_copy_opcode_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.sized_source_write_range_def, venomStateTheory.eval_operand_def,
    wordsTheory.w2n_n2w]
QED

Theorem mm_local_payload_word_static[local]:
  mode IN {CalldataMerge; DloadMerge} /\ dst < dimword (:256) /\ dst + 32 <= eom ==>
  static_mem_ok eom ctx fn (mk_load_inst mode inst src v) t /\
  static_mem_ok eom ctx fn (mk_mstore_from_load inst dst v) u
Proof
  Cases_on `mode` >> simp[] >> strip_tac >>
  simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
    mk_load_inst_def, mode_load_opcode_def, mk_mstore_from_load_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def, venomStateTheory.eval_operand_def,
    wordsTheory.w2n_n2w] >>
  Cases_on `lookup_var v u` >> simp[arithmeticTheory.ADD_COMM]

QED



Theorem mm_local_payload_word_representative_payload[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  cap = mm_local_payload_capture mode is H N /\
  mm_local_group_captures is cap B g /\
  j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
  cap j = SOME (d,bs) /\ (EL j is).inst_opcode = MSTORE /\ g.cg_length = 32 ==>
  d = g.cg_dst /\ bs = mm_local_bytes B g.cg_src 32
Proof
  strip_tac >>
  `LENGTH bs = 32` by
    (Cases_on `mode` >> gvs[mm_local_payload_capture_def,
      mode_copy_opcode_def, mm_local_write_capture_def, AllCaseEqs()]) >>
  `g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
   bs = mm_local_bytes B (g.cg_src + (d-g.cg_dst)) (LENGTH bs)` by
    (qpat_assum `mm_local_group_captures is cap B g` mp_tac >>
     rewrite_tac[mm_local_group_captures_def] >>
     disch_then (qspecl_then [`j`,`d`,`bs`] mp_tac) >> simp[]) >>
  `d = g.cg_dst` by decide_tac >> gvs[]
QED

Theorem mm_local_payload_chunk_steps[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  ~MEM inst.inst_id ns /\ ALOOKUP rs inst.inst_id = SOME g /\
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
  g.cg_length < dimword (:256) /\
  bs = TAKE g.cg_length (DROP g.cg_src
    (if mode = CalldataMerge then t.vs_call_ctx.cc_calldata else t.vs_data_section)
      ++ REPLICATE g.cg_length 0w) /\
  fresh_inst_id es = (lid,es1) /\ fresh_ir_var es1 = (v,es2) /\ v IN excluded /\
  (g.cg_length = 32 /\ mode <> DloadMerge /\ inst.inst_opcode = MSTORE ==>
    step_inst fuel ctx inst t = OK (write_memory_with_expansion g.cg_dst bs t)) /\
  apply_groups_inst_supply mode ns rs es inst = (chunk,es') ==>
  ?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
    t'.vs_memory = (write_memory_with_expansion g.cg_dst bs t).vs_memory /\
    mm_local_nonmemory_frame t' = mm_local_nonmemory_frame t /\
    (!x. x NOTIN excluded ==> lookup_var x t' = lookup_var x t)
Proof
  strip_tac >> Cases_on `g.cg_length = 32 /\ mode <> DloadMerge`
  >- (qpat_x_assum `g.cg_length = 32 /\ mode <> DloadMerge`
        (CONJUNCTS_THEN assume_tac) >> Cases_on `inst.inst_opcode = MSTORE`
      >- (qexists `write_memory_with_expansion g.cg_dst bs t
            with vs_inst_idx := SUC t.vs_inst_idx` >>
          gnvs[apply_groups_inst_supply_def] >> gvs[] >>
          simp[mm_local_exec_prefix_single, venomInstTheory.is_terminator_def,
            venomStateTheory.write_memory_with_expansion_def,
            mm_local_nonmemory_frame_def, venomStateTheory.lookup_var_def]) >>
      `step_inst fuel ctx
         (mk_load_inst mode (inst with inst_id := lid) g.cg_src v) t =
         OK (update_var v (word_of_bytes T (0w:bytes32) bs) t) /\
       step_inst fuel ctx (mk_mstore_from_load inst g.cg_dst v)
         (update_var v (word_of_bytes T (0w:bytes32) bs) t) =
         OK (update_var v (word_of_bytes T (0w:bytes32) bs)
           (write_memory_with_expansion g.cg_dst bs t))` by
        (mp_tac (Q.INST [`inst` |-> `inst with inst_id := lid`,
           `dst` |-> `g.cg_dst`, `src` |-> `g.cg_src`,
           `w` |-> `word_of_bytes T (0w:bytes32) bs`] mm_local_payload_word_steps) >>
         mp_tac (Q.INST [`dst` |-> `g.cg_dst`, `src` |-> `g.cg_src`,
           `w` |-> `word_of_bytes T (0w:bytes32) bs`] mm_local_payload_word_steps) >>
         simp[] >> metis_tac[]) >>
      `step_inst fuel ctx (mk_mstore_from_load inst g.cg_dst v)
         (update_var v (word_of_bytes T (0w:bytes32) bs) t
            with vs_inst_idx := SUC t.vs_inst_idx) =
         OK (update_var v (word_of_bytes T (0w:bytes32) bs)
           (write_memory_with_expansion g.cg_dst bs t)
             with vs_inst_idx := SUC t.vs_inst_idx)` by
        (irule dftIndexedExecTheory.dft_step_ok_idx >> conj_tac
         >- simp[mk_mstore_from_load_def,venomInstTheory.is_terminator_def] >>
         first_assum MATCH_ACCEPT_TAC) >>
      `~is_terminator (mk_load_inst mode (inst with inst_id := lid) g.cg_src v).inst_opcode /\
       ~is_terminator (mk_mstore_from_load inst g.cg_dst v).inst_opcode` by
        (Cases_on `mode` >> simp[mk_load_inst_def,mk_mstore_from_load_def,
          mode_load_opcode_def,venomInstTheory.is_terminator_def]) >>
      qexists `update_var v (word_of_bytes T (0w:bytes32) bs)
          (write_memory_with_expansion g.cg_dst bs t)
            with vs_inst_idx := SUC (SUC t.vs_inst_idx)` >>
      gnvs[apply_groups_inst_supply_def] >> gvs[] >> conj_tac
      >- simp[mm_local_exec_prefix_def] >>
      simp[mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
        venomStateTheory.lookup_var_def,
        venomStateTheory.update_var_def, venomStateTheory.write_memory_with_expansion_def,
        finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >> metis_tac[]) >>
  `step_inst fuel ctx (mk_bulk_copy_inst mode inst g) t =
    OK (write_memory_with_expansion g.cg_dst bs t)` by
    (mp_tac (Q.INST [`i` |-> `mk_bulk_copy_inst mode inst g`,
      `dst` |-> `n2w g.cg_dst`, `src` |-> `n2w g.cg_src`,
      `len` |-> `n2w g.cg_length`] (SPEC_ALL mm_local_payload_bulk_step)) >>
     simp[mk_bulk_copy_inst_def, wordsTheory.w2n_n2w]) >>
  `~is_terminator (mk_bulk_copy_inst mode inst g).inst_opcode` by
    (Cases_on `mode` >> simp[mk_bulk_copy_inst_def,mode_copy_opcode_def,
      venomInstTheory.is_terminator_def]) >>
  qexists `write_memory_with_expansion g.cg_dst bs t
    with vs_inst_idx := SUC t.vs_inst_idx` >>
  gnvs[apply_groups_inst_supply_def] >> gvs[] >> conj_tac
  >- simp[mm_local_exec_prefix_single] >>
  simp[mm_local_exec_prefix_single, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
    venomStateTheory.write_memory_with_expansion_def]
QED

Theorem mm_local_payload_captured_store_step[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  mm_local_payload_capture mode is H N j = SOME (d,bs) /\
  (EL j is).inst_opcode = MSTORE /\
  t.vs_labels = (H j).vs_labels /\
  (!v. MEM (Var v) (EL j is).inst_operands ==> lookup_var v t = lookup_var v (H j)) ==>
  LENGTH bs = 32 /\
  step_inst fuel ctx (EL j is) t = OK (write_memory_with_expansion d bs t)
Proof
  strip_tac >>
  `mm_local_write_capture is H N j = SOME (d,bs)` by
    (Cases_on `mode` >> gvs[mm_local_payload_capture_def, mode_copy_opcode_def]) >>
  `!op. MEM op (EL j is).inst_operands ==> eval_operand op t = eval_operand op (H j)` by
    (rpt strip_tac >> Cases_on `op` >> simp[venomStateTheory.eval_operand_def]) >>
  gvs[mm_local_write_capture_def, AllCaseEqs()] >>
  rename1 `(EL j is).inst_operands = [a;b]` >>
  `eval_operand a t = eval_operand a (H j) /\
   eval_operand b t = eval_operand b (H j)` by simp[] >>
  gvs[] >> simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  with_opcode_clause simp >>
  simp[venomExecSemanticsTheory.exec_write2_def, venomMemPropsTheory.mstore_eq_write_mem]
QED

Theorem mm_local_payload_nonterminator_stop[local]:
  mm_local_payload_cut cap is gs H n excluded pc t /\
  (i.inst_opcode = INVOKE ==> mm_local_pending_indices is gs n = []) /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\
  ~(?err. step_inst fuel ctx i (H n) = Error err) /\
  ~(?u. step_inst fuel ctx i (H n) = OK u) ==>
  lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx i (H n)) (step_inst fuel ctx i t)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (irule venomExecutionReplayPropsTheory.state_non_ok >> metis_tac[mm_local_payload_cut_empty]) >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    gvs[mm_local_payload_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
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

Theorem mm_local_payload_terminator_result[local]:
  mm_local_payload_cut cap is gs H n excluded pc t /\
  mm_local_pending_indices is gs n = [] /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  is_terminator i.inst_opcode ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [i] (H n)) (dft_exec_suffix fuel ctx [i] t)
Proof
  strip_tac >> irule venomExecutionReplayPropsTheory.state_terminator_result >>
  metis_tac[mm_local_payload_cut_empty]
QED


Theorem mm_local_payload_live_load_step[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  bytes = (if mode = CalldataMerge then (\u. u.vs_call_ctx.cc_calldata)
           else (\u. u.vs_data_section)) /\
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode /\
  (!v src. FLOOKUP ss.ss_loads v = SOME src ==>
    lookup_var v s = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src (bytes s) ++ REPLICATE 32 0w)))) /\
  (!v src. FLOOKUP ss.ss_loads v = SOME src ==> ~MEM v inst.inst_outputs) ==>
  !v src. FLOOKUP (scan_inst dfg mode ss inst).ss_loads v = SOME src ==>
    lookup_var v t = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src (bytes t) ++ REPLICATE 32 0w)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule mm_local_scan_lookup_step >> strip_tac
  >- (`lookup_var v t = lookup_var v s` by
        (irule basePtrProofsTheory.step_inst_preserves_lookup >> metis_tac[]) >>
      `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section` by
        metis_tac[venomInstProofsTheory.step_preserves_call_ctx,
          venomInstProofsTheory.step_preserves_data_section] >>
      gvs[] >> metis_tac[]) >>
  `mode = CalldataMerge \/ mode = DloadMerge` by gvs[] >>
  gvs[mode_load_opcode_def, venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def, venomExecSemanticsTheory.exec_read1_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem mm_local_payload_live_load_cut[local]:
  !n h states fn0 supply index k bb sk fuel ctx mode bytes.
  mode IN {CalldataMerge; DloadMerge} /\
  bytes = (if mode = CalldataMerge then (\u. u.vs_call_ctx.cc_calldata)
           else (\u. u.vs_data_section)) /\
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  h+n <= LENGTH bb.bb_instructions /\ n < LENGTH states /\
  (FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state
    (TAKE h bb.bb_instructions)).ss_loads = FEMPTY /\
  (!r. r < n ==>
    ~is_terminator (EL (h+r) bb.bb_instructions).inst_opcode /\
    ?t. step_inst fuel ctx (EL (h+r) bb.bb_instructions) (EL r states) = OK t /\
        EL (SUC r) states = t with vs_inst_idx := SUC (EL r states).vs_inst_idx) ==>
  !v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE (h+n) bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (EL n states) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src (bytes (EL n states)) ++ REPLICATE 32 0w)))
Proof
  Induct_on `n`
  >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE (h+n) bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (EL n states) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src (bytes (EL n states)) ++ REPLICATE 32 0w)))` by
    (first_x_assum match_mp_tac >>
     qexistsl [`supply`,`index`,`k`,`sk`,`fuel`,`ctx`] >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `h+n < LENGTH bb.bb_instructions` by decide_tac >>
  `~is_terminator (EL (h+n) bb.bb_instructions).inst_opcode /\
    ?t. step_inst fuel ctx (EL (h+n) bb.bb_instructions) (EL n states) = OK t /\
        EL (SUC n) states = t with vs_inst_idx := SUC (EL n states).vs_inst_idx` by
    (first_x_assum irule >> simp[]) >>
  `!u a. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE (h+n) bb.bb_instructions)).ss_loads u = SOME a ==>
    ~MEM u (EL (h+n) bb.bb_instructions).inst_outputs` by
    (metis_tac[mm_local_live_cut_fresh]) >>
  `~is_terminator (EL (h+n) bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `!r. r < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE (h+n) bb.bb_instructions)`,
    `inst` |-> `EL (h+n) bb.bb_instructions`, `s` |-> `EL n states`,
    `dfg` |-> `dfg_build_function fn0`] (SPEC_ALL mm_local_payload_live_load_step)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qspecl_then [`v`,`src`] mp_tac) >>
  gvs[arithmeticTheory.ADD_CLAUSES, rich_listTheory.TAKE_SUC_BY_TAKE,
      rich_listTheory.FOLDL_SNOC, venomStateTheory.lookup_var_def]
QED

Theorem mm_local_payload_live_load_history[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  bytes = (if mode = CalldataMerge then (\u. u.vs_call_ctx.cc_calldata)
           else (\u. u.vs_data_section)) /\
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  h = phi_prefix_length bb.bb_instructions /\
  h <= j /\ j <= LENGTH bb.bb_instructions /\
  (!q. h <= q /\ q < j ==>
    ~is_terminator (EL q bb.bb_instructions).inst_opcode /\
    ?u. step_inst fuel ctx (EL q bb.bb_instructions) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC (H q).vs_inst_idx) ==>
  !v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src (bytes (H j)) ++ REPLICATE 32 0w)))
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`j-h`,`h`,`GENLIST (\r. H (h+r)) (SUC (j-h))`,
    `fn0`,`supply`,`index`,`k`,`bb`,`sk`,`fuel`,`ctx`,`mode`,`bytes`]
    mm_local_payload_live_load_cut) >>
  `h + (j-h) = j` by decide_tac >>
  simp[mm_local_scan_phi_prefix, empty_scan_state_def, EL_GENLIST] >>
  impl_tac >- (rpt strip_tac >>
    qpat_x_assum `!q. _ ==> ~is_terminator _ /\ _`
      (qspec_then `r + phi_prefix_length bb.bb_instructions` mp_tac) >>
    (impl_tac >- (gvs[] >> decide_tac)) >> simp[arithmeticTheory.ADD_CLAUSES]) >> simp[]
QED

Theorem mm_local_payload_stopping_history[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\
  s.vs_inst_idx = h /\ s.vs_current_bb = bb.bb_label /\
  cd = (if mode = CalldataMerge then s.vs_call_ctx.cc_calldata else s.vs_data_section) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn bb s) /\
  ~(?err. exec_block fuel ctx bb s = Error err) ==>
  ?n H. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==>
      (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
      static_mem_ok eom ctx fn (EL q is) (H q)) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n) /\
    (!j. (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
          else (H j).vs_data_section) = cd) /\
    (!j dst v src. j < LENGTH is /\ (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state
        (TAKE j is)).ss_loads v = SOME src ==>
      lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP src cd ++ REPLICATE 32 0w))))

Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `h <= LENGTH bb.bb_instructions` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `?n H. h <= n /\ n < LENGTH bb.bb_instructions /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q bb.bb_instructions).inst_opcode /\
      ?u. step_inst fuel ctx (EL q bb.bb_instructions) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==>
      static_mem_ok eom ctx fn (EL q bb.bb_instructions) (H q)) /\
    (is_terminator (EL n bb.bb_instructions).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n bb.bb_instructions) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n bb.bb_instructions] (H n)` by
    (irule venomExecutionReplayPropsTheory.source_stopping_history >> simp[] >> metis_tac[]) >>
  `!q. h <= q /\ q <= n ==> (H q).vs_current_bb = bb.bb_label` by
    metis_tac[venomExecutionReplayPropsTheory.source_history_label] >>
  `!q. h <= q /\ q <= n ==>
    (H q).vs_call_ctx = s.vs_call_ctx /\
    (H q).vs_data_section = s.vs_data_section` by
    (rpt strip_tac >>
     `h + (q-h) = q` by decide_tac >>
     mp_tac (Q.SPECL [`q-h`,`h`,`H`,`is`,`fuel`,`ctx`]
       venomExecutionReplayPropsTheory.payload_history_fields) >>
     (impl_tac >- (gvs[] >> rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS])) >>
     simp[]) >>
  qabbrev_tac `H0 = \j. if j < h then s else H j` >>
  `!j. j <= n ==>
    (if mode = CalldataMerge then (H0 j).vs_call_ctx.cc_calldata
     else (H0 j).vs_data_section) = cd` by
    (rpt strip_tac >> Cases_on `j < h` >> simp[Abbr `H0`] >>
     `h <= j` by decide_tac >> metis_tac[]) >>
  `!j dst v src. j <= n /\ j < LENGTH is /\
    (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H0 j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))` by
    (rpt strip_tac >> Cases_on `j < h`
     >- (`EVERY (\i. i.inst_opcode = PHI) (TAKE h is)` by
           simp[analysisSimProofsBaseTheory.phi_prefix_all_phi] >>
         `(EL j is).inst_opcode = PHI` by
           (qpat_x_assum `EVERY _ (TAKE h is)`
             (fn th => mp_tac (Q.SPEC `j` (REWRITE_RULE[EVERY_EL] th))) >>
           simp[LENGTH_TAKE,EL_TAKE] >> gvs[LENGTH_TAKE,EL_TAKE] >> decide_tac) >> gvs[]) >>
     `h <= j /\ j <= LENGTH bb.bb_instructions` by gvs[] >>
     mp_tac (Q.INST [`bytes` |-> `(if mode = CalldataMerge then (\u. u.vs_call_ctx.cc_calldata)
       else (\u. u.vs_data_section))`]
       (SPEC_ALL mm_local_payload_live_load_history)) >>
     (impl_tac >- (gvs[] >> rpt strip_tac >>
       metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS,arithmeticTheory.LESS_IMP_LESS_OR_EQ])) >>
     strip_tac >> simp[Abbr `H0`] >> gvs[] >> metis_tac[]) >>
  `?H'. (!j. j <= n ==> H' j = H0 j) /\
    (!j. (if mode = CalldataMerge then (H' j).vs_call_ctx.cc_calldata
          else (H' j).vs_data_section) = cd) /\
    (!j dst v src. j < LENGTH is /\ (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state
        (TAKE j is)).ss_loads v = SOME src ==>
      lookup_var v (H' j) = SOME (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP src cd ++ REPLICATE 32 0w))))` by
    (irule mm_local_payload_prefix_extend >> metis_tac[]) >>
  `!j. h <= j /\ j <= n ==> H' j = H j` by
    (rpt strip_tac >> simp[Abbr `H0`] >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  qexistsl [`n`,`H'`] >>
  gvs[] >> rpt strip_tac >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ,
    arithmeticTheory.LESS_OR]
QED

Theorem mm_local_payload_cut_nop_stutter[local]:
  mm_local_payload_cut cap is gs H n excluded pc t /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
  (H (SUC n)).vs_memory = (H n).vs_memory /\
  mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
  (!v. v NOTIN excluded ==> lookup_var v (H (SUC n)) = lookup_var v (H n)) ==>
  mm_local_payload_cut cap is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  gvs[mm_local_payload_cut_def, mm_local_nonmemory_frame_def,
    venomStateTheory.lookup_var_def] >>
  gvs[mm_local_pending_def] >> qexists `ws` >> simp[] >>
  irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]
QED

Theorem mm_local_payload_cut_erased_write[local]:
  mm_local_payload_cut cap is gs H n excluded pc t /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n] /\
  cap n = SOME (d,bs) /\
  (H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory /\
  mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
  (!v. lookup_var v (H (SUC n)) = lookup_var v (H n)) ==>
  mm_local_payload_cut cap is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >>
  `mm_local_pending cap (mm_local_pending_indices is gs (SUC n))
      (H (SUC n)) t` by
    (asm_rewrite_tac[] >> irule mm_local_pending_create >>
     fs[mm_local_payload_cut_def] >> metis_tac[]) >>
  gvs[mm_local_payload_cut_def, mm_local_nonmemory_frame_def,
    venomStateTheory.lookup_var_def, mm_local_pending_def] >>
  qexists `ws'` >> simp[] >> irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]
QED

Theorem mm_local_payload_erased_write_transition[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  cap = mm_local_payload_capture mode is H N /\ cap n = SOME (d,bs) /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n] /\
  MEM (EL n is).inst_id ns /\
  mm_local_payload_cut cap is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  apply_groups_inst_supply mode ns rs es (EL n is) = ([mk_nop_from (EL n is)],es) /\
  mm_local_exec_prefix fuel ctx [mk_nop_from (EL n is)] t
    (t with vs_inst_idx := SUC pc) /\
  mm_local_payload_cut cap is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >> conj_tac >- simp[apply_groups_inst_supply_def] >>
  conj_tac
  >- (simp[mm_local_exec_prefix_single, venomInstPropsTheory.step_nop_identity,
        mk_nop_from_def, venomInstTheory.is_terminator_def] >>
      fs[mm_local_payload_cut_def]) >>
  `(H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory /\
   mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
   (!v. lookup_var v (H (SUC n)) = lookup_var v (H n))` by
    (mp_tac (Q.INST [`n` |-> `N`, `j` |-> `n`]
       (SPEC_ALL mm_local_payload_capture_actual_step)) >>
     (impl_tac >- gvs[]) >> simp[]) >>
  irule mm_local_payload_cut_erased_write >> metis_tac[]
QED

Theorem mm_local_payload_load_frame[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  i.inst_opcode = mode_load_opcode mode /\ step_inst fuel ctx i s = OK t ==>
  t.vs_memory = s.vs_memory /\ mm_local_nonmemory_frame t = mm_local_nonmemory_frame s
Proof
  Cases_on `mode` >> simp[mode_load_opcode_def] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  with_opcode_clause simp >> simp[venomExecSemanticsTheory.exec_read1_def] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.update_var_def]
QED

Theorem mm_local_payload_erased_load_transition[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
  (EL n is).inst_opcode = mode_load_opcode mode /\
  (!v. MEM v (EL n is).inst_outputs ==> v IN excluded) /\
  MEM (EL n is).inst_id ns /\
  mm_local_payload_cut cap is gs H n excluded pc t /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  apply_groups_inst_supply mode ns rs es (EL n is) = ([mk_nop_from (EL n is)],es) /\
  mm_local_exec_prefix fuel ctx [mk_nop_from (EL n is)] t
    (t with vs_inst_idx := SUC pc) /\
  mm_local_payload_cut cap is gs H (SUC n) excluded (SUC pc)
    (t with vs_inst_idx := SUC pc)
Proof
  strip_tac >> conj_tac >- simp[apply_groups_inst_supply_def] >>
  conj_tac
  >- (simp[mm_local_exec_prefix_single, venomInstPropsTheory.step_nop_identity,
        mk_nop_from_def, venomInstTheory.is_terminator_def] >>
      fs[mm_local_payload_cut_def]) >>
  `u.vs_memory = (H n).vs_memory /\
   mm_local_nonmemory_frame u = mm_local_nonmemory_frame (H n)` by
    metis_tac[mm_local_payload_load_frame] >>
  `!v. v NOTIN excluded ==> lookup_var v u = lookup_var v (H n)` by
    (rpt strip_tac >> irule basePtrProofsTheory.step_inst_preserves_lookup >>
     metis_tac[]) >>
  irule mm_local_payload_cut_nop_stutter >>
  gvs[mm_local_nonmemory_frame_def, venomStateTheory.lookup_var_def]
QED

Theorem mm_local_payload_barrier_transition[local]:
  mm_local_pending_indices is gs n = [] /\
  mm_local_pending_indices is gs (SUC n) = [] /\
  mm_local_payload_cut cap is gs H n excluded pc t /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  ~is_terminator (EL n is).inst_opcode /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_payload_cut cap is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >>
  `state_equiv excluded ((H n) with vs_inst_idx := pc) t` by
    metis_tac[mm_local_payload_cut_empty] >>
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
  >- gvs[mm_local_exec_prefix_single, mm_local_payload_cut_def] >>
  gvs[mm_local_payload_cut_def, mm_local_pending_empty, state_equiv_frame,
    mm_local_nonmemory_frame_def, stateFrameTheory.state_frame_def,
    venomStateTheory.lookup_var_def, venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_payload_nonvolatile_transition[local]:
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n /\
  n < LENGTH is /\ ~is_volatile_memory (EL n is) /\
  mm_local_payload_cut cap is gs H n excluded pc t /\
  (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  ~is_terminator (EL n is).inst_opcode /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n ==>
  ?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
    mm_local_payload_cut cap is gs H (SUC n) excluded (SUC pc) t'
Proof
  strip_tac >> drule mm_local_nonvolatile_effects >> strip_tac >>
  `state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
    gvs[mm_local_payload_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
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
  >- gvs[mm_local_exec_prefix_single, mm_local_payload_cut_def] >>
  gvs[mm_local_payload_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
    stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
    venomStateTheory.venom_state_component_equality] >>
  gvs[mm_local_pending_def] >> qexists_tac `ws` >> simp[] >>
  irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]
QED


Theorem mm_local_payload_due_extent[local]:
  mm_local_group_coverage is n cap g /\
  mm_local_group_endpoint is n cap g /\
  ws = MAP (THE o cap) js /\
  (!j. MEM j js ==> IS_SOME (cap j)) /\
  (!j d bs. (MEM j js /\ cap j = SOME (d,bs)) <=>
    (j < n /\ j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
     cap j = SOME (d,bs))) ==>
  (!a. (g.cg_dst <= a /\ a < g.cg_dst + g.cg_length) <=>
    ?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs) /\
  (!d bs. MEM (d,bs) ws ==> d + LENGTH bs <= g.cg_dst + g.cg_length) /\
  MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws) = g.cg_dst + g.cg_length
Proof
  strip_tac >>
  `!d bs. MEM (d,bs) ws <=> ?j. MEM j js /\ cap j = SOME (d,bs)` by
    (gvs[MEM_MAP] >> rpt gen_tac >> eq_tac
     >- (strip_tac >> rename1 `MEM j js` >>
         `IS_SOME (cap j)` by metis_tac[] >>
         Cases_on `cap j` >> gvs[] >> metis_tac[]) >>
     strip_tac >> qexists `j` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ws = _` kall_tac >>
  fs[mm_local_group_coverage_def, mm_local_group_endpoint_def] >>
  conj_tac >- metis_tac[] >>
  irule venomWriteReplayPropsTheory.write_log_endpoint >> metis_tac[]
QED

Theorem mm_local_payload_due_realize[local]:
  mm_local_group_captures is cap B g /\
  mm_local_group_coverage is n cap g /\
  mm_local_group_endpoint is n cap g /\
  ws = MAP (THE o cap) js /\
  (!j. MEM j js ==> IS_SOME (cap j)) /\
  (!j d bs. (MEM j js /\ cap j = SOME (d,bs)) <=>
    (j < n /\ j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
     cap j = SOME (d,bs))) ==>
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws =
    write_memory_with_expansion g.cg_dst (mm_local_bytes B g.cg_src g.cg_length) v
Proof
  strip_tac >>
  drule_all mm_local_payload_due_extent >> strip_tac >>
  irule mm_local_write_log_realize >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `?j. MEM j js /\ cap j = SOME (d,bs)` by
    (gvs[MEM_MAP] >> rename1 `MEM j js` >>
     `IS_SOME (cap j)` by metis_tac[] >>
     Cases_on `cap j` >> gvs[] >> metis_tac[]) >>
  fs[mm_local_group_captures_def] >> metis_tac[]
QED

Theorem mm_local_payload_representative_discharge[local]:
  mm_local_pending cap js s t /\ cap r = SOME (d,bs) /\
  survivors = FILTER (\j. ~P j) js /\
  (!pre j mid k post a cs b ds.
    js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k /\
    cap j = SOME (a,cs) /\ cap k = SOME (b,ds) ==>
    mm_local_write_compatible a cs b ds) /\
  (!j a cs. MEM j survivors /\ cap j = SOME (a,cs) ==>
    mm_local_write_compatible a cs d bs) /\
  (!v. FOLDL (\st (a,cs). write_memory_with_expansion a cs st) v
    (MAP (THE o cap) (FILTER P js ++ [r])) =
    write_memory_with_expansion dst merged v) /\
  s'.vs_memory = (write_memory_with_expansion d bs s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion dst merged t).vs_memory ==>
  mm_local_pending cap survivors s' t'
Proof
  strip_tac >>
  `EVERY (\j. IS_SOME (cap j)) js` by
    (gvs[mm_local_pending_def] >> metis_tac[venomWriteReplayPropsTheory.capture_log_canonical]) >>
  `!Q. LIST_REL (\j w. cap j = SOME w) (FILTER Q js)
      (MAP (THE o cap) (FILTER Q js))` by
    (gen_tac >> simp[LIST_REL_MAP2] >> irule EVERY2_refl >>
     simp[EVERY_MEM, MEM_FILTER] >> qx_gen_tac `j` >> strip_tac >>
     `IS_SOME (cap j)` by gvs[EVERY_MEM] >>
     Cases_on `cap j` >> gvs[]) >>
  qpat_x_assum `survivors = _` SUBST_ALL_TAC >>
  irule mm_local_pending_compatible_discharge_filter >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  qexistsl [`d`,`dst`,`merged`,
    `MAP (THE o cap) (FILTER P js)`,`bs`,
    `MAP (THE o cap) (FILTER (\j. ~P j) js)`,`s`,`t`] >>
  simp[] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!v. FOLDL _ _ _ = _` (qspec_then `v` mp_tac) >>
      simp[MAP_APPEND, FOLDL_APPEND]) >>
  simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `j` >> strip_tac >>
  `IS_SOME (cap j)` by gvs[EVERY_MEM, MEM_FILTER] >>
  Cases_on `cap j` >> gvs[] >> PairCases_on `x` >>
  gvs[] >> metis_tac[]
QED


Theorem mm_local_payload_representative_transition[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  cap = mm_local_payload_capture mode is H (LENGTH is) /\
  n < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL n is).inst_id,g) /\
  (!j. (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
         else (H j).vs_data_section) = cd) /\
  (!j dst v src. j < LENGTH is /\ (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode is gs /\
  rs = rep_map_of_groups is gs /\
  (!v. chunk = [EL n is] /\ MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j d bs. j <= n /\ cap j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j)) /\
  eom < dimword (:256) /\
  mm_local_payload_cut cap is gs H n excluded pc t /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  apply_groups_inst_supply mode ns rs es (EL n is) = (chunk,es') ==>
  ?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
    mm_local_payload_cut cap is gs H (SUC n) excluded (pc + LENGTH chunk) t' /\
    (!w. EVERY (\i. static_mem_ok eom ctx fn' i w) chunk)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL n is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `~MEM (EL n is).inst_id ns /\ ALOOKUP rs (EL n is).inst_id = SOME g` by
    metis_tac[mm_local_prefix_selected_rep, EL_MEM] >>
  `(EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    metis_tac[mm_local_canonical_rep_write] >>
  `mm_local_group_captures is cap
      (\a. if a < LENGTH cd then EL a cd else 0w) g /\
   mm_local_group_coverage is (LENGTH is) cap g /\
   mm_local_group_endpoint is (LENGTH is) cap g` by
    (mp_tac (SPEC_ALL mm_local_payload_final_certificate) >>
     qpat_assum `is = _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `gs = _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `!j d bs. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      cap j = SOME (d,bs) ==>
      d + LENGTH bs < dimword (:256) /\
      (LENGTH bs = 0 \/ d + LENGTH bs <= eom)` by
    (rpt gen_tac >> strip_tac >>
     `j <= n` by
       (mp_tac (Q.INST [`cg` |-> `g`]
         (Q.SPECL [`is`,`j`,`n`] mm_local_rep_position_max)) >> simp[]) >>
     mp_tac (Q.INST [`n` |-> `LENGTH is`]
       (SPEC_ALL mm_local_payload_capture_finite)) >>
     qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  SUBGOAL_THEN ``g.cg_dst < dimword (:256) /\ g.cg_length < dimword (:256) /\
   (g.cg_length = 0 \/ g.cg_dst + g.cg_length <= eom)``
    (map_every assume_tac o CONJUNCTS)
  >-
    (mp_tac (Q.INST [`n` |-> `LENGTH is`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:word8``]
         mm_local_payload_group_finite))) >>
     impl_tac >- (pure_asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >>
     simp[]) >>
  `g.cg_src < dimword (:256)` by metis_tac[mm_local_group_source_finite] >>
  qabbrev_tac `due = FILTER (\j. mm_local_rep_index is gs j = n)
    (mm_local_pending_indices is gs n)` >>
  `!j. MEM j (due ++ [n]) ==> IS_SOME (cap j)` by
    (mp_tac (Q.INST [`r` |-> `n`, `N` |-> `LENGTH is`]
       (SPEC_ALL mm_local_payload_due_captures_some)) >>
     qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >>
     impl_tac >-
       (simp[Abbr `due`] >> rpt strip_tac >>
        qpat_assum `!j dst v src. j < LENGTH is /\ _ ==> _`
          (qspecl_then [`j`,`dst`,`v`,`src`] mp_tac) >>
        (impl_tac >- simp[]) >>
        disch_then (fn th => rewrite_tac[th]) >> simp[]) >>
     simp[]) >>
  `?d bs. cap n = SOME (d,bs)` by
    (`IS_SOME (cap n)` by
       (qpat_assum `!j. MEM j (due ++ [n]) ==> _`
          (qspec_then `n` mp_tac) >> simp[]) >>
     Cases_on `cap n` >- fs[] >>
     rename1 `cap n = SOME captured` >> Cases_on `captured` >> metis_tac[]) >>
  `!v. FOLDL (\st (a,cs). write_memory_with_expansion a cs st) v
    (MAP (THE o cap) (due ++ [n])) =
    write_memory_with_expansion g.cg_dst
      (mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w) g.cg_src g.cg_length) v` by
    (gen_tac >>
     mp_tac (Q.INST [`n` |-> `LENGTH is`, `js` |-> `due ++ [n]`,
       `ws` |-> `MAP (THE o cap) (due ++ [n])`,
       `B` |-> `\a. if a < LENGTH cd then EL a cd else 0w`]
       (SPEC_ALL mm_local_payload_due_realize)) >>
     impl_tac >- (simp[] >>
     mp_tac (Q.INST [`r` |-> `n`, `N` |-> `LENGTH is`]
       (SPEC_ALL mm_local_payload_due_capture_indices)) >>
     qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[Abbr `due`]) >> simp[]) >>
  `!j l a cs b ds. MEM j (mm_local_pending_indices is gs n) /\ j < l /\ l <= n /\
      (?h. MEM h gs /\ MEM (EL l is).inst_id h.cg_inst_ids) /\
      cap j = SOME (a,cs) /\ cap l = SOME (b,ds) ==>
      mm_local_write_compatible a cs b ds` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`d` |-> `a`, `bs` |-> `cs`, `a` |-> `b`, `cs` |-> `ds`]
       (SPEC_ALL mm_local_payload_pending_compatible)) >> pure_asm_rewrite_tac[] >> simp[]) >>
  Cases_on `fresh_inst_id es` >> rename1 `fresh_inst_id es = (lid,es1)` >>
  Cases_on `fresh_ir_var es1` >> rename1 `fresh_ir_var es1 = (v,es2)` >>
  `es1.irs_used_vars = es.irs_used_vars` by
    (qpat_assum `fresh_inst_id es = _`
       (fn th => mp_tac (AP_TERM ``\p:num # ir_supply. (SND p).irs_used_vars`` th)) >>
     simp[NoAsms,irSupplyTheory.fresh_inst_id_def]) >>
  `v IN excluded` by
    (drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >> metis_tac[]) >>
  qpat_assum `mm_local_payload_cut cap is gs H n excluded pc t`
    (strip_assume_tac o PURE_REWRITE_RULE[mm_local_payload_cut_def]) >>
  `(H n).vs_call_ctx = t.vs_call_ctx /\
   (H n).vs_data_section = t.vs_data_section /\
   (H n).vs_labels = t.vs_labels` by
    (qpat_assum `mm_local_nonmemory_frame (H n) = mm_local_nonmemory_frame t`
       (fn th => mp_tac (AP_TERM
         ``\s:venom_state. (s.vs_call_ctx,s.vs_data_section,s.vs_labels)`` th)) >>
     simp[NoAsms,mm_local_nonmemory_frame_def,stateFrameTheory.state_frame_def]) >>
  `(if mode = CalldataMerge then t.vs_call_ctx.cc_calldata else t.vs_data_section) = cd` by
    (qpat_assum `(H n).vs_call_ctx = t.vs_call_ctx` (fn cth =>
     qpat_assum `(H n).vs_data_section = t.vs_data_section` (fn dth =>
     qpat_assum `!j. (if mode = CalldataMerge then _ else _) = cd`
       (qspec_then `n` (ACCEPT_TAC o PURE_REWRITE_RULE[cth,dth]))))) >>
  `g.cg_length = 32 /\ mode <> DloadMerge /\ (EL n is).inst_opcode = MSTORE ==>
   step_inst fuel ctx (EL n is) t = OK (write_memory_with_expansion g.cg_dst
     (mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w) g.cg_src g.cg_length) t)` by
    (strip_tac >>
     `chunk = [EL n is]` by gvs[apply_groups_inst_supply_def] >>
     `d = g.cg_dst /\ bs = mm_local_bytes
       (\a. if a < LENGTH cd then EL a cd else 0w) g.cg_src 32` by
       (mp_tac (Q.INST [`N` |-> `LENGTH (is:instruction list)`, `j` |-> `n:num`,
         `B` |-> `\a. if a < LENGTH cd then EL a cd else (0w:word8)`]
         (SPEC_ALL mm_local_payload_word_representative_payload)) >>
        qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
     mp_tac (Q.INST [`N` |-> `LENGTH (is:instruction list)`, `j` |-> `n:num`]
       (SPEC_ALL mm_local_payload_captured_store_step)) >>
     qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >>
     (impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[])) >> simp[]) >>
  `?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
      t'.vs_memory = (write_memory_with_expansion g.cg_dst
        (mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w) g.cg_src g.cg_length) t).vs_memory /\
      mm_local_nonmemory_frame t' = mm_local_nonmemory_frame t /\
      (!x. x NOTIN excluded ==> lookup_var x t' = lookup_var x t)` by
    (mp_tac (Q.INST [`inst` |-> `EL n is`,
       `bs` |-> `mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w)
          g.cg_src g.cg_length`] (SPEC_ALL mm_local_payload_chunk_steps)) >>
     impl_tac >- simp[mm_local_calldata_bytes] >> simp[]) >>
  `mm_local_pending_indices is gs (SUC n) =
    FILTER (\j. mm_local_rep_index is gs j <> n) (mm_local_pending_indices is gs n)` by
    (mp_tac (Q.INST [`r` |-> `n`]
       (SPEC_ALL mm_local_payload_representative_pending_suc)) >> simp[]) >>
  `(H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory /\
   mm_local_nonmemory_frame (H (SUC n)) = mm_local_nonmemory_frame (H n) /\
   (!x. lookup_var x (H (SUC n)) = lookup_var x (H n))` by
    (mp_tac (Q.INST [`n` |-> `LENGTH is`, `j` |-> `n`]
       (SPEC_ALL mm_local_payload_capture_actual_step)) >>
     (impl_tac >- (qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >> simp[])) >>
     simp[]) >>
  `mm_local_pending cap (mm_local_pending_indices is gs n) (H n) t` by
    fs[mm_local_payload_cut_def] >>
  `mm_local_pending cap (mm_local_pending_indices is gs (SUC n)) (H (SUC n)) t'` by
    (mp_tac (Q.INST [`js` |-> `mm_local_pending_indices is gs n`,
       `r` |-> `n`, `P` |-> `\j. mm_local_rep_index is gs j = n`,
       `survivors` |-> `mm_local_pending_indices is gs (SUC n)`,
       `s` |-> `H (n:num)`, `s'` |-> `H (SUC n)`, `dst` |-> `g.cg_dst`,
       `merged` |-> `mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w)
         g.cg_src g.cg_length`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:num``]
         mm_local_payload_representative_discharge))) >>
     impl_tac >- (simp[Abbr `due`] >> conj_tac
     >- (map_every qx_gen_tac [`pre`,`j`,`mid`,`l`,`post`,`a`,`cs`,`b`,`ds`] >>
         strip_tac >>
         `SORTED $< (mm_local_pending_indices is gs n)` by simp[mm_local_pending_indices_order] >>
         `j < l` by
           (qpat_x_assum `SORTED $< (mm_local_pending_indices is gs n)` mp_tac >>
            simp[sortingTheory.SORTED_APPEND, relationTheory.transitive_def] >>
            metis_tac[MEM_APPEND, MEM]) >>
         `MEM j (mm_local_pending_indices is gs n) /\
          MEM l (mm_local_pending_indices is gs n)` by simp[MEM_APPEND] >>
         `l < n /\ ?h. MEM h gs /\ MEM (EL l is).inst_id h.cg_inst_ids` by
           metis_tac[mm_local_pending_indices_mem] >>
         `l <= n` by decide_tac >>
         qpat_assum `!j l a cs b ds. _`
           (qspecl_then [`j`,`l`,`a`,`cs`,`b`,`ds`] mp_tac) >> simp[] >>
         disch_then irule >> qexists `h` >>
         qpat_assum `is = _` (fn th => rewrite_tac[GSYM th]) >>
         qpat_assum `gs = _` (fn th => rewrite_tac[GSYM th]) >>
         asm_rewrite_tac[]) >>
     simp[MEM_FILTER] >> map_every qx_gen_tac [`j`,`a`,`cs`] >> strip_tac >>
     `j < n` by metis_tac[mm_local_pending_indices_mem] >>
     qpat_assum `!j l a cs b ds. _`
       (qspecl_then [`j`,`n`,`a`,`cs`,`d`,`bs`] mp_tac) >>
     simp[] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  qexists `t'` >> simp[] >> conj_tac
  >- (rewrite_tac[mm_local_payload_cut_def] >> conj_tac
      >- (qspecl_then [`chunk`,`fuel`,`ctx`,`t`,`t'`] mp_tac
            mm_local_exec_prefix_cursor >> simp[]) >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  gen_tac >> Cases_on `g.cg_length = 32 /\ mode <> DloadMerge`
  >- (fs[] >> Cases_on `(EL n is).inst_opcode = MSTORE`
      >- (`?dw sv. (EL n is).inst_operands = [Lit dw; Var sv] /\ w2n dw = g.cg_dst` by
            (`d = g.cg_dst` by
               (mp_tac (Q.INST [`N` |-> `LENGTH (is:instruction list)`, `j` |-> `n:num`,
                 `B` |-> `\a. if a < LENGTH cd then EL a cd else (0w:word8)`]
                 (SPEC_ALL mm_local_payload_word_representative_payload)) >>
                qpat_assum `cap = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
             mp_tac (Q.INST [`j` |-> `n:num`] (SPEC_ALL mm_local_final_write_birth)) >>
             qpat_assum `gs = _` (fn th => rewrite_tac[GSYM th]) >>
             (impl_tac >- simp[]) >> strip_tac
             >- (qpat_x_assum `(EL n is).inst_opcode = mode_copy_opcode mode` mp_tac >>
                 simp[]) >>
             rename1 `(EL n is).inst_operands = [Lit dw0; Var sv0]` >>
             qexistsl [`dw0`,`sv0`] >> simp[] >>
             gvs[mm_local_payload_capture_def, mm_local_payload_opcodes,
               mm_local_write_capture_def, venomStateTheory.eval_operand_def,
               AllCaseEqs()]) >>
          gnvs[apply_groups_inst_supply_def] >> gvs[] >>
          Cases_on `lookup_var sv w` >>
          simp[unitMemInvTheory.static_mem_ok_def, unitMemInvTheory.inst_mem_ranges_def,
            contextCodegenRelTheory.source_memory_read_ranges_def,
            codegenRelTheory.source_memory_write_ranges_def,
            codegenRelTheory.fixed_source_write_range_def,
            venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM]) >>
      gnvs[apply_groups_inst_supply_def] >> gvs[] >> simp[] >>
      (conj_tac
       >- (irule (DISCH_ALL (CONJUNCT1 (UNDISCH
             (Q.INST [`mode` |-> `CalldataMerge`, `dst` |-> `g.cg_dst`]
               (SPEC_ALL mm_local_payload_word_static))))) >>
           simp[] >> qexists `g` >> simp[]) >>
       irule (DISCH_ALL (CONJUNCT2 (UNDISCH
         (Q.INST [`mode` |-> `CalldataMerge`, `dst` |-> `g.cg_dst`]
           (SPEC_ALL mm_local_payload_word_static))))) >> simp[])) >>
  `chunk = [mk_bulk_copy_inst mode (EL n is) g]` by
    (Cases_on `g.cg_length = 32`
     >- (`mode = DloadMerge` by
           (qpat_assum `~(g.cg_length = 32 /\ mode <> DloadMerge)` mp_tac >> simp[]) >>
         qpat_x_assum `apply_groups_inst_supply _ _ _ _ _ = _` mp_tac >>
         simp[apply_groups_inst_supply_def]) >>
     qpat_x_assum `apply_groups_inst_supply _ _ _ _ _ = _` mp_tac >>
     simp[apply_groups_inst_supply_def]) >>
  asm_rewrite_tac[] >> simp[] >>
  irule mm_local_payload_bulk_static >> simp[]
QED

Theorem mm_local_payload_actual_safe_transition_if_forward[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  dfg = dfg_build_function fn0 /\ is = bb.bb_instructions /\
  gs = (scan_block dfg mode bb).ss_flushed /\
  cap = mm_local_payload_capture mode is H (LENGTH is) /\
  n < LENGTH is /\ ~is_terminator (EL n is).inst_opcode /\
  (!j. (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
         else (H j).vs_data_section) = cd) /\
  (!j dst v src. j < LENGTH is /\ (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) /\
  (!v. chunk = [EL n is] /\
    MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded) /\
  (!v. MEM (EL n is).inst_id (nop_ids_of_groups dfg mode is gs) /\
    (EL n is).inst_opcode = mode_load_opcode mode /\
    MEM v (EL n is).inst_outputs ==> v IN excluded) /\
  step_inst fuel ctx (EL n is) (H n) = OK u /\
  H (SUC n) = u with vs_inst_idx := SUC n /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!j d bs. j <= n /\ cap j = SOME (d,bs) ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u) /\
  eom < dimword (:256) /\
  mm_local_payload_cut cap is gs H n excluded pc t /\
  static_mem_ok eom ctx fn (EL n is) (H n) /\
  (in_revert_forward fn (H n) ==> in_revert_forward fn' t) /\
  (!v. v NOTIN excluded ==> MEM v es.irs_used_vars) /\
  apply_groups_inst_supply mode (nop_ids_of_groups dfg mode is gs)
    (rep_map_of_groups is gs) es (EL n is) = (chunk,es') ==>
  ?t'. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx chunk t t' /\
    mm_local_payload_cut cap is gs H (SUC n) excluded (pc + LENGTH chunk) t'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  qabbrev_tac `ns = nop_ids_of_groups dfg mode is gs` >>
  qabbrev_tac `rs = rep_map_of_groups is gs` >>
  Cases_on `MEM (EL n is).inst_id ns`
  >- (`?g. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids` by
        metis_tac[mm_local_nop_group_member] >>
      `chunk = [mk_nop_from (EL n is)] /\ es' = es` by
        gvs[apply_groups_inst_supply_def] >>
      SUBGOAL_THEN ``((EL n is).inst_opcode = mode_load_opcode mode) \/
        (EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}`` ASSUME_TAC
      >- (Cases_on `(EL n is).inst_opcode = mode_load_opcode mode` >- simp[] >>
         Cases_on `(EL n is).inst_opcode = mode_copy_opcode mode`
         >- (Cases_on `mode` >> gvs[mode_copy_opcode_def]) >>
         Cases_on `(EL n is).inst_opcode = MSTORE` >- simp[] >>
         metis_tac[mm_local_prefix_nonselected_group_absent]) >>
      `?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
          mm_local_payload_cut cap is gs H (SUC n) excluded (pc + LENGTH chunk) t'` by
        (qpat_x_assum `(EL n is).inst_opcode = mode_load_opcode mode \/ _` strip_assume_tac
         >- (`(EL n is).inst_opcode NOTIN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
               (Cases_on `mode` >> gvs[mode_load_opcode_def]) >>
             `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n` by
               metis_tac[mm_local_nonwrite_successor] >>
             `!v. MEM v (EL n is).inst_outputs ==> v IN excluded` by metis_tac[] >>
             mp_tac (SPEC_ALL mm_local_payload_erased_load_transition) >>
             (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
             qexists `t with vs_inst_idx := SUC pc` >> gvs[arithmeticTheory.ADD1]) >>
         `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]` by
           metis_tac[mm_local_erased_write_pending_suc] >>
         `?c. cap n = SOME (c.cg_dst,
           mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w) c.cg_src c.cg_length)` by
           (mp_tac (Q.INST [`j` |-> `n`, `N` |-> `LENGTH is`]
              (SPEC_ALL mm_local_payload_selected_capture_birth)) >>
            impl_tac >- metis_tac[] >> metis_tac[]) >>
         mp_tac (Q.INST [`N` |-> `LENGTH is`, `d` |-> `c.cg_dst`,
           `bs` |-> `mm_local_bytes (\a. if a < LENGTH cd then EL a cd else 0w)
             c.cg_src c.cg_length`]
           (SPEC_ALL mm_local_payload_erased_write_transition)) >>
         (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
         qexists `t with vs_inst_idx := SUC pc` >> gvs[arithmeticTheory.ADD1]) >>
      qexists `t'` >> simp[] >> irule mm_local_safe_exec_prefix_universal >>
      conj_tac
      >- simp[mk_nop_from_def, unitMemInvTheory.static_mem_ok_def,
        unitMemInvTheory.inst_mem_ranges_def,
        contextCodegenRelTheory.source_memory_read_ranges_def,
        codegenRelTheory.source_memory_write_ranges_def] >> gvs[]) >>
  Cases_on `ALOOKUP rs (EL n is).inst_id`
  >- (`chunk = [EL n is] /\ es' = es` by gvs[apply_groups_inst_supply_def] >>
      `!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded` by metis_tac[] >>
      `static_mem_ok eom ctx fn' (EL n is) t` by
        metis_tac[mm_local_payload_retained_static_if_forward] >>
      Cases_on `(EL n is).inst_opcode = DLOAD`
      >- (`mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n` by
            (mp_tac (SPEC_ALL mm_local_nonwrite_successor) >>
             (impl_tac >- gvs[]) >> simp[]) >>
          `state_equiv excluded
            ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t` by
            gvs[mm_local_payload_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
              stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
              venomStateTheory.venom_state_component_equality] >>
          `step_inst fuel ctx (EL n is)
            ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) =
            OK (u with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>)` by
            (qpat_x_assum `step_inst _ _ _ _ = OK u` mp_tac >>
             simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
             gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
               venomExecSemanticsTheory.exec_read1_def,
               venomStateTheory.eval_operand_def, AllCaseEqs(),
               venomStateTheory.update_var_def] >> strip_tac >> gvs[] >>
             rename1 `eval_operand op (H n) = SOME off` >> Cases_on `op` >>
             gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
          drule_all removeUnusedProofsTheory.step_inst_result_equiv_full >>
          disch_then (qspecl_then [`fuel`,`ctx`] mp_tac) >>
          Cases_on `step_inst fuel ctx (EL n is) t` >>
          simp[result_equiv_def] >> strip_tac >>
          `u.vs_memory = (H n).vs_memory /\ v.vs_memory = t.vs_memory` by
            (conj_tac
             >- (mp_tac (Q.INST [`mode` |-> `DloadMerge`, `i` |-> `EL (n:num) (is:instruction list)`,
                   `s` |-> `H (n:num)`, `t` |-> `u:venom_state`]
                   (SPEC_ALL mm_local_payload_load_frame)) >>
                 (impl_tac >- simp[mode_load_opcode_def]) >> simp[]) >>
             mp_tac (Q.INST [`mode` |-> `DloadMerge`, `i` |-> `EL (n:num) (is:instruction list)`,
               `s` |-> `t:venom_state`, `t` |-> `v:venom_state`]
               (SPEC_ALL mm_local_payload_load_frame)) >>
             (impl_tac >- simp[mode_load_opcode_def]) >> simp[]) >>
          qexists_tac `v with vs_inst_idx := SUC pc` >> conj_tac
          >- gvs[mm_local_safe_exec_prefix_def, mm_local_payload_cut_def] >>
          gvs[mm_local_payload_cut_def, state_equiv_frame, mm_local_nonmemory_frame_def,
            stateFrameTheory.state_frame_def, venomStateTheory.lookup_var_def,
            venomStateTheory.venom_state_component_equality] >>
          gvs[mm_local_pending_def] >> qexists_tac `ws` >> simp[] >>
          irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]) >>
      `((EL n is).inst_opcode IN {MSTORE; mode_copy_opcode mode} ==>
        ~(?g. MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids))` by
        (strip_tac >> irule mm_local_prefix_retained_write_unselected >>
         simp[Abbr `ns`,Abbr `rs`] >>
         Cases_on `mode` >> gvs[mode_copy_opcode_def] >> metis_tac[]) >>
      `bb.bb_instructions = TAKE n is ++ EL n is::DROP (SUC n) is` by
        (qspec_then `n` (qspec_then `is` mp_tac) rich_listTheory.TAKE_DROP_SUC >> simp[]) >>
      SUBGOAL_THEN ``scan_inst dfg mode (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE n is)) (EL n is) =
         hard_barrier (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE n is)) \/
        ~is_volatile_memory (EL n is)`` ASSUME_TAC
      >- (mp_tac (Q.INST [`pre` |-> `TAKE n is`, `post` |-> `DROP (SUC n) is`,
          `i` |-> `EL n is`, `ss` |-> `FOLDL (scan_inst dfg mode) empty_scan_state (TAKE n is)`]
          (SPEC_ALL mm_local_mem2mem_ordinary_classification)) >>
         (impl_tac >- metis_tac[]) >>
         qpat_x_assum `bb.bb_instructions = TAKE n is ++ EL n is::DROP (SUC n) is` kall_tac >>
         strip_tac >> simp[] >>
         Cases_on `mode` >> gvs[mode_load_opcode_def, is_volatile_memory_def,
           venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
           venomEffectsTheory.empty_effects_def]) >>
      qpat_x_assum `bb.bb_instructions = TAKE n is ++ EL n is::DROP (SUC n) is` kall_tac >>
      `?t'. mm_local_exec_prefix fuel ctx [EL n is] t t' /\
        mm_local_payload_cut cap is gs H (SUC n) excluded (SUC pc) t'` by
        (qpat_x_assum `_ \/ ~is_volatile_memory (EL n is)` strip_assume_tac
         >- (`mm_local_pending_indices is gs n = [] /\
              mm_local_pending_indices is gs (SUC n) = []` by
               metis_tac[mm_local_hard_barrier_pending_empty,mm_local_hard_barrier_pending_next_empty] >>
             irule mm_local_payload_barrier_transition >> metis_tac[]) >>
         `(EL n is).inst_opcode NOTIN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
           (simp[] >> rpt conj_tac >> strip_tac >>
            qpat_x_assum `~is_volatile_memory (EL n is)` mp_tac >>
            simp[is_volatile_memory_def, venomEffectsTheory.write_effects_def]) >>
         `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n` by
           metis_tac[mm_local_nonwrite_successor] >>
         irule mm_local_payload_nonvolatile_transition >> metis_tac[]) >>
      qexists `t'` >> gvs[mm_local_safe_exec_prefix_def,
        mm_local_exec_prefix_def, arithmeticTheory.ADD1]) >>
  `?g. MEM g gs /\ rep_of_group is g = SOME ((EL n is).inst_id,x)` by
    (drule alistTheory.ALOOKUP_MEM >>
     qpat_assum `Abbrev (rs = _)`
       (fn th => pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     pure_rewrite_tac[rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
     strip_tac >> rename1 `IS_SOME opt` >> Cases_on `opt` >> fs[] >> metis_tac[]) >>
  `g = x` by gvs[rep_of_group_def, AllCaseEqs()] >>
  `?t'. mm_local_exec_prefix fuel ctx chunk t t' /\
    mm_local_payload_cut cap is gs H (SUC n) excluded (pc + LENGTH chunk) t' /\
    (!w. EVERY (\i. static_mem_ok eom ctx fn' i w) chunk)` by
    (mp_tac (SPEC_ALL mm_local_payload_representative_transition) >>
     (impl_tac >- (simp[Abbr `ns`,Abbr `rs`] >> metis_tac[])) >> simp[]) >>
  qexists `t'` >> simp[] >> metis_tac[mm_local_safe_exec_prefix_universal]
QED

Theorem mm_local_payload_actual_safe_interval_if_forward[local]:
  !m n es t out es' pre.
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  dfg = dfg_build_function fn0 /\ is = bb.bb_instructions /\
  gs = (scan_block dfg mode bb).ss_flushed /\
  ns = nop_ids_of_groups dfg mode is gs /\ rs = rep_map_of_groups is gs /\
  f = apply_groups_inst_supply mode ns rs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  cap = mm_local_payload_capture mode is H (LENGTH is) /\
  h = phi_prefix_length is /\ h <= n /\ n + m <= LENGTH is /\
  (!j. (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
         else (H j).vs_data_section) = cd) /\
  (!j dst v src. j < LENGTH is /\ (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP src cd ++ REPLICATE 32 0w)))) /\
  (!j a bs. cap j = SOME (a,bs) ==> h <= j) /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ eom < dimword (:256) /\
  (!j. h <= j /\ j < n + m ==>
    (H j).vs_current_bb = bb.bb_label /\ (H j).vs_inst_idx = j /\
    static_mem_ok eom ctx fn (EL j is) (H j) /\
    ~is_terminator (EL j is).inst_opcode /\
    ?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
      H (SUC j) = u with vs_inst_idx := SUC j) /\
  (!j pref sj tj. h <= j /\ j < n + m /\
    mm_flat_map_supply f sk (TAKE j is) = (pref,sj) /\
    mm_local_payload_cut cap is gs H j excluded (LENGTH pref) tj ==>
    in_revert_forward fn (H j) ==> in_revert_forward fn' tj) /\
  mm_flat_map_supply f sk (TAKE n is) = (pre,es) /\
  mm_local_payload_cut cap is gs H n excluded (LENGTH pre) t /\
  mm_flat_map_supply f es (TAKE m (DROP n is)) = (out,es') ==>
  ?t'. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t t' /\
    mm_local_payload_cut cap is gs H (n + m) excluded (LENGTH pre + LENGTH out) t'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!j pref sj tj chunk sj'. n <= j /\ j < n + m /\
    mm_flat_map_supply f sk (TAKE j is) = (pref,sj) /\
    mm_local_payload_cut cap is gs H j excluded (LENGTH pref) tj /\
    f sj (EL j is) = (chunk,sj') ==>
    ?tj'. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx chunk tj tj' /\
      mm_local_payload_cut cap is gs H (SUC j) excluded
        (LENGTH pref + LENGTH chunk) tj'` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `h <= j /\ j < LENGTH is` by decide_tac >>
     `MEM (EL j is) bb.bb_instructions` by metis_tac[EL_MEM] >>
     `ir_supply_extends sk sj` by
       (drule_at (Pat `mm_flat_map_supply _ _ _ = (pref,sj)`) mm_local_list_resources >>
        (impl_tac >- metis_tac[mm_local_mode_resources]) >> simp[]) >>
     `?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
          H (SUC j) = u with vs_inst_idx := SUC j` by metis_tac[] >>
     `!v. chunk = [EL j is] /\ MEM (Var v) (EL j is).inst_operands ==>
       v NOTIN excluded` by
       (gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        `MEM v (venomInst$inst_uses (EL j is))` by
          metis_tac[venomWfPropsTheory.operand_var_in_inst_uses] >>
        mp_tac (Q.INST [`inst` |-> `EL (j:num) (is:instruction list)`,
          `es` |-> `sj:ir_supply`, `es'` |-> `sj':ir_supply`]
          (SPEC_ALL mm_local_retained_operand_protected)) >>
        (impl_tac >- (gvs[] >> metis_tac[EL_MEM])) >> simp[]) >>
     `!v. MEM (EL j is).inst_id ns /\
       (EL j is).inst_opcode = mode_load_opcode mode /\
       MEM v (EL j is).inst_outputs ==> v IN excluded` by
       (rpt strip_tac >> simp[] >> metis_tac[EL_MEM]) >>
     `!v. v NOTIN excluded ==> MEM v sj.irs_used_vars` by
       (gvs[ir_supply_extends_def,list_subset_def,EVERY_MEM] >> metis_tac[]) >>
     `!q a bs. q <= j /\ cap q = SOME (a,bs) ==> h <= q /\ q < n + m` by
       (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        conj_tac >- metis_tac[] >> decide_tac) >>
     `!q a bs. q <= j /\ cap q = SOME (a,bs) ==>
       (H q).vs_current_bb = bb.bb_label /\ (H q).vs_inst_idx = q /\
       static_mem_ok eom ctx fn (EL q is) (H q) /\
       ?u. step_inst fuel ctx (EL q is) (H q) = OK u` by
       (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        `h <= q /\ q < n + m` by metis_tac[] >>
        qpat_x_assum `!j. h <= j /\ j < n + m ==> _`
          (qspec_then `q` mp_tac) >> simp[] >> metis_tac[]) >>
     `(in_revert_forward fn (H j) ==> in_revert_forward fn' tj)` by
       (qpat_assum `!j pref sj tj. _`
         (qspecl_then [`j`,`pref`,`sj`,`tj`] mp_tac) >> simp[]) >>
     mp_tac (Q.INST [`n` |-> `j`, `es` |-> `sj`, `es'` |-> `sj'`,
       `t` |-> `tj`, `pc` |-> `LENGTH (pref:instruction list)`]
         (SPEC_ALL mm_local_payload_actual_safe_transition_if_forward)) >>
     (impl_tac >- (gvs[] >> rpt strip_tac >> metis_tac[])) >> simp[]) >>
  mp_tac (Q.INST [`supply` |-> `sk`,
    `P` |-> `static_mem_ok eom ctx fn'`,
    `Inv` |-> `\j pc (sj:ir_supply) tj. mm_local_payload_cut cap is gs H j excluded pc tj`]
      (SPEC_ALL (INST_TYPE [alpha |-> ``:ir_supply``, beta |-> ``:instruction``]
        mm_local_safe_flatmap_interval))) >>
  (impl_tac >- gvs[]) >> simp[]
QED

Theorem mm_local_payload_post_phi_pair[local]:
  mode IN {CalldataMerge; DloadMerge} /\
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode is gs /\
  rs = rep_map_of_groups is gs /\
  deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  transform_block_mode_supply (dfg_build_function fn0) mode sk bb = (bb',sk') /\
  s.vs_inst_idx = phi_prefix_length is /\ s.vs_current_bb = bb.bb_label /\
  state_equiv excluded s t0 /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  eom < dimword (:256) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn bb s) /\
  ~(?err. exec_block fuel ctx bb s = Error err) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (exec_block fuel ctx bb s) (exec_block fuel ctx bb' t0) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn' bb' t0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `h = phi_prefix_length is` >>
  qabbrev_tac `f = apply_groups_inst_supply mode ns rs` >>
  `t0.vs_inst_idx = h` by gvs[state_equiv_def] >>
  `h <= LENGTH is` by simp[Abbr `h`,venomExecProofsTheory.phi_prefix_length_le] >>
  `EVERY (\i. i.inst_opcode = PHI) (TAKE h is)` by
    simp[Abbr `h`,analysisSimProofsBaseTheory.phi_prefix_all_phi] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `mm_flat_map_supply f sk (TAKE h is) = (TAKE h is,sk)` by
    (simp[Abbr `f`] >> irule mm_local_mem2mem_phi_emission >>
     qexistsl [`bb`,`fn0`,`gs`,`index`,`k`,`sk`,`supply`] >>
     simp[Abbr `h`,EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
     conj_tac >- metis_tac[MEM_TAKE] >>
     qspec_then `bb.bb_instructions` (mp_tac o REWRITE_RULE[EVERY_MEM])
       analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `?n H. h <= n /\ n < LENGTH is /\ H h = s /\
    (!q. h <= q /\ q <= n ==>
      (H q).vs_inst_idx = q /\ (H q).vs_current_bb = bb.bb_label /\
      static_mem_ok eom ctx fn (EL q is) (H q)) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q is).inst_opcode /\
      ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (is_terminator (EL n is).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n is) (H n) = OK u)) /\
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [EL n is] (H n) /\
    (!j. (if mode = CalldataMerge then (H j).vs_call_ctx.cc_calldata
          else (H j).vs_data_section) =
      (if mode = CalldataMerge then s.vs_call_ctx.cc_calldata else s.vs_data_section)) /\
    (!j dst v src. j < LENGTH is /\ (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state
        (TAKE j is)).ss_loads v = SOME src ==>
      lookup_var v (H j) = SOME (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP src
          (if mode = CalldataMerge then s.vs_call_ctx.cc_calldata else s.vs_data_section)
          ++ REPLICATE 32 0w))))` by
    (irule mm_local_payload_stopping_history >> simp[Abbr `h`] >> metis_tac[]) >>
  qabbrev_tac `cap = mm_local_payload_capture mode is H (LENGTH is)` >>
  `!j a bs. cap j = SOME (a,bs) ==> h <= j` by
    (rpt strip_tac >> spose_not_then strip_assume_tac >>
     `j < h /\ j < LENGTH is` by decide_tac >>
     `(EL j is).inst_opcode = PHI` by
       (qpat_x_assum `EVERY _ (TAKE h is)`
             (fn th => mp_tac (Q.SPEC `j` (REWRITE_RULE[EVERY_EL] th))) >>
           simp[LENGTH_TAKE,EL_TAKE] >> gvs[LENGTH_TAKE,EL_TAKE] >> decide_tac) >>
     Cases_on `mode` >>
     gvs[Abbr `cap`,mm_local_payload_capture_def,mm_local_write_capture_def,
       mode_copy_opcode_def]) >>
  `wf_function (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (irule mm_local_prefix_function_wf >> metis_tac[wf_ssa_def]) >>
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by simp[MEM_LUPDATE] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (mp_tac (Q.SPECL [`fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks`, `bb`]
      venomExecProofsTheory.wf_lookup_block) >> simp[]) >>
  `!j pref sj tj. h <= j /\ j <= n /\
    mm_flat_map_supply f sk (TAKE j is) = (pref,sj) /\
    mm_local_payload_cut cap is gs H j excluded (LENGTH pref) tj ==>
    in_revert_forward fn (H j) ==> in_revert_forward fn' tj` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
     `(H j).vs_current_bb = bb.bb_label` by metis_tac[] >>
     `tj.vs_current_bb = bb.bb_label /\ tj.vs_inst_idx = LENGTH pref` by
       (qpat_assum `mm_local_payload_cut _ _ _ _ _ _ _ tj` mp_tac >>
        simp[NoAsms,mm_local_payload_cut_def,mm_local_nonmemory_frame_def,
          stateFrameTheory.state_frame_def,venomStateTheory.venom_state_component_equality] >>
        strip_tac >> gvs[] >> metis_tac[]) >>
     mp_tac (Q.INST [`n` |-> `j`,`pre` |-> `pref`,`sn` |-> `sj`,
       `s` |-> `H (j:num)`,`t` |-> `tj`] (SPEC_ALL mm_local_prefix_in_revert_forward)) >>
     (impl_tac >- (gvs[Abbr `f`] >> metis_tac[])) >> simp[]) >>
  Cases_on `mm_flat_map_supply f sk (TAKE (n-h) (DROP h is))` >>
  rename1 `mm_flat_map_supply f sk (TAKE (n-h) (DROP h is)) = (out,esn)` >>
  `mm_local_payload_cut cap is gs H h excluded (LENGTH (TAKE h is)) t0` by
    (irule mm_local_payload_cut_init >>
     (conj_tac >- simp[Abbr `h`]) >>
     `LENGTH (TAKE h is) = h` by simp[] >>
     `s with vs_inst_idx := h = s` by
       simp[Abbr `h`,venomStateTheory.venom_state_component_equality] >>
     metis_tac[]) >>
  `?t. mm_local_safe_exec_prefix (static_mem_ok eom ctx fn') fuel ctx out t0 t /\
    mm_local_payload_cut cap is gs H n excluded (h + LENGTH out) t` by
    (mp_tac (Q.INST [`m` |-> `n-h`, `n` |-> `h`, `es` |-> `sk`,
       `es'` |-> `esn`, `pre` |-> `TAKE h is`, `t` |-> `t0`,
       `dfg` |-> `dfg_build_function fn0`,
       `cd` |-> `if mode = CalldataMerge then s.vs_call_ctx.cc_calldata else s.vs_data_section`]
       (SPEC_ALL mm_local_payload_actual_safe_interval_if_forward)) >>
     `h + (n-h) = n` by decide_tac >>
     (impl_tac >- (gvs[Abbr `h`,Abbr `f`,Abbr `cap`] >> rpt strip_tac >>
       metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ])) >> simp[]) >>
  `mm_flat_map_supply f sk (TAKE n is) = (TAKE h is ++ out,esn)` by
    (`TAKE n is = TAKE h is ++ TAKE (n-h) (DROP h is)` by
       (`h + (n-h) = n` by decide_tac >>
        mp_tac (Q.SPECL [`h`,`n-h`,`is`] (INST_TYPE [alpha |-> ``:instruction``] listTheory.TAKE_SUM)) >>
        asm_rewrite_tac[]) >>
     asm_rewrite_tac[] >> irule mm_local_flat_map_supply_append >>
     qexists `sk` >> qpat_x_assum `is = _` SUBST_ALL_TAC >> simp[]) >>
  `~(?err. step_inst fuel ctx (EL n is) (H n) = Error err)` by
    (Cases_on `step_inst fuel ctx (EL n is) (H n)` >> gvs[dft_exec_suffix_def]) >>
  `(!es. f es (EL n is) = ([EL n is],es)) /\
    (!v. MEM (Var v) (EL n is).inst_operands ==> v NOTIN excluded)` by
    (mp_tac (Q.INST [`s` |-> `H (n:num)`]
       (SPEC_ALL mm_local_mode_stopping_unchanged)) >>
     (impl_tac >- asm_rewrite_tac[]) >> simp[Abbr `f`]) >>
  `(in_revert_forward fn (H n) ==> in_revert_forward fn' t)` by
    (qpat_assum `!j pref sj tj. _`
       (qspecl_then [`n`,`TAKE h is ++ out`,`esn`,`t`] mp_tac) >> simp[] >> gvs[]) >>
  `static_mem_ok eom ctx fn' (EL n is) t` by
    (irule mm_local_payload_retained_static_if_forward >>
     qexistsl [`H`,`cap`,`excluded`,`fn`,`gs`,`is`,`n`,`h + LENGTH out`] >>
     simp[] >> metis_tac[]) >>
  `lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [EL n is] (H n))
    (dft_exec_suffix fuel ctx [EL n is] t)` by
    (Cases_on `is_terminator (EL n is).inst_opcode`
     >- (`bb_well_formed bb` by
           (irule (cj 1 mm_local_prefix_wf_last) >>
            qexistsl [`fn0`,`index`,`k`,`sk`,`supply`] >>
            gvs[venomWfTheory.wf_ssa_def,ir_supply_covers_fn_def,
              irSupplyTheory.fn_ir_inst_ids_def,irSupplyTheory.block_ir_inst_ids_def,
              EVERY_MEM,MEM_FLAT,MEM_MAP] >> metis_tac[EL_MEM,MEM_MAP]) >>
         `SUC n = LENGTH is` by
           (qpat_x_assum `bb_well_formed bb` mp_tac >>
            simp[venomWfTheory.bb_well_formed_def] >> strip_tac >>
            `n = PRE (LENGTH is)` by metis_tac[] >>
            qpat_x_assum `is = _` (fn th => SUBST_ALL_TAC (SYM th)) >> decide_tac) >>
         `mm_local_pending_indices is gs n = []` by
           metis_tac[mm_local_mode_terminal_pending_empty] >>
         irule mm_local_payload_terminator_result >> metis_tac[]) >>
     `((EL n is).inst_opcode = INVOKE ==> mm_local_pending_indices is gs n = [])` by
       (strip_tac >>
        mp_tac (Q.INST [`ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) mode)
          empty_scan_state (TAKE n is)`]
          (SPEC_ALL mm_local_hard_barrier_pending_empty)) >>
        (impl_tac >- (asm_rewrite_tac[] >> Cases_on `mode` >>
          gvs[scan_inst_def,mode_copy_opcode_def,mode_load_opcode_def,
            is_volatile_memory_def,venomEffectsTheory.read_effects_def,
            venomEffectsTheory.write_effects_def,venomEffectsTheory.all_effects_def])) >>
        simp[]) >>
     `lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
       (step_inst fuel ctx (EL n is) (H n)) (step_inst fuel ctx (EL n is) t)` by
       (irule mm_local_payload_nonterminator_stop >> metis_tac[]) >>
     qpat_x_assum `lift_result (\_ _. F) _ _ _ _` mp_tac >>
     Cases_on `step_inst fuel ctx (EL n is) (H n)` >>
     Cases_on `step_inst fuel ctx (EL n is) t` >>
     simp[lift_result_def,dft_exec_suffix_def]) >>
  `is_terminator (EL n is).inst_opcode \/ ~(?u. step_inst fuel ctx (EL n is) t = OK u)` by
    (qpat_x_assum `is = _` kall_tac >>
     Cases_on `is_terminator (EL n is).inst_opcode` >> simp[] >>
     qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
     simp[dft_exec_suffix_def] >>
     Cases_on `step_inst fuel ctx (EL n is) (H n)` >> fs[] >>
     Cases_on `step_inst fuel ctx (EL n is) t` >> simp[lift_result_def]) >>
  `mm_flat_map_supply f sk is = (bb'.bb_instructions,sk')` by
    (qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
     simp[transform_block_mode_supply_def,Abbr `f`] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `mm_local_exec_prefix fuel ctx out t0 t` by
    metis_tac[mm_local_safe_exec_prefix_erase] >>
  (conj_tac
  >- (mp_tac (Q.INST [`pre` |-> `TAKE h is`, `supply` |-> `sk`,
        `fin` |-> `sk'`, `s` |-> `H (n:num)`,
        `rok` |-> `\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0)`,
        `rhalt` |-> `execution_equiv excluded`, `rabort` |-> `revert_equiv`]
        (SPEC_ALL (INST_TYPE [alpha |-> ``:ir_supply``] mm_local_emitted_stopping_result))) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> gvs[]) >>
  mp_tac (Q.INST [`pre` |-> `TAKE h is`, `supply` |-> `sk`,
    `fin` |-> `sk'`, `P` |-> `static_mem_ok eom ctx`,
    `Inv` |-> `\c fn i s. T`] (SPEC_ALL (INST_TYPE [alpha |-> ``:ir_supply``] mm_local_emitted_stopping_trace))) >>
  (impl_tac >- (simp[contextCodegenRelTheory.reachability_closed_def,
    contextCodegenRelTheory.fn_entry_inv_def] >> metis_tac[])) >> simp[] >> gvs[])
QED

Theorem mm_local_mode_function_correct:
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] = SOME mode /\
  transform_block_mode_supply (dfg_build_function fn0) mode sk bb = (bb',sk') /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  fn_entry_state fn s /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eom < dimword (:256) /\
  EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn s) /\
  ~(?err. run_function fuel ctx fn s = Error err) ==>
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (run_function fuel ctx fn s) (run_function fuel ctx fn' s) /\
  EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn' s)
Proof
  strip_tac >>
  `k <= 4` by decide_tac >>
  `fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ all_reachable fn /\
    ir_supply_covers_fn sk fn /\ fn_entry_label fn = fn_entry_label fn0` by
    metis_tac[mm_local_prefix_structure] >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk')` by simp[mm_local_phase_def] >>
  `fn_entry_label fn' = fn_entry_label fn0` by
    metis_tac[mm_local_phase_structure] >>
  `MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])` by
    (`k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >> gvs[]) >>
  qabbrev_tac `is = bb.bb_instructions` >>
  qabbrev_tac `gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed` >>
  qabbrev_tac `ns = nop_ids_of_groups (dfg_build_function fn0) mode is gs` >>
  qabbrev_tac `rs = rep_map_of_groups is gs` >>
  qabbrev_tac `deleted = {v | ?q. MEM q is /\ MEM q.inst_id ns /\ MEM v q.inst_outputs}` >>
  qabbrev_tac `excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted}` >>
  qabbrev_tac `h = phi_prefix_length is` >>
  qabbrev_tac `R = \a b. state_equiv excluded
    (a with vs_inst_idx := 0) (b with vs_inst_idx := 0)` >>
  qabbrev_tac `P = \((p,d,id),f,i,t):list_visit.
    p = [] ==> static_mem_ok eom ctx f i t` >>
  `EVERY (\i. i.inst_opcode = PHI ==>
    !v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) bb.bb_instructions /\
   (!cb i v. MEM cb fn0.fn_blocks /\ cb.bb_label <> bb.bb_label /\
     MEM i cb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v NOTIN excluded)` by
    (mp_tac mm_local_mode_entry_operands >>
     (impl_tac >- simp[Abbr `is`,Abbr `gs`,Abbr `ns`,Abbr `deleted`,Abbr `excluded`]) >>
     simp[]) >>
  `MEM bb fn.fn_blocks` by
    (simp[MEM_EL] >> qexists `index` >> simp[EL_LUPDATE]) >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (simp[Abbr `is`] >> metis_tac[mm_local_prefix_wf_id_distinct]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (DROP h is)` by
    (simp[Abbr `h`,Abbr `is`] >>
     irule simplifyCfgFixupStaticTheory.scfg_phi_suffix_nonphi >>
     qpat_x_assum `bb_well_formed bb` mp_tac >>
     pure_rewrite_tac[bb_well_formed_def] >> strip_tac >>
     first_assum MATCH_ACCEPT_TAC) >>
  Cases_on `mm_flat_map_supply (apply_groups_inst_supply mode ns rs) sk (DROP h is)` >>
  rename1 `mm_flat_map_supply (apply_groups_inst_supply mode ns rs) sk (DROP h is) = (out,es)` >>
  `phi_prefix_length bb'.bb_instructions = h /\
    (!z. eval_phis z bb'.bb_instructions = eval_phis z bb.bb_instructions)` by
    (mp_tac (Q.INST [`phis` |-> `TAKE h is`, `tail_insts` |-> `DROP h is`]
       mm_local_mem2mem_phi_boundary) >>
     (impl_tac >- simp[Abbr `h`,Abbr `is`,Abbr `gs`,Abbr `ns`,Abbr `rs`,
       analysisSimProofsBaseTheory.phi_prefix_all_phi]) >>
     strip_tac >>
     `bb'.bb_instructions = TAKE h is ++ out` by
       (qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
        fs[Abbr `is`,Abbr `gs`,Abbr `ns`,Abbr `rs`] >>
        simp[transform_block_mode_supply_def,AllCaseEqs()] >>
        rpt strip_tac >> gvs[]) >>
     simp[Abbr `h`,Abbr `is`]) >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def,irSupplyTheory.fn_ir_inst_ids_def,
       irSupplyTheory.block_ir_inst_ids_def,EVERY_MEM,MEM_FLAT,MEM_MAP] >>
     metis_tac[EL_MEM,MEM_MAP]) >>
  `bb.bb_label = (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mm_local_prefix_wf_last,wf_ssa_def] >>
  `bb'.bb_label = bb.bb_label` by
    metis_tac[mmSupplyWfProofsTheory.transform_block_mode_supply_label] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn0.fn_blocks)` by
    fs[wf_function_def,venomInstTheory.fn_labels_def] >>
  `!lbl. lookup_block lbl fn.fn_blocks =
    if lbl = bb.bb_label then SOME bb else lookup_block lbl fn0.fn_blocks` by
    (gen_tac >> qspecl_then [`fn0.fn_blocks`,`index`,`bb`,`lbl`] mp_tac
       venomTransformStructurePropsTheory.lookup_block_lupdate >> simp[]) >>
  `!lbl. lookup_block lbl fn'.fn_blocks =
    if lbl = bb.bb_label then SOME bb' else lookup_block lbl fn0.fn_blocks` by
    (gen_tac >> qspecl_then [`fn0.fn_blocks`,`index`,`bb'`,`lbl`] mp_tac
       venomTransformStructurePropsTheory.lookup_block_lupdate >> simp[]) >>
  `!n d a b. R a b /\ EVERY P (trace_blocks [] d n ctx fn a) /\
    ~(?err. run_blocks n ctx fn a = Error err) ==>
    lift_result R (execution_equiv excluded) revert_equiv
      (run_blocks n ctx fn a) (run_blocks n ctx fn' b) /\
    EVERY P (trace_blocks [] d n ctx fn' b)` suffices_by
  (strip_tac >> mp_tac (Q.INST [`Q` |-> `P`,`Rt` |-> `execution_equiv excluded`,
    `Ra` |-> `revert_equiv`] venomExecutionReplayPropsTheory.function_pair) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    simp[Abbr `R`,state_equiv_def,execution_equiv_def,
      stateFrameTheory.execution_frame_def,venomStateTheory.lookup_var_def])) >>
  disch_then (qspecl_then [`fuel`,`s`,`s`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    simp[Abbr `R`,state_equiv_def,execution_equiv_def])) >>
  simp[Abbr `P`] >> metis_tac[venomExecutionReplayPropsTheory.function_forget_vars]) >>
    (mp_tac (Q.INST [`Q` |-> `P`, `Rt` |-> `execution_equiv excluded`,
       `Ra` |-> `revert_equiv`] venomExecutionReplayPropsTheory.blocks_pair) >>
     (impl_tac >- (conj_tac
     >- simp[Abbr `R`,state_equiv_def,execution_equiv_def,
          stateFrameTheory.execution_frame_def,venomStateTheory.lookup_var_def] >>
     map_every qx_gen_tac [`fuel1`,`d`,`a`,`b`,`cb`] >> strip_tac >>
     `a.vs_current_bb = b.vs_current_bb` by fs[Abbr `R`,state_equiv_def] >>
     `a.vs_current_bb = cb.bb_label` by
       metis_tac[venomExecProofsTheory.lookup_block_label] >>
     Cases_on `a.vs_current_bb <> bb.bb_label`
     >- (     `b.vs_current_bb <> bb.bb_label` by metis_tac[] >>
     `lookup_block a.vs_current_bb fn0.fn_blocks = SOME cb` by
       (qpat_x_assum `lookup_block a.vs_current_bb fn.fn_blocks = SOME cb` mp_tac >> simp[]) >>
     `MEM cb fn0.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
     `lookup_block b.vs_current_bb fn'.fn_blocks = SOME cb` by
       (qpat_assum `!lbl. lookup_block lbl fn'.fn_blocks = _`
         (qspec_then `b.vs_current_bb` mp_tac) >> simp[] >> metis_tac[]) >>
     qexists_tac `cb` >> simp[] >>
     mp_tac (Q.INST [`s` |-> `a`,`t` |-> `b`,`fuel` |-> `fuel1`,`bb` |-> `cb`]
       venomExecutionReplayPropsTheory.same_run_block_correct) >>
     (impl_tac >- (asm_rewrite_tac[] >> fs[Abbr `R`,Abbr `P`] >> metis_tac[])) >>
     simp[Abbr `R`,Abbr `P`]) >>
     `a.vs_current_bb = bb.bb_label` by fs[] >>
     `lookup_block a.vs_current_bb fn.fn_blocks = SOME bb` by
           (qpat_assum `!lbl. lookup_block lbl fn.fn_blocks = _`
             (fn th => pure_rewrite_tac[SPEC ``a.vs_current_bb`` th]) >>
            asm_rewrite_tac[]) >>
         `cb = bb` by metis_tac[optionTheory.SOME_11] >>
         qpat_x_assum `cb = bb` SUBST_ALL_TAC >>
         `b.vs_current_bb = bb.bb_label` by metis_tac[] >>
         qexists_tac `bb'` >> conj_tac
         >- (qpat_assum `!lbl. lookup_block lbl fn'.fn_blocks = _`
               (fn th => pure_rewrite_tac[SPEC ``b.vs_current_bb`` th]) >>
             qpat_assum `b.vs_current_bb = bb.bb_label`
               (fn th => rewrite_tac[th])) >>
         mp_tac (Q.INST [`s` |-> `a`, `t` |-> `b`, `fuel` |-> `fuel1`,
           `d` |-> `SUC d`, `Rt` |-> `execution_equiv excluded`,
           `Ra` |-> `revert_equiv`] venomExecutionReplayPropsTheory.run_block_pair) >>
         (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
           qx_gen_tac `sp` >> strip_tac >>
           `?tp. eval_phis b bb.bb_instructions = OK tp /\
             state_equiv excluded (sp with vs_inst_idx := h) (tp with vs_inst_idx := h)` by
             (irule venomExecutionReplayPropsTheory.phi_entry_pair >> fs[Abbr `R`] >> metis_tac[]) >>
           qexists_tac `tp` >> conj_tac >- metis_tac[] >>
           `sp.vs_current_bb = bb.bb_label` by
             metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
           `EVERY (\((p,d',id),f,i,t). p=[] ==> static_mem_ok eom ctx f i t)
             (trace_block [] (SUC d) fuel1 ctx fn bb (sp with vs_inst_idx := h))` by
             (mp_tac (Q.INST [`p` |-> `[]`,`s` |-> `a`,`fuel` |-> `fuel1`]
               dftGasFromListTraceDefsTheory.trace_blocks_enter) >>
              (impl_tac >- asm_rewrite_tac[]) >>
              disch_then (fn th =>
                qpat_x_assum `EVERY P (trace_blocks _ _ _ _ _ _)`
                  (mp_tac o REWRITE_RULE [th])) >>
              simp[Abbr `P`,Abbr `h`,Abbr `is`,EVERY_APPEND]) >>
           `~(?err. exec_block fuel1 ctx bb (sp with vs_inst_idx := h) = Error err)` by
             (qpat_x_assum `~(?err. run_block fuel1 ctx bb a = Error err)` mp_tac >>
              simp[venomExecSemanticsTheory.run_block_def,Abbr `h`,Abbr `is`]) >>
           Cases_on `mode = Mem2Mem`
           >- (qpat_x_assum `mode = Mem2Mem` SUBST_ALL_TAC >>
               conj_tac
               >- (mp_tac (Q.INST [`s` |-> `sp with vs_inst_idx := h`,
                     `t0` |-> `tp with vs_inst_idx := h`, `fuel` |-> `fuel1`,
                     `d` |-> `SUC d`] mm_local_mem2mem_post_phi_result) >>
                   (impl_tac >- (simp[Abbr `is`,Abbr `gs`,Abbr `ns`,Abbr `rs`,
                      Abbr `deleted`,Abbr `excluded`,Abbr `h`] >> metis_tac[])) >>
                   simp[Abbr `R`,Abbr `h`,Abbr `is`]) >>
               mp_tac (Q.INST [`s` |-> `sp with vs_inst_idx := h`,
                 `t0` |-> `tp with vs_inst_idx := h`, `fuel` |-> `fuel1`,
                 `d` |-> `SUC d`] mm_local_mem2mem_post_phi_trace) >>
               (impl_tac >- (simp[Abbr `is`,Abbr `gs`,Abbr `ns`,Abbr `rs`,
                  Abbr `deleted`,Abbr `excluded`,Abbr `h`] >> metis_tac[])) >>
               simp[Abbr `P`,Abbr `h`,Abbr `is`]) >>
           `mode IN {CalldataMerge;DloadMerge}` by (Cases_on `mode` >> gvs[]) >>
           mp_tac (Q.INST [`s` |-> `sp with vs_inst_idx := h`,
             `t0` |-> `tp with vs_inst_idx := h`, `fuel` |-> `fuel1`,
             `d` |-> `SUC d`] mm_local_payload_post_phi_pair) >>
           (impl_tac >- (simp[Abbr `is`,Abbr `gs`,Abbr `ns`,Abbr `rs`,
              Abbr `deleted`,Abbr `excluded`,Abbr `h`] >> metis_tac[])) >>
           simp[Abbr `R`,Abbr `P`,Abbr `h`,Abbr `is`])) >> simp[])) >> simp[])
QED

