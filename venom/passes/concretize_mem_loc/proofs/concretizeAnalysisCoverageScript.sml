(* Local static allocation-base coverage only: no runtime-origin assertion. *)
Theory concretizeAnalysisCoverage
Ancestors concretizeAnalysisBaseModel concretizeAnalysisScan singleWriterScan
  concretizeAnalysisSupport concretizeAnalysisBoundary concretizeMemLocDefs
  basePtrDefs basePtrProofs ptrDiscipline venomWf venomInst list pred_set
  finite_map relation arithmetic mem2varProofs

Theorem bp_descriptor_stream_member:
  !is d. MEM d (bp_descriptor_stream is) <=>
         ?i. MEM i is /\ bp_descriptor i = SOME d
Proof
  Induct >> simp[bp_descriptor_stream_def] >> rpt gen_tac >>
  Cases_on `bp_descriptor h` >> simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM, EQ_SYM_EQ]
QED

Theorem bp_descriptor_out:
  bp_descriptor i = SOME d ==> inst_output i = SOME (sw_out d)
Proof
  Cases_on `inst_output i` >> simp[bp_descriptor_def] >>
  Cases_on `i.inst_opcode` >> simp[bp_descriptor_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[sw_out_def]
QED

Theorem bp_descriptor_stream_consistent:
  ssa_form fn /\ EVERY (\i. MEM i (fn_insts fn)) is ==>
  sw_consistent (bp_descriptor_stream is)
Proof
  simp[sw_consistent_def, bp_descriptor_stream_member] >> rpt strip_tac >>
  `i = i'` suffices_by (strip_tac >> gvs[]) >>
  `inst_output i = SOME (sw_out d)` by metis_tac[bp_descriptor_out] >>
  `inst_output i' = SOME (sw_out d)` by metis_tac[bp_descriptor_out] >>
  irule ssa_alloca_output_unique >>
  conj_tac
  >- (qexists `fn` >> gvs[EVERY_MEM]) >>
  qexists `sw_out d` >> gvs[inst_output_def, AllCaseEqs()]
QED

Theorem bp_scan_descriptor_consistent:
  ssa_form fn ==> sw_consistent (bp_descriptor_stream (bp_scan_insts fn order))
Proof
  strip_tac >> irule bp_descriptor_stream_consistent >>
  qexists `fn` >> simp[EVERY_MEM] >> metis_tac[bp_scan_insts_member]
QED

Theorem bp_unconditional_descriptor_refines:
  !n r. fn_ptr_ok P fn /\ ssa_form fn /\
    bp_supported (fn_pv P fn) r /\
    sw_admissible (bp_descriptor_stream (bp_scan_insts fn order)) (bp_bases r) ==>
    bp_bases (bp_unconditional_passes n fn order r) =
    FUNPOW (sw_scan (bp_descriptor_stream (bp_scan_insts fn order))) n (bp_bases r)
Proof
  Induct >> simp[bp_unconditional_passes_def] >> rpt gen_tac >> strip_tac >>
  `sw_consistent (bp_descriptor_stream (bp_scan_insts fn order))` by
    simp[bp_scan_descriptor_consistent] >>
  `EVERY (\i. MEM i (fn_insts fn)) (bp_scan_insts fn order)` by
    (simp[EVERY_MEM] >> metis_tac[bp_scan_insts_member]) >>
  `bp_bases (SND (bp_one_pass fn order r)) =
   sw_scan (bp_descriptor_stream (bp_scan_insts fn order)) (bp_bases r)` by
    (simp[bp_one_pass_scan] >> irule bp_process_block_descriptor_refines >>
     conj_tac >- (qexistsl [`P`, `fn`] >> simp[]) >>
     qexists `bp_descriptor_stream (bp_scan_insts fn order)` >> simp[EVERY_MEM]) >>
  `sw_admissible (bp_descriptor_stream (bp_scan_insts fn order))
     (bp_bases (SND (bp_one_pass fn order r)))` by
    (simp[] >> irule sw_scan_admissible >> simp[EVERY_MEM]) >>
  `bp_supported (fn_pv P fn) (SND (bp_one_pass fn order r))` by
    simp[bp_one_pass_def, bp_supported_fn_pass_aux] >>
  first_x_assum (qspec_then `SND (bp_one_pass fn order r)` mp_tac) >>
  simp[arithmeticTheory.FUNPOW]
QED

Theorem bp_iterate_descriptor_rounds:
  fn_ptr_ok P fn /\ ssa_form fn ==>
  bp_bases (bp_iterate_fuel n fn order FEMPTY) =
  sw_rounds (bp_descriptor_stream (bp_scan_insts fn order)) n
Proof
  strip_tac >>
  `bp_bases FEMPTY = (\v. {})` by
    simp[FUN_EQ_THM, bp_bases_def, bp_get_ptrs_def] >>
  `bp_bases (bp_iterate_fuel n fn order FEMPTY) =
   bp_bases (bp_unconditional_passes n fn order FEMPTY)` by
    (simp[FUN_EQ_THM, bp_bases_def, bp_iterate_fuel_unconditional_ptrs]) >>
  simp[] >>
  `bp_bases (bp_unconditional_passes n fn order FEMPTY) =
   FUNPOW (sw_scan (bp_descriptor_stream (bp_scan_insts fn order))) n (\v. {})` by
    (irule EQ_TRANS >>
     qexists `FUNPOW (sw_scan (bp_descriptor_stream (bp_scan_insts fn order))) n
       (bp_bases FEMPTY)` >> conj_tac
     >- (irule bp_unconditional_descriptor_refines >>
         simp[bp_supported_def, bp_get_ptrs_def, bp_bases_def, sw_bottom_admissible] >>
         qexists `P` >> simp[]) >>
     simp[bp_bases_def, bp_get_ptrs_def, combinTheory.K_DEF]) >>
  `!k. FUNPOW (sw_scan (bp_descriptor_stream (bp_scan_insts fn order))) k (\v. {}) =
       sw_rounds (bp_descriptor_stream (bp_scan_insts fn order)) k` by
    (Induct >> simp[sw_rounds_def, FUNPOW_SUC]) >> simp[]
QED

Theorem bp_local_base_coverage:
  fn_ptr_ok P fn /\ ssa_form fn /\
  sw_seed (bp_descriptor_stream (bp_scan_insts fn order)) a x /\
  RTC (sw_edge (bp_descriptor_stream (bp_scan_insts fn order))) x v /\
  CARD (IMAGE sw_out (set (bp_descriptor_stream (bp_scan_insts fn order)))) <= n ==>
  a IN bp_bases (bp_iterate_fuel n fn order FEMPTY) v
Proof
  strip_tac >>
  `sw_consistent (bp_descriptor_stream (bp_scan_insts fn order))` by
    simp[bp_scan_descriptor_consistent] >>
  drule_all sw_rounds_reachable >> strip_tac >>
  `sw_le (sw_rounds (bp_descriptor_stream (bp_scan_insts fn order))
          (CARD (IMAGE sw_out (set (bp_descriptor_stream (bp_scan_insts fn order))))))
         (sw_rounds (bp_descriptor_stream (bp_scan_insts fn order)) n)` by
    (irule sw_rounds_mono >> simp[]) >>
  `bp_bases (bp_iterate_fuel n fn order FEMPTY) =
    sw_rounds (bp_descriptor_stream (bp_scan_insts fn order)) n` by
    (irule bp_iterate_descriptor_rounds >> simp[] >> qexists `P` >> simp[]) >>
  gvs[sw_le_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem bp_descriptor_writer_bound:
  CARD (IMAGE sw_out (set (bp_descriptor_stream (bp_scan_insts fn order)))) <=
  LENGTH (fn_insts fn)
Proof
  `IMAGE sw_out (set (bp_descriptor_stream (bp_scan_insts fn order))) SUBSET
   IMAGE (\i. THE (inst_output i)) (set (fn_insts fn))` by
    (simp[SUBSET_DEF, IN_IMAGE, bp_descriptor_stream_member] >> rpt strip_tac >>
     qexists `i` >> drule bp_descriptor_out >>
     simp[] >> metis_tac[bp_scan_insts_member]) >>
  irule arithmeticTheory.LE_TRANS >>
  qexists `CARD (IMAGE (\i. THE (inst_output i)) (set (fn_insts fn)))` >>
  conj_tac >- (irule CARD_SUBSET >> simp[]) >>
  irule arithmeticTheory.LE_TRANS >> qexists `CARD (set (fn_insts fn))` >>
  simp[CARD_IMAGE_LE, CARD_LIST_TO_SET]
QED

Theorem bp_production_local_base_coverage:
  fn_ptr_ok P fn /\ ssa_form fn /\
  sw_seed (bp_descriptor_stream (bp_scan_insts fn order)) a x /\
  RTC (sw_edge (bp_descriptor_stream (bp_scan_insts fn order))) x v ==>
  a IN bp_bases (bp_iterate_fuel (concretize_memloc_fuel fn) fn order FEMPTY) v
Proof
  strip_tac >>
  `CARD (IMAGE sw_out (set (bp_descriptor_stream (bp_scan_insts fn order)))) <=
   concretize_memloc_fuel fn` by
    (mp_tac bp_descriptor_writer_bound >>
     simp[concretize_memloc_fuel_def]) >>
  metis_tac[bp_local_base_coverage]
QED

Theorem bp_analyze_production_local_base_coverage:
  fn_ptr_ok P fn /\ ssa_form fn /\
  sw_seed (bp_descriptor_stream (bp_scan_insts fn cfg.cfg_dfs_pre)) a x /\
  RTC (sw_edge (bp_descriptor_stream (bp_scan_insts fn cfg.cfg_dfs_pre))) x v ==>
  a IN bp_bases (bp_analyze_fuel (concretize_memloc_fuel fn) cfg fn) v
Proof
  simp[bp_analyze_fuel_def] >> metis_tac[bp_production_local_base_coverage]
QED

Theorem bp_local_base_path_coverage:
  !k x v. NRC (sw_edge (bp_descriptor_stream (bp_scan_insts fn order))) k x v ==>
  fn_ptr_ok P fn /\ ssa_form fn /\
  sw_seed (bp_descriptor_stream (bp_scan_insts fn order)) a x ==>
  a IN bp_bases (bp_iterate_fuel (SUC k) fn order FEMPTY) v
Proof
  Induct_on `k` >> simp[arithmeticTheory.NRC_SUC_RECURSE_LEFT, arithmeticTheory.NRC_0] >> rpt strip_tac
  >- (`sw_consistent (bp_descriptor_stream (bp_scan_insts fn order))` by
        simp[bp_scan_descriptor_consistent] >>
      drule_all sw_rounds_seed >> strip_tac >>
      `bp_bases (bp_iterate_fuel 1 fn order FEMPTY) =
       sw_rounds (bp_descriptor_stream (bp_scan_insts fn order)) 1` by
        metis_tac[bp_iterate_descriptor_rounds] >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `bp_bases (bp_iterate_fuel (SUC k) fn order FEMPTY) =
   sw_rounds (bp_descriptor_stream (bp_scan_insts fn order)) (SUC k)` by
    metis_tac[bp_iterate_descriptor_rounds] >>
  `sw_consistent (bp_descriptor_stream (bp_scan_insts fn order))` by
    simp[bp_scan_descriptor_consistent] >>
  gvs[] >> drule_all sw_rounds_edge >> strip_tac >>
  `bp_bases (bp_iterate_fuel (SUC (SUC k)) fn order FEMPTY) =
   sw_rounds (bp_descriptor_stream (bp_scan_insts fn order)) (SUC (SUC k))` by
    metis_tac[bp_iterate_descriptor_rounds] >> simp[]
QED
