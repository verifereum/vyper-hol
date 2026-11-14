(* Local memmerging phase: pending geometry and source exclusion. *)
Theory mmLocalPendingProofs
Ancestors
  venomFnInstsProofs venomInst memoryReadRel
  mmSupplyWfProofs mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner allocaRemapSSA o1MakeSsaCfg makeSsaCurrentWfSsa
  cfgWf venomWf stateEquiv rich_list mmTransform mmScan mmCopy list sorting
  simplifyCfgPhiSemantics simplifyCfgFixupStatic basePtrProofs mmTraceProofs frameViewMemory dftCommutation
  regularMemorySim rangeAnalysisProofs dftIndexedExec removeUnusedProofs analysisSimProofsBase
  mmLocalStructureProofs
  mmLocalCaptureProofs
  venomTransformStructureProps venomWriteReplayProps venomExecutionReplayProps irSupplyFreshProps
Libs
  wordsLib finite_mapLib stepInstBaseLib

Definition mm_local_pending_indices_def:
  mm_local_pending_indices is gs n = FILTER (\j.
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    ?g r. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      r < LENGTH is /\ n <= r /\
      rep_of_group is g = SOME ((EL r is).inst_id,g)) (COUNT_LIST n)
End

Theorem mm_local_pending_indices_mem:
  MEM j (mm_local_pending_indices is gs n) <=>
  j < n /\ (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  ?g r. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    r < LENGTH is /\ n <= r /\ rep_of_group is g = SOME ((EL r is).inst_id,g)
Proof
  simp[mm_local_pending_indices_def, MEM_FILTER, MEM_COUNT_LIST] >> metis_tac[]
QED

Definition mm_local_epoch_start_def:
  mm_local_epoch_start is gs n = MAX_LIST
    (FILTER (\q. mm_local_pending_indices is gs q = []) (COUNT_LIST (SUC n)))
End

Theorem mm_local_epoch_start_member[local]:
  MEM (mm_local_epoch_start is gs n)
    (FILTER (\q. mm_local_pending_indices is gs q = []) (COUNT_LIST (SUC n)))
Proof
  rewrite_tac[mm_local_epoch_start_def] >>
  irule rich_listTheory.MAX_LIST_MEM >>
  `MEM 0 (FILTER (\q. mm_local_pending_indices is gs q = []) (COUNT_LIST (SUC n)))`
    suffices_by (Cases_on `FILTER (\q. mm_local_pending_indices is gs q = [])
      (COUNT_LIST (SUC n))` >> simp[]) >>
  simp[MEM_FILTER, MEM_COUNT_LIST, mm_local_pending_indices_def,
    rich_listTheory.COUNT_LIST_def]
QED

Theorem mm_local_epoch_start_bound:
  a = mm_local_epoch_start is gs n ==> a <= n
Proof
  strip_tac >> mp_tac mm_local_epoch_start_member >>
  simp[MEM_FILTER, MEM_COUNT_LIST]
QED

Theorem mm_local_epoch_start_empty[local]:
  a = mm_local_epoch_start is gs n ==> mm_local_pending_indices is gs a = []
Proof
  strip_tac >> mp_tac mm_local_epoch_start_member >>
  simp[MEM_FILTER]
QED

Theorem mm_local_epoch_start_nonempty:
  a = mm_local_epoch_start is gs n /\ a <= q /\ q < n ==>
  ?b. MEM b (mm_local_pending_indices is gs (SUC q))
Proof
  strip_tac >>
  Cases_on `mm_local_pending_indices is gs (SUC q) = []`
  >- (`MEM (SUC q) (FILTER (\u. mm_local_pending_indices is gs u = [])
        (COUNT_LIST (SUC n)))` by simp[MEM_FILTER, MEM_COUNT_LIST] >>
      drule rich_listTheory.MAX_LIST_PROPERTY >>
      gvs[GSYM mm_local_epoch_start_def]) >>
  Cases_on `mm_local_pending_indices is gs (SUC q)` >> gvs[] >> metis_tac[]
QED

Theorem mm_local_epoch_start_pending_bound:
  a = mm_local_epoch_start is gs n /\ MEM j (mm_local_pending_indices is gs n) ==>
  a <= j
Proof
  strip_tac >>
  `a <= n` by metis_tac[mm_local_epoch_start_bound] >>
  `mm_local_pending_indices is gs a = []` by metis_tac[mm_local_epoch_start_empty] >>
  spose_not_then assume_tac >>
  `MEM j (mm_local_pending_indices is gs a)` suffices_by simp[] >>
  gvs[mm_local_pending_indices_mem] >>
  qexistsl [`g`, `r`] >> simp[] >> decide_tac
QED

Theorem mm_local_epoch_start_suc:
  mm_local_epoch_start is gs (SUC n) =
    if mm_local_pending_indices is gs (SUC n) = [] then SUC n
    else mm_local_epoch_start is gs n
Proof
  Cases_on `mm_local_pending_indices is gs (SUC n) = []`
  >- (simp[] >>
      `mm_local_epoch_start is gs (SUC n) <= SUC n` by
        metis_tac[mm_local_epoch_start_bound] >>
      `MEM (SUC n) (FILTER (\q. mm_local_pending_indices is gs q = [])
        (COUNT_LIST (SUC (SUC n))))` by simp[MEM_FILTER, MEM_COUNT_LIST] >>
      drule rich_listTheory.MAX_LIST_PROPERTY >>
      simp[GSYM mm_local_epoch_start_def]) >>
  simp[mm_local_epoch_start_def, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, FILTER_APPEND]
QED

Theorem mm_local_pending_indices_order:
  SORTED $< (mm_local_pending_indices is gs n) /\
  ALL_DISTINCT (mm_local_pending_indices is gs n)
Proof
  simp[mm_local_pending_indices_def] >> conj_tac
  >- (irule sortingTheory.SORTED_FILTER >>
      simp[sortingTheory.sorted_lt_count_list, relationTheory.transitive_def] >> decide_tac) >>
  irule FILTER_ALL_DISTINCT >> simp[rich_listTheory.all_distinct_count_list]
QED

Theorem mm_local_store_birth_every[local]:
  (!a b. P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\
  (!dst v src. inst.inst_operands = [Lit dst; Var v] /\
    FLOOKUP ss.ss_loads v = SOME src ==>
    P <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := inst.inst_id ::
           (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) |>) ==>
  mm_local_scan_every P (scan_store dfg mode ss inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[scan_store_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::ops` >>
  Cases_on `ops` >- simp[scan_store_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::value::ops` >>
  Cases_on `ops`
  >- (Cases_on `dst` >> Cases_on `value` >>
      simp[scan_store_def, operand_var_def, operand_lit_val_def,
        mm_local_barrier_every] >>
      rename1 `inst.inst_operands = [Lit addr; Var v]` >>
      Cases_on `FLOOKUP ss.ss_loads v` >- simp[mm_local_barrier_every] >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `flush_hazards mode ss0 cg` >>
      `P cg` by (simp[Abbr `cg`] >> metis_tac[]) >>
      `mm_local_scan_every P ss0` by
        (simp[Abbr `ss0`] >> IF_CASES_TAC >> simp[mm_local_invalidate_every]) >>
      drule mm_local_hazards_every >>
      disch_then (qspecl_then [`mode`, `cg`] assume_tac) >>
      gvs[mm_local_scan_every_def] >> irule mm_local_add_every >> simp[]) >>
  simp[scan_store_def, mm_local_barrier_every]
QED

Theorem mm_local_bulk_birth_every[local]:
  (!a b. P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\
  (!dst src len. inst.inst_operands = [Lit dst; Lit src; Lit len] ==>
    P <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [inst.inst_id] |>) ==>
  mm_local_scan_every P (scan_bulk_copy mode ss inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[scan_bulk_copy_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::ops` >>
  Cases_on `ops` >- simp[scan_bulk_copy_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::src::ops` >>
  Cases_on `ops` >- simp[scan_bulk_copy_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::src::len::ops` >>
  Cases_on `ops`
  >- (Cases_on `dst` >>
      simp[scan_bulk_copy_def, operand_lit_val_def, mm_local_barrier_every] >>
      Cases_on `src` >> simp[operand_lit_val_def, mm_local_barrier_every] >>
      Cases_on `len` >> simp[operand_lit_val_def, mm_local_barrier_every] >>
      qmatch_goalsub_abbrev_tac `flush_hazards mode ss0 cg` >>
      `P cg` by (simp[Abbr `cg`] >> metis_tac[]) >>
      `mm_local_scan_every P ss0` by
        (simp[Abbr `ss0`] >> IF_CASES_TAC >> simp[mm_local_invalidate_every]) >>
      drule mm_local_hazards_every >>
      disch_then (qspecl_then [`mode`, `cg`] assume_tac) >>
      gvs[mm_local_scan_every_def] >> irule mm_local_add_every >> simp[]) >>
  simp[scan_bulk_copy_def, mm_local_barrier_every]
QED

Theorem mm_local_inst_birth_every:
  (!a b. P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\
  (inst.inst_opcode = MSTORE ==>
    !dst v src. inst.inst_operands = [Lit dst; Var v] /\ FLOOKUP ss.ss_loads v = SOME src ==>
      P <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
        cg_inst_ids := inst.inst_id ::
          (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) |>) /\
  (inst.inst_opcode = mode_copy_opcode mode ==>
    !dst src len. inst.inst_operands = [Lit dst; Lit src; Lit len] ==>
      P <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
        cg_inst_ids := [inst.inst_id] |>) ==>
  mm_local_scan_every P (scan_inst dfg mode ss inst)
Proof
  strip_tac >> simp[scan_inst_def] >>
  IF_CASES_TAC >- (irule mm_local_load_every >> simp[]) >>
  IF_CASES_TAC >- (irule mm_local_store_birth_every >> metis_tac[]) >>
  IF_CASES_TAC >- (irule mm_local_bulk_birth_every >> metis_tac[]) >>
  rpt IF_CASES_TAC >> simp[mm_local_barrier_every]
QED

Definition mm_local_id_birth_def:
  mm_local_id_birth dfg mode is id <=> ?p. p < LENGTH is /\
    ((?dst src len. (EL p is).inst_opcode = mode_copy_opcode mode /\
       (EL p is).inst_operands = [Lit dst; Lit src; Lit len] /\ id = (EL p is).inst_id) \/
     (?dst v src. (EL p is).inst_opcode = MSTORE /\
       (EL p is).inst_operands = [Lit dst; Var v] /\
       FLOOKUP (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE p is)).ss_loads v = SOME src /\
       (id = (EL p is).inst_id \/ ?li. dfg_get_def dfg v = SOME li /\ id = li.inst_id)))
End

Theorem mm_local_birth_merge[local]:
  (!id. MEM id a.cg_inst_ids ==> mm_local_id_birth dfg mode is id) /\
  (!id. MEM id b.cg_inst_ids ==> mm_local_id_birth dfg mode is id) ==>
  !id. MEM id (copy_merge a b).cg_inst_ids ==> mm_local_id_birth dfg mode is id
Proof
  simp[copy_merge_def, MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_scan_births[local]:
  !t. t <= LENGTH is ==>
    mm_local_scan_every (\g. !id. MEM id g.cg_inst_ids ==> mm_local_id_birth dfg mode is id)
      (FOLDL (scan_inst dfg mode) empty_scan_state (TAKE t is))
Proof
  Induct >- simp[mm_local_scan_every_def, empty_scan_state_def] >>
  strip_tac >>
  `t < LENGTH is /\ t <= LENGTH is` by decide_tac >>
  simp[rich_listTheory.TAKE_SUC, FOLDL_APPEND] >>
  irule mm_local_inst_birth_every >>
  conj_tac >- metis_tac[mm_local_birth_merge] >>
  simp[] >> rpt conj_tac >> rpt strip_tac >>
  simp[mm_local_id_birth_def] >> qexists `t` >>
  simp[] >> Cases_on `dfg_get_def dfg v` >> gvs[]
QED

Theorem mm_local_final_write_birth:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\ is = bb.bb_instructions /\
  j < LENGTH is /\ MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
  (?dst src len. (EL j is).inst_opcode = mode_copy_opcode mode /\
    (EL j is).inst_operands = [Lit dst; Lit src; Lit len]) \/
  (?dst v src. (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `mm_local_scan_every
    (\g. !id. MEM id g.cg_inst_ids ==> mm_local_id_birth (dfg_build_function fn0) mode is id)
    (scan_block (dfg_build_function fn0) mode bb)` by
    (simp[scan_block_def] >> irule mm_local_barrier_every >>
     mp_tac (Q.SPEC `LENGTH (bb.bb_instructions)`
       (Q.INST [`dfg` |-> `dfg_build_function fn0`, `is` |-> `bb.bb_instructions`]
         mm_local_scan_births)) >> simp[]) >>
  `mm_local_id_birth (dfg_build_function fn0) mode is (EL j is).inst_id` by
    (gnvs[mm_local_scan_every_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `mm_local_id_birth _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mm_local_id_birth_def])
  >- (`p = j` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
      metis_tac[])
  >- (`p = j` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
      metis_tac[]) >>
  drule mm_local_scan_lookup_origin >> strip_tac >>
  `MEM q bb.bb_instructions /\ MEM v q.inst_outputs` by
    (gvs[] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  drule_all mm_local_prefix_producer_identify >> strip_tac >>
  `?a. a < LENGTH is /\ q = EL a is` by metis_tac[MEM_EL] >>
  `a = j` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
  qpat_x_assum `_ IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` mp_tac >>
  `q = EL j is` by metis_tac[] >>
  qpat_x_assum `q.inst_opcode = _` mp_tac >>
  Cases_on `mode` >> simp[mode_load_opcode_def]
QED

Theorem mm_local_canonical_pending_copy_owner:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  n <= LENGTH is /\ MEM j (mm_local_pending_indices is gs n) ==>
  ?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids
Proof
  strip_tac >>
  qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `j < LENGTH is` by decide_tac >>
  `MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed` by metis_tac[] >>
  drule_all (REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `mode`] mm_local_final_write_birth)) >> strip_tac
  >- (drule_all (REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `mode`] mm_local_indexed_bulk_owner)) >> metis_tac[]) >>
  drule_all (REWRITE_RULE [] (Q.INST [`s0` |->
    `FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE j is)`]
    (SPEC_ALL mm_local_indexed_store_owner))) >> metis_tac[]
QED

Theorem mm_local_canonical_pending_capture_owner:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is /\ MEM j (mm_local_pending_indices is gs n) /\
  mm_local_write_capture is H N j = SOME (d,bs) ==>
  ?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length
Proof
  strip_tac >>
  qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `j < LENGTH is` by decide_tac >>
  `MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
  drule_all (REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >> strip_tac
  >- (drule_all (REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_bulk_owner)) >> strip_tac >>
      qexists `h` >>
      gvs[mm_local_write_capture_def, venomStateTheory.eval_operand_def,
          venomStateTheory.read_memory_def, AllCaseEqs()]) >>
  drule_all (REWRITE_RULE [] (Q.INST [`s0` |->
    `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is)`]
    (SPEC_ALL (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_store_owner)))) >> strip_tac >>
  qexists `h` >>
  gvs[mm_local_write_capture_def, venomStateTheory.eval_operand_def,
      AllCaseEqs()]
QED

Theorem mm_local_canonical_pending_owner[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is /\ n <= N /\ mm_local_history is H N /\
  MEM j (mm_local_pending_indices is gs n) ==>
  ?h d bs. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    mm_local_write_capture is H N j = SOME (d,bs) /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length
Proof
  strip_tac >>
  qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `j < LENGTH is` by decide_tac >>
  `MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
  drule_all (REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >> strip_tac
  >- (drule_all mm_local_indexed_bulk_history_owner >> simp[]) >>
  drule_all (REWRITE_RULE [] (Q.INST [`s0` |->
    `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is)`]
    (SPEC_ALL mm_local_indexed_store_history_owner))) >>
  strip_tac >> qexistsl [`h`, `d`, `bs`] >> simp[]
QED

Theorem mm_local_canonical_pending_log[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is /\ n <= N /\ mm_local_history is H N ==>
  LIST_REL (\j w. mm_local_write_capture is H N j = SOME w)
    (mm_local_pending_indices is gs n)
    (MAP (THE o mm_local_write_capture is H N) (mm_local_pending_indices is gs n))
Proof
  strip_tac >> simp[LIST_REL_MAP2] >> irule EVERY2_refl >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM x (mm_local_pending_indices is gs n)` by metis_tac[] >>
  drule_all mm_local_canonical_pending_owner >> strip_tac >> gvs[]
QED

Theorem mm_local_canonical_pending_replay[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is /\ n <= N /\ mm_local_history is H N ==>
  (mm_local_pending (mm_local_write_capture is H N) (mm_local_pending_indices is gs n) s t <=>
   s.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) t
      (MAP (THE o mm_local_write_capture is H N) (mm_local_pending_indices is gs n))).vs_memory)
Proof
  strip_tac >> drule_all mm_local_canonical_pending_log >> strip_tac >>
  eq_tac >- metis_tac[mm_local_pending_log] >>
  strip_tac >> simp[mm_local_pending_def] >> metis_tac[]
QED

Theorem mm_local_write_rep_unique:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  j < LENGTH is /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM a gs /\ MEM b gs /\ MEM (EL j is).inst_id a.cg_inst_ids /\
  MEM (EL j is).inst_id b.cg_inst_ids /\ r < LENGTH is /\ q < LENGTH is /\
  rep_of_group is a = SOME ((EL r is).inst_id,a) /\
  rep_of_group is b = SOME ((EL q is).inst_id,b) ==> r = q
Proof
  strip_tac >>
  `a = b` by
    (irule mm_local_prefix_write_group_owner >>
     qexistsl [`bb`, `fn0`, `index`, `k`, `mode`, `sk`, `supply`, `EL j is`] >>
     gvs[] >> metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `((EL r is).inst_id = (EL q is).inst_id)` by gvs[] >>
  metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]
QED

Definition mm_local_rep_index_def:
  mm_local_rep_index is gs j = @r. r < LENGTH is /\
    ?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      rep_of_group is g = SOME ((EL r is).inst_id,g)
End

Theorem mm_local_rep_index_eq:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  j < LENGTH is /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\ r < LENGTH is /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  mm_local_rep_index is gs j = r
Proof
  strip_tac >> simp[mm_local_rep_index_def] >> SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  qpat_x_assum `is = _` SUBST_ALL_TAC >>
  qpat_x_assum `gs = _` SUBST_ALL_TAC >>
  metis_tac[mm_local_write_rep_unique]
QED

Theorem mm_local_canonical_pending_owned[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is /\ n <= N /\ mm_local_history is H N ==>
  mm_local_owned (mm_local_write_capture is H N) (mm_local_rep_index is gs) n
    (mm_local_pending_indices is gs n)
Proof
  strip_tac >> simp[mm_local_owned_def, mm_local_pending_indices_order, EVERY_MEM] >>
  qx_gen_tac `j` >> strip_tac >>
  `MEM j (mm_local_pending_indices is gs n)` by metis_tac[] >>
  drule_all mm_local_canonical_pending_owner >> strip_tac >>
  qpat_x_assum `MEM j (mm_local_pending_indices is gs n)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `j < LENGTH is` by decide_tac >>
  drule_all mm_local_rep_index_eq >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem mm_local_canonical_pending_keep:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is ==>
  FILTER (\j. SUC n <= mm_local_rep_index is gs j) (mm_local_pending_indices is gs n) =
  FILTER (\j. j < n) (mm_local_pending_indices is gs (SUC n))
Proof
  strip_tac >>
  simp[NoAsms, mm_local_pending_indices_def, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, FILTER_APPEND, FILTER_FILTER, COND_RAND] >>
  rewrite_tac[rich_listTheory.FILTER_EQ] >>
  qx_gen_tac `j` >> simp[MEM_COUNT_LIST] >> strip_tac >>
  eq_tac >> strip_tac >>
  `j < LENGTH is` by decide_tac >>
  `mm_local_rep_index is gs j = r` by
    (qpat_x_assum `is = _` SUBST_ALL_TAC >>
     qpat_x_assum `gs = _` SUBST_ALL_TAC >>
     metis_tac[mm_local_rep_index_eq, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_SUC_REFL, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem mm_local_canonical_pending_partition[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is /\ n <= N /\ mm_local_history is H N ==>
  FILTER (\j. mm_local_rep_index is gs j <> n) (mm_local_pending_indices is gs n) =
  FILTER (\j. j < n) (mm_local_pending_indices is gs (SUC n))
Proof
  strip_tac >>
  drule_all mm_local_canonical_pending_owned >>
  rewrite_tac[mm_local_owned_def, EVERY_MEM] >> strip_tac >>
  drule_all mm_local_canonical_pending_keep >>
  disch_then (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[rich_listTheory.FILTER_EQ] >> rpt strip_tac >>
  `n <= mm_local_rep_index is gs x` by metis_tac[] >> BETA_TAC >> decide_tac
QED

Theorem mm_local_canonical_pending_append[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\
  EVERY (\j. SUC n <= mm_local_rep_index is gs j) (mm_local_pending_indices is gs n) /\
  (EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n < r /\ r < LENGTH is ==>
  mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]
Proof
  strip_tac >>
  `n <= LENGTH is` by decide_tac >>
  drule_all mm_local_canonical_pending_keep >>
  `FILTER (\j. SUC n <= mm_local_rep_index is gs j) (mm_local_pending_indices is gs n) =
   mm_local_pending_indices is gs n` by metis_tac[FILTER_EQ_ID] >>
  strip_tac >>
  `MEM n (mm_local_pending_indices is gs (SUC n))` by
    (rewrite_tac[mm_local_pending_indices_mem] >>
     `SUC n <= r` by decide_tac >>
     conj_tac >- decide_tac >> conj_tac >- asm_rewrite_tac[] >>
     qexistsl [`g`, `r`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `MEM n _` mp_tac >>
  qpat_x_assum `_ = FILTER (\j. j < n) _` mp_tac >>
  pure_rewrite_tac[mm_local_pending_indices_def, rich_listTheory.COUNT_LIST_SNOC,
    rich_listTheory.SNOC_APPEND, FILTER_APPEND] >>
  qmatch_goalsub_abbrev_tac `FILTER P (COUNT_LIST n)` >>
  qmatch_goalsub_abbrev_tac `FILTER (\j. j < n) (FILTER Q (COUNT_LIST n))` >>
  `FILTER (\j. j < n) (FILTER Q (COUNT_LIST n)) = FILTER Q (COUNT_LIST n)` by
    (rewrite_tac[FILTER_EQ_ID, EVERY_MEM, MEM_FILTER, MEM_COUNT_LIST] >> simp[]) >>
  simp[NoAsms, FILTER_APPEND, COND_RAND, MEM_FILTER, MEM_COUNT_LIST] >>
  simp[] >>
  qpat_x_assum `FILTER _ (mm_local_pending_indices is gs n) = _` mp_tac >>
  pure_rewrite_tac[mm_local_pending_indices_def] >>
  qunabbrev_tac `P` >>
  qpat_x_assum `is = _` SUBST_ALL_TAC >>
  qpat_x_assum `gs = _` SUBST_ALL_TAC >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Theorem mm_local_canonical_bulk_runtime_read[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ mm_local_history is H (SUC n) /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (EL n is).inst_opcode = MCOPY /\
  (EL n is).inst_operands = [Lit dst; Lit src; Lit len] /\
  mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs n) (H n) t ==>
  read_memory (w2n src) (w2n len) (H n) = read_memory (w2n src) (w2n len) t
Proof
  strip_tac >>
  qabbrev_tac `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE n is)` >>
  qabbrev_tac `c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
    cg_inst_ids := [(EL n is).inst_id] |>` >>
  qabbrev_tac `hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c` >>
  `n <= LENGTH is /\ n <= SUC n` by decide_tac >>
  `!j. MEM j (mm_local_pending_indices is gs n) ==> j < n /\ ?h g r d bs.
    mm_local_write_capture is H (SUC n) j = SOME (d,bs) /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n <= r /\ r < LENGTH is /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length` by
    (rpt strip_tac >>
     `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE n is)` by simp[Abbr `ss`] >>
     drule_all mm_local_canonical_pending_owner >> strip_tac >>
     qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
       (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
     qexistsl [`h`, `g`, `r`, `d`, `bs`] >> metis_tac[]) >>
  `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
     empty_scan_state (TAKE n is)` by simp[Abbr `ss`] >>
  `c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
     cg_inst_ids := [(EL n is).inst_id] |>` by simp[Abbr `c`] >>
  `hs = flush_hazards Mem2Mem
     (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c` by simp[Abbr `hs`] >>
  drule_all mm_local_indexed_bulk_pending_birth >> simp[]
QED

Theorem mm_local_canonical_bulk_runtime_capture[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ mm_local_history is H (SUC n) /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (EL n is).inst_opcode = MCOPY /\
  (EL n is).inst_operands = [Lit dst; Lit src; Lit len] /\
  mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs n) (H n) t ==>
  mm_local_write_capture is H (SUC n) n =
    SOME (w2n dst,read_memory (w2n src) (w2n len) t)
Proof
  strip_tac >>
  drule_all mm_local_canonical_bulk_runtime_read >> strip_tac >>
  `n < SUC n` by decide_tac >>
  drule_all mm_local_write_capture_copy >> simp[]
QED

Theorem mm_local_canonical_bulk_defer[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ mm_local_history is H (SUC n) /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  EVERY (\j. SUC n <= mm_local_rep_index is gs j) (mm_local_pending_indices is gs n) /\
  MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n < r /\ r < LENGTH is /\
  (EL n is).inst_opcode = MCOPY /\
  (EL n is).inst_operands = [Lit dst; Lit src; Lit len] /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL n is).inst_id] |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c /\
  mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs n) (H n) t ==>
  read_memory (w2n src) (w2n len) (H n) = read_memory (w2n src) (w2n len) t /\
  mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs (SUC n)) (H (SUC n)) t
Proof
  strip_tac >>
  `n <= LENGTH is /\ n <= SUC n` by decide_tac >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]` by
    (irule mm_local_canonical_pending_append >> simp[] >> metis_tac[]) >>
  `!j. MEM j (mm_local_pending_indices is gs n) ==> j < n /\ ?h g r d bs.
    mm_local_write_capture is H (SUC n) j = SOME (d,bs) /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n <= r /\ r < LENGTH is /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length` by
    (rpt strip_tac >> drule_all mm_local_canonical_pending_owner >> strip_tac >>
     qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
       (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
     qexistsl [`h`, `g'`, `r'`, `d`, `bs`] >> gvs[]) >>
  drule_all mm_local_indexed_bulk_pending_birth >> simp[]
QED

Theorem mm_local_canonical_store_defer_post_phis[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ mm_local_history is H (SUC n) /\ n < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  EVERY (\j. SUC n <= mm_local_rep_index is gs j) (mm_local_pending_indices is gs n) /\
  MEM g gs /\ MEM (EL n is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n < r /\ r < LENGTH is /\
  (EL n is).inst_opcode = MSTORE /\ (EL n is).inst_operands = [Lit dst; Var v] /\
  h = phi_prefix_length bb.bb_instructions /\ h <= n /\
  LENGTH states = SUC (n-h) /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  EL 0 states = s_phi with vs_inst_idx := h /\
  (!r. r < n-h ==>
    ~is_terminator (EL (h+r) bb.bb_instructions).inst_opcode /\
    ?t. step_inst fuel ctx (EL (h+r) bb.bb_instructions) (EL r states) = OK t /\
        EL (SUC r) states = t with vs_inst_idx := SUC (EL r states).vs_inst_idx) /\
  H n = EL (n-h) states /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  FLOOKUP ss.ss_loads v = SOME src /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL n is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id]) |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) 32)) c /\
  mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs n) (H n) t ==>
  read_memory src 32 (H n) = read_memory src 32 t /\
  mm_local_pending (mm_local_write_capture is H (SUC n))
    (mm_local_pending_indices is gs (SUC n)) (H (SUC n)) t
Proof
  strip_tac >>
  `n <= LENGTH is /\ n <= SUC n` by decide_tac >>
  `mm_local_pending_indices is gs (SUC n) = mm_local_pending_indices is gs n ++ [n]` by
    (irule mm_local_canonical_pending_append >> simp[] >> metis_tac[]) >>
  `!j. MEM j (mm_local_pending_indices is gs n) ==> j < n /\ ?h g r d bs.
    mm_local_write_capture is H (SUC n) j = SOME (d,bs) /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n <= r /\ r < LENGTH is /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length` by
    (rpt strip_tac >> drule_all mm_local_canonical_pending_owner >> strip_tac >>
     qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)`
       (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
     metis_tac[]) >>
  drule_all mm_local_indexed_store_pending_post_phis >> simp[]
QED

Theorem mm_local_canonical_rep_write:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  n < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL n is).inst_id,g) ==>
  (EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (EL n is).inst_id = SOME g` by
    (qpat_x_assum `is = _` SUBST_ALL_TAC >>
     qpat_x_assum `gs = _` SUBST_ALL_TAC >>
     drule_all mm_local_prefix_selected_rep >> simp[]) >>
  drule_all mm_local_prefix_rep_write >> simp[]
QED

Theorem mm_local_canonical_due_group:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  n < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL n is).inst_id,g) /\
  js = mm_local_pending_indices is gs n /\
  due = FILTER (\j. mm_local_rep_index is gs j = n) js ==>
  due = FILTER (\j. j < n /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM (EL j is).inst_id g.cg_inst_ids) (COUNT_LIST n)
Proof
  strip_tac >> drule_all mm_local_canonical_rep_write >> strip_tac >>
  `MEM (EL n is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  qpat_x_assum `due = _` SUBST_ALL_TAC >>
  qpat_x_assum `js = _` SUBST_ALL_TAC >>
  simp[NoAsms, mm_local_pending_indices_def, FILTER_FILTER] >>
  rewrite_tac[rich_listTheory.FILTER_EQ] >>
  qx_gen_tac `j` >> simp[NoAsms, MEM_COUNT_LIST] >> strip_tac >>
  eq_tac
  >- (strip_tac >> `j < LENGTH is` by decide_tac >>
      `mm_local_rep_index is gs j = r` by
        (qpat_x_assum `is = _` SUBST_ALL_TAC >>
         qpat_x_assum `gs = _` SUBST_ALL_TAC >>
         irule mm_local_rep_index_eq >>
         metis_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
      `r = n` by metis_tac[] >>
      `MEM (EL n is).inst_id g'.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
      `g' = g` by
        (irule mm_local_prefix_write_group_owner >>
         qexistsl [`bb`, `fn0`, `index`, `k`, `mode`, `sk`, `supply`, `EL n is`] >>
         gvs[] >> metis_tac[EL_MEM]) >> gvs[]) >>
  strip_tac >> `j < LENGTH is` by decide_tac >>
  `mm_local_rep_index is gs j = n` by
    (irule mm_local_rep_index_eq >> metis_tac[pred_setTheory.IN_INSERT]) >>
  simp[] >> qexistsl [`g`, `n`] >> gvs[]
QED

Theorem mm_local_canonical_rep_rest[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ mm_local_history is H (SUC n) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL n is).inst_id,g) /\
  js = mm_local_pending_indices is gs n /\
  rest = FILTER (\j. mm_local_rep_index is gs j <> n) js ==>
  rest = mm_local_pending_indices is gs (SUC n)
Proof
  strip_tac >>
  `n <= LENGTH is /\ n <= SUC n` by decide_tac >>
  drule_all mm_local_canonical_rep_write >> strip_tac >>
  `MEM (EL n is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `~MEM n (mm_local_pending_indices is gs (SUC n))` by
    (strip_tac >>
     qpat_x_assum `MEM n (mm_local_pending_indices _ _ _)`
       (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
     `r = n` by (irule mm_local_write_rep_unique >> metis_tac[]) >> decide_tac) >>
  `FILTER (\j. j < n) (mm_local_pending_indices is gs (SUC n)) =
    mm_local_pending_indices is gs (SUC n)` by
    (rewrite_tac[FILTER_EQ_ID, EVERY_MEM] >> qx_gen_tac `j` >> strip_tac >>
     drule (iffLR mm_local_pending_indices_mem) >> strip_tac >>
     `j <> n` by metis_tac[] >> simp[] >> decide_tac) >>
  drule_all mm_local_canonical_pending_partition >> simp[] >> metis_tac[]
QED

Theorem mm_local_canonical_rep_capture:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ mm_local_history is H (SUC n) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL n is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC n) ==>
  ?d bs. cap n = SOME (d,bs) /\
    (H (SUC n)).vs_memory = (write_memory_with_expansion d bs (H n)).vs_memory
Proof
  strip_tac >> drule_all mm_local_canonical_rep_write >> strip_tac >>
  `MEM (EL n is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
  `n < SUC n` by simp[] >>
  drule_all (REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >> strip_tac
  >- (drule_all mm_local_write_capture_copy >> strip_tac >>
      drule_all mm_local_write_capture_sound >> strip_tac >>
      qexistsl [`w2n dst`, `read_memory (w2n src) (w2n len) (H n)`] >> gvs[]) >>
  drule_all mm_local_history_store_value >> strip_tac >>
  drule_all mm_local_write_capture_store >> strip_tac >>
  drule_all mm_local_write_capture_sound >> strip_tac >>
  qexistsl [`w2n dst`, `word_to_bytes value T`] >> gvs[]
QED

Theorem mm_local_canonical_due_records[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ mm_local_history is H (SUC n) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL n is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC n) /\
  js = mm_local_pending_indices is gs n /\
  due = FILTER (\j. mm_local_rep_index is gs j = n) js ==>
  LIST_REL (\j w. cap j = SOME w) (due ++ [n])
    (MAP (THE o cap) (due ++ [n]))
Proof
  strip_tac >>
  `n <= LENGTH is /\ n <= SUC n` by decide_tac >>
  drule_all mm_local_canonical_rep_capture >> strip_tac >>
  simp[LIST_REL_MAP2] >> irule EVERY2_refl >>
  simp[EVERY_MEM] >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = n` >- gvs[] >>
  `MEM j (mm_local_pending_indices is gs n)` by
    (gvs[MEM_APPEND, MEM_FILTER]) >>
  drule_all mm_local_canonical_pending_owner >> strip_tac >> gvs[]
QED

Theorem mm_local_canonical_rest_records[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ mm_local_history is H (SUC n) /\
  cap = mm_local_write_capture is H (SUC n) /\
  js = mm_local_pending_indices is gs n /\
  rest = FILTER (\j. mm_local_rep_index is gs j <> n) js ==>
  LIST_REL (\j w. cap j = SOME w) rest (MAP (THE o cap) rest)
Proof
  strip_tac >>
  `n <= LENGTH is /\ n <= SUC n` by decide_tac >>
  drule_all mm_local_canonical_pending_log >> strip_tac >>
  simp[LIST_REL_MAP2] >> irule EVERY2_refl >>
  simp[EVERY_MEM] >> qx_gen_tac `j` >> strip_tac >>
  `MEM j (mm_local_pending_indices is gs n)` by gvs[MEM_FILTER] >>
  drule_all LIST_REL_MEM_IMP >> strip_tac >> gvs[]
QED

Theorem mm_local_hazards_destination_alternative[local]:
  MEM h (flush_hazards mode ss c).ss_copies ==>
  ~copy_overwrites c (copy_dst_interval h) \/
  copy_can_merge h c \/ copy_can_merge c h
Proof
  simp[flush_hazards_def] >> rpt IF_CASES_TAC >>
  gvs[flush_copies_def, MEM_FILTER, waw_hazards_def, FILTER_EQ_NIL, EVERY_MEM] >>
  metis_tac[]
QED

(* Temporary actual-scanner interface probe; remove at delivery. *)
Theorem mm_local_empty_blocker_probe[local]:
  !dfg.
  (FOLDL (scan_inst dfg Mem2Mem) empty_scan_state
    [mk_inst 1 MCOPY [Lit 0w; Lit 1000w; Lit 100w] [];
     mk_inst 2 MCOPY [Lit 50w; Lit 3000w; Lit 0w] [];
     mk_inst 3 MCOPY [Lit 90w; Lit 1090w; Lit 10w] []]).ss_copies =
    [<|cg_dst := 0; cg_src := 1000; cg_length := 100; cg_inst_ids := [1]|>;
     <|cg_dst := 50; cg_src := 3000; cg_length := 0; cg_inst_ids := [2]|>;
     <|cg_dst := 90; cg_src := 1090; cg_length := 10; cg_inst_ids := [3]|>] /\
  (FOLDL (\ss i. scan_bulk_copy Mem2Mem ss i) empty_scan_state
    [mk_inst 1 MCOPY [Lit 0w; Lit 1000w; Lit 100w] [];
     mk_inst 2 MCOPY [Lit 50w; Lit 3000w; Lit 0w] [];
     mk_inst 3 MCOPY [Lit 90w; Lit 1090w; Lit 10w] []]).ss_copies =
    [<|cg_dst := 0; cg_src := 1000; cg_length := 100; cg_inst_ids := [1]|>;
     <|cg_dst := 50; cg_src := 3000; cg_length := 0; cg_inst_ids := [2]|>;
     <|cg_dst := 90; cg_src := 1090; cg_length := 10; cg_inst_ids := [3]|>] /\
  copy_overwrites
    <|cg_dst := 90; cg_src := 1090; cg_length := 10; cg_inst_ids := [3]|>
    (copy_dst_interval
      <|cg_dst := 0; cg_src := 1000; cg_length := 100; cg_inst_ids := [1]|>) /\
  copy_can_merge
    <|cg_dst := 0; cg_src := 1000; cg_length := 100; cg_inst_ids := [1]|>
    <|cg_dst := 90; cg_src := 1090; cg_length := 10; cg_inst_ids := [3]|>
Proof
  gen_tac >> EVAL_TAC
QED

Theorem mm_local_two_copy_read[local]:
  mm_local_history is H (n+2) /\
  (EL n is).inst_opcode = MCOPY /\
  (EL n is).inst_operands = [Lit dst; Lit src; Lit len] /\
  c1 = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
          cg_inst_ids := [(EL n is).inst_id] |> /\
  ss = FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE (SUC n) is) /\
  MEM c1 ss.ss_copies /\
  hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval c2.cg_dst c2.cg_length)) c2 /\
  MEM c1 hs.ss_copies ==>
  read_memory c2.cg_src c2.cg_length (H (SUC n)) =
  read_memory c2.cg_src c2.cg_length (H n)
Proof
  strip_tac >>
  `mm_local_write_capture is H (n+2) n =
     SOME (w2n dst,read_memory (w2n src) (w2n len) (H n)) /\
   LENGTH (read_memory (w2n src) (w2n len) (H n)) = w2n len` by
    (irule mm_local_write_capture_copy >> simp[]) >>
  `~copy_overwrites c1 (copy_src_interval c2)` by
    metis_tac[mm_local_hazards_source_exclusion] >>
  drule_all mm_local_write_capture_sound >> strip_tac >>
  `read_memory c2.cg_src c2.cg_length (H (SUC n)) =
   read_memory c2.cg_src c2.cg_length
     (write_memory_with_expansion (w2n dst) (read_memory (w2n src) (w2n len) (H n)) (H n))` by
    simp[venomStateTheory.read_memory_def] >>
  pop_assum SUBST1_TAC >>
  irule venomWriteReplayPropsTheory.read_write_disjoint >>
  drule (INST_TYPE [alpha |-> ``:word8``] mm_local_capture_source_exclusion) >>
  disch_then (qspecl_then [`w2n dst`, `read_memory (w2n src) (w2n len) (H n)`] mp_tac) >>
  gvs[] >> simp[venomStateTheory.read_memory_def] >> metis_tac[]
QED

Theorem mm_local_two_copy_captures[local]:
  mm_local_history is H (n+2) /\
  (EL n is).inst_opcode = MCOPY /\
  (EL n is).inst_operands = [Lit dst1; Lit src1; Lit len1] /\
  (EL (SUC n) is).inst_opcode = MCOPY /\
  (EL (SUC n) is).inst_operands = [Lit dst2; Lit src2; Lit len2] /\
  c1 = <| cg_dst := w2n dst1; cg_src := w2n src1; cg_length := w2n len1;
          cg_inst_ids := [(EL n is).inst_id] |> /\
  c2 = <| cg_dst := w2n dst2; cg_src := w2n src2; cg_length := w2n len2;
          cg_inst_ids := [(EL (SUC n) is).inst_id] |> /\
  ss = FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE (SUC n) is) /\
  MEM c1 ss.ss_copies /\
  hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval c2.cg_dst c2.cg_length)) c2 /\
  MEM c1 hs.ss_copies ==>
  mm_local_write_capture is H (n+2) n =
    SOME (c1.cg_dst,read_memory c1.cg_src c1.cg_length (H n)) /\
  mm_local_write_capture is H (n+2) (SUC n) =
    SOME (c2.cg_dst,read_memory c2.cg_src c2.cg_length (H n))
Proof
  strip_tac >>
  `read_memory c2.cg_src c2.cg_length (H (SUC n)) =
   read_memory c2.cg_src c2.cg_length (H n)` by
    (drule_all mm_local_two_copy_read >> simp[]) >>
  `mm_local_write_capture is H (n+2) n =
     SOME (w2n dst1,read_memory (w2n src1) (w2n len1) (H n)) /\
   LENGTH (read_memory (w2n src1) (w2n len1) (H n)) = w2n len1` by
    (irule mm_local_write_capture_copy >> simp[]) >>
  `mm_local_write_capture is H (n+2) (SUC n) =
     SOME (w2n dst2,read_memory (w2n src2) (w2n len2) (H (SUC n))) /\
   LENGTH (read_memory (w2n src2) (w2n len2) (H (SUC n))) = w2n len2` by
    (irule mm_local_write_capture_copy >> simp[]) >>
  gvs[]
QED

Theorem mm_local_copy_birth_log[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 /\
  ~copy_overwrites c1 (copy_src_interval c2) /\
  EVERY (\(d,bs).
    (c2.cg_src + c2.cg_length <= d \/ d + LENGTH bs <= c2.cg_src) /\
    (c1.cg_dst + c1.cg_length <= d \/ d + LENGTH bs <= c1.cg_dst)) ws ==>
  mcopy c2.cg_dst c2.cg_src c2.cg_length
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (mcopy c1.cg_dst c1.cg_src c1.cg_length s) ws) =
  write_memory_with_expansion (copy_merge c1 c2).cg_dst
    (read_memory (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length s)
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws)
Proof
  strip_tac >>
  `read_memory c2.cg_src c2.cg_length
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (mcopy c1.cg_dst c1.cg_src c1.cg_length s) ws) =
   read_memory c2.cg_src c2.cg_length s` by
    (irule EQ_TRANS >>
     irule_at Any venomWriteReplayPropsTheory.read_write_log >>
     conj_tac >- (gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
     simp[venomExecSemanticsTheory.mcopy_def, GSYM venomStateTheory.read_memory_def] >>
     irule venomWriteReplayPropsTheory.read_write_disjoint >>
     gvs[copy_overwrites_def, copy_src_interval_def, copy_dst_interval_def,
         mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
         mmIntervalTheory.interval_end_def, mm_local_read_memory_bytes, mm_local_bytes_length,
         arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
     simp[mm_local_bytes_def] >> decide_tac) >>
  simp[venomExecSemanticsTheory.mcopy_def, GSYM venomStateTheory.read_memory_def] >>
  `EVERY (\(d,bs). d + LENGTH bs <= c1.cg_dst \/
    c1.cg_dst + LENGTH (read_memory c1.cg_src c1.cg_length s) <= d) ws` by
    (gvs[EVERY_MEM, pairTheory.FORALL_PROD, mm_local_read_memory_bytes, mm_local_bytes_length] >> metis_tac[]) >>
  drule venomWriteReplayPropsTheory.write_log_commute >>
  disch_then (qspec_then `s` (fn th => once_rewrite_tac[GSYM th])) >>
  simpLib.SIMP_TAC (srw_ss()) [mm_local_read_memory_bytes] >>
  irule mm_local_bytes_write_merge >> simp[]
QED

Theorem mm_local_copy_compatible_birth[local]:
  (if c1.cg_dst <= c2.cg_dst then copy_can_merge c1 c2
   else copy_can_merge c2 c1) /\
  ~copy_overwrites c1 (copy_src_interval c2) /\
  p1 = read_memory c1.cg_src c1.cg_length s /\
  EVERY (\(d,bs).
    (c2.cg_src + c2.cg_length <= d \/ d + LENGTH bs <= c2.cg_src) /\
    mm_local_write_compatible c1.cg_dst p1 d bs) ws /\
  g = (if c1.cg_dst <= c2.cg_dst then copy_merge c1 c2 else copy_merge c2 c1) ==>
  mcopy c2.cg_dst c2.cg_src c2.cg_length
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (mcopy c1.cg_dst c1.cg_src c1.cg_length s) ws) =
  write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length s)
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws)
Proof
  strip_tac >>
  `read_memory c2.cg_src c2.cg_length
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (mcopy c1.cg_dst c1.cg_src c1.cg_length s) ws) =
   read_memory c2.cg_src c2.cg_length s` by
    (irule EQ_TRANS >> irule_at Any venomWriteReplayPropsTheory.read_write_log >>
     conj_tac >- (gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
     simp[venomExecSemanticsTheory.mcopy_def, GSYM venomStateTheory.read_memory_def] >>
     irule venomWriteReplayPropsTheory.read_write_disjoint >>
     gvs[copy_overwrites_def, copy_src_interval_def, copy_dst_interval_def,
         mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
         mmIntervalTheory.interval_end_def, mm_local_read_memory_bytes,
         mm_local_bytes_length, arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
     simp[mm_local_bytes_def] >> decide_tac) >>
  simp[venomExecSemanticsTheory.mcopy_def, GSYM venomStateTheory.read_memory_def] >>
  `EVERY (\(d,bs). mm_local_write_compatible d bs c1.cg_dst
    (read_memory c1.cg_src c1.cg_length s)) ws` by
    (fs[EVERY_MEM, pairTheory.FORALL_PROD] >>
     metis_tac[mm_local_write_compatible_sym]) >>
  drule mm_local_write_log_compatible_commute >>
  disch_then (qspec_then `s` (fn th => once_rewrite_tac[GSYM th])) >>
  Cases_on `c1.cg_dst <= c2.cg_dst`
  >- (gvs[] >> simpLib.SIMP_TAC (srw_ss()) [mm_local_read_memory_bytes] >>
      irule mm_local_bytes_write_merge >> simp[]) >>
  gvs[] >> simpLib.SIMP_TAC (srw_ss()) [mm_local_read_memory_bytes] >>
  irule mm_local_bytes_write_merge_reverse >> simp[]
QED

Theorem mm_local_two_copy_merge[local]:
  mm_local_history is H (n+2) /\
  (EL n is).inst_opcode = MCOPY /\
  (EL n is).inst_operands = [Lit dst1; Lit src1; Lit len1] /\
  (EL (SUC n) is).inst_opcode = MCOPY /\
  (EL (SUC n) is).inst_operands = [Lit dst2; Lit src2; Lit len2] /\
  c1 = <| cg_dst := w2n dst1; cg_src := w2n src1; cg_length := w2n len1;
          cg_inst_ids := [(EL n is).inst_id] |> /\
  c2 = <| cg_dst := w2n dst2; cg_src := w2n src2; cg_length := w2n len2;
          cg_inst_ids := [(EL (SUC n) is).inst_id] |> /\
  ss = FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE (SUC n) is) /\
  MEM c1 ss.ss_copies /\
  hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval c2.cg_dst c2.cg_length)) c2 /\
  MEM c1 hs.ss_copies /\ c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  (H (n+2)).vs_memory =
    (write_memory_with_expansion (copy_merge c1 c2).cg_dst
      (read_memory (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length (H n)) (H n)).vs_memory
Proof
  strip_tac >> drule_all mm_local_two_copy_captures >> strip_tac >>
  `n+2 = SUC (SUC n)` by decide_tac >>
  ` (H (SUC n)).vs_memory =
    (write_memory_with_expansion c1.cg_dst
      (read_memory c1.cg_src c1.cg_length (H n)) (H n)).vs_memory` by
    (irule mm_local_write_capture_sound >> goal_assum (drule_at Any) >> simp[]) >>
  ` (H (n+2)).vs_memory =
    (write_memory_with_expansion c2.cg_dst
      (read_memory c2.cg_src c2.cg_length (H n)) (H (SUC n))).vs_memory` by
    (simp[] >> irule mm_local_write_capture_sound >> goal_assum (drule_at Any) >> simp[]) >>
  `write_memory_with_expansion c2.cg_dst (read_memory c2.cg_src c2.cg_length (H n))
     (write_memory_with_expansion c1.cg_dst (read_memory c1.cg_src c1.cg_length (H n)) (H n)) =
   write_memory_with_expansion (copy_merge c1 c2).cg_dst
     (read_memory (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length (H n)) (H n)` by
    (simpLib.SIMP_TAC (srw_ss()) [mm_local_read_memory_bytes] >>
     irule mm_local_bytes_write_merge >> simp[]) >>
  gvs[write_as_replace, venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_hazards_removed[local]:
  ?tail. (flush_hazards Mem2Mem ss c).ss_flushed = ss.ss_flushed ++ tail /\
    (!g. MEM g tail ==> MEM g ss.ss_copies /\
      ~MEM g (flush_hazards Mem2Mem ss c).ss_copies)
Proof
  simp[flush_hazards_def, mode_allows_overlap_def] >>
  rpt IF_CASES_TAC >>
  gvs[flush_copies_def, waw_hazards_def, raw_hazards_def, war_hazards_def,
      copies_that_overwrite_def, APPEND_ASSOC] >>
  simp[MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_hazards_historical_captures[local]:
  hs = flush_hazards Mem2Mem (invalidate_loads ss iv) c /\ j < LENGTH is /\
  EVERY (mm_local_group_captures is cap B) ss.ss_copies /\
  (!g. MEM g ss.ss_copies ==> ~MEM (EL j is).inst_id g.cg_inst_ids) /\
  cap' = (\q. if q = j then SOME (d,bs) else cap q) ==>
  ?tail. hs.ss_flushed = ss.ss_flushed ++ tail /\
    EVERY (mm_local_group_captures is cap' B) tail /\
    (!g. MEM g tail ==> MEM g ss.ss_copies /\ ~MEM g hs.ss_copies)
Proof
  strip_tac >>
  qspecl_then [`invalidate_loads ss iv`, `c`] strip_assume_tac
    (GEN_ALL mm_local_hazards_removed) >>
  gvs[invalidate_loads_def] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  irule mm_local_group_captures_extend >> metis_tac[]
QED

Theorem mm_local_bulk_capture_survivors[local]:
  i.inst_opcode = MCOPY /\ i.inst_operands = [Lit dst; Lit src; Lit len] /\
  step_inst_base i s = OK t /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [i.inst_id] |> /\
  hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c ==>
  (!g. MEM g hs.ss_copies ==>
    read_memory g.cg_src g.cg_length t = read_memory g.cg_src g.cg_length s) /\
  (?tail. hs.ss_flushed = ss.ss_flushed ++ tail)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      metis_tac[mm_local_snapshot_copy_base]) >>
  gvs[] >>
  `ss.ss_flushed = (invalidate_loads ss (mk_interval (w2n dst) (w2n len))).ss_flushed`
    by simp[invalidate_loads_def] >>
  metis_tac[mm_local_hazards_flushed_extension]
QED

Theorem mm_local_store_capture_survivors[local]:
  i.inst_opcode = MSTORE /\ i.inst_operands = [Lit dst; Var v] /\
  lookup_var v s = SOME (mload src s) /\ step_inst_base i s = OK t /\
  c.cg_dst = w2n dst /\ c.cg_src = src /\ c.cg_length = 32 /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) 32)) c ==>
  (!g. MEM g hs.ss_copies ==>
    read_memory g.cg_src g.cg_length t = read_memory g.cg_src g.cg_length s) /\
  (?tail. hs.ss_flushed = ss.ss_flushed ++ tail)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[mm_local_snapshot_store_base]) >>
  gvs[] >>
  `ss.ss_flushed = (invalidate_loads ss (mk_interval (w2n dst) 32)).ss_flushed`
    by simp[invalidate_loads_def] >>
  metis_tac[mm_local_hazards_flushed_extension]
QED

Theorem mm_local_zero_store_capture_birth[local]:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  i = EL j is /\ i.inst_opcode = MSTORE /\
  i.inst_operands = [Lit dst; Lit 0w] /\ step_inst_base i s = OK t /\
  c = copy_memzero (w2n dst) 32 [i.inst_id] /\
  cap' = (\q. if q = j then SOME (w2n dst, REPLICATE 32 0w) else cap q) ==>
  scan_inst_memzero dfg mz i = mz with mz_copies := add_copy mz.mz_copies c /\
  t.vs_memory = (write_memory_with_expansion (w2n dst) (REPLICATE 32 0w) s).vs_memory /\
  cap' j = SOME (w2n dst, REPLICATE 32 0w) /\
  mm_local_group_captures is cap' (\a. 0w) c
Proof
  strip_tac >> conj_tac
  >- gvs[scan_inst_memzero_def, is_zero_store_def, operand_lit_val_def] >>
  conj_tac
  >- (gvs[venomExecSemanticsTheory.step_inst_base_def,
          venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operand_def] >>
      simp[mstore_0w_eq_write]) >>
  conj_tac >- simp[] >> irule mm_local_group_captures_birth >>
  simp[copy_memzero_def] >> qexists `j` >>
  gvs[copy_memzero_def, mm_local_bytes_def, REPLICATE_GENLIST, combinTheory.K_DEF]
QED

Theorem mm_local_zero_calldata_capture_birth[local]:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  i = EL j is /\ is_calldatasize_copy dfg i /\
  i.inst_operands = [Lit dst; Var v; Lit len] /\
  lookup_var v s = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  step_inst_base i s = OK t /\
  c = copy_memzero (w2n dst) (w2n len) [i.inst_id] /\
  cap' = (\q. if q = j then SOME (w2n dst, REPLICATE (w2n len) 0w) else cap q) ==>
  scan_inst_memzero dfg mz i = mz with mz_copies := add_copy mz.mz_copies c /\
  t.vs_memory = (write_memory_with_expansion (w2n dst) (REPLICATE (w2n len) 0w) s).vs_memory /\
  cap' j = SOME (w2n dst, REPLICATE (w2n len) 0w) /\
  mm_local_group_captures is cap' (\a. 0w) c
Proof
  strip_tac >>
  `i.inst_opcode = CALLDATACOPY` by fs[is_calldatasize_copy_def] >>
  conj_tac
  >- gvs[scan_inst_memzero_def, is_zero_store_def, operand_lit_val_def] >>
  conj_tac
  >- (gvs[venomExecSemanticsTheory.step_inst_base_def, venomStateTheory.eval_operand_def] >>
      simp[calldatacopy_past_end_bytes, TAKE_LENGTH_ID_rwt]) >>
  conj_tac >- simp[] >> irule mm_local_group_captures_birth >>
  simp[copy_memzero_def] >> qexists `j` >>
  gvs[copy_memzero_def, mm_local_bytes_def, REPLICATE_GENLIST, combinTheory.K_DEF]
QED

Definition mm_local_group_coverage_def:
  mm_local_group_coverage is n cap g <=>
    !a. (g.cg_dst <= a /\ a < g.cg_dst + g.cg_length) <=>
      ?j d bs. j < n /\ j < LENGTH is /\
        MEM (EL j is).inst_id g.cg_inst_ids /\ cap j = SOME (d,bs) /\
        d <= a /\ a < d + LENGTH bs
End

Theorem mm_local_group_coverage_birth[local]:
  j < n /\ j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  g.cg_inst_ids = [(EL j is).inst_id] /\
  cap j = SOME (g.cg_dst, bs) /\ LENGTH bs = g.cg_length ==>
  mm_local_group_coverage is n cap g
Proof
  simp[mm_local_group_coverage_def] >> strip_tac >> gen_tac >> eq_tac
  >- (strip_tac >> qexistsl [`j`, `g.cg_dst`, `bs`] >> simp[]) >>
  strip_tac >>
  `j' = j` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
  gvs[]
QED

Theorem mm_local_copy_merge_interval[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  (!a. ((copy_merge c1 c2).cg_dst <= a /\
        a < (copy_merge c1 c2).cg_dst + (copy_merge c1 c2).cg_length) <=>
    (c1.cg_dst <= a /\ a < c1.cg_dst + c1.cg_length) \/
    (c2.cg_dst <= a /\ a < c2.cg_dst + c2.cg_length))
Proof
  simp[copy_merge_def, copy_can_merge_def, arithmeticTheory.MAX_DEF] >>
  rpt strip_tac >> IF_CASES_TAC >> decide_tac
QED

Theorem mm_local_group_coverage_merge:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 /\
  mm_local_group_coverage is n cap c1 /\ mm_local_group_coverage is n cap c2 ==>
  mm_local_group_coverage is n cap (copy_merge c1 c2)
Proof
  strip_tac >> drule_all mm_local_copy_merge_interval >> strip_tac >>
  fs[mm_local_group_coverage_def] >> gen_tac >>
  first_x_assum (qspec_then `a` SUBST1_TAC) >>
  simp[copy_merge_def, MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_merge_adjacent_coverage[local]:
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
    EVERY (mm_local_group_coverage is n cap) cs ==>
    EVERY (mm_local_group_coverage is n cap) (merge_adjacent cs)
Proof
  recInduct merge_adjacent_ind >> simp[merge_adjacent_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2`
  >- (gvs[] >> first_x_assum irule >> conj_tac
      >- (gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
              copy_merge_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      simp[] >> irule mm_local_group_coverage_merge >>
      gvs[sortingTheory.SORTED_DEF]) >>
  gvs[] >> first_x_assum irule >> gvs[sortingTheory.SORTED_DEF]
QED

Theorem mm_local_add_copy_coverage[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
  EVERY (mm_local_group_coverage is n cap) cs /\
  mm_local_group_coverage is n cap c ==>
  EVERY (mm_local_group_coverage is n cap) (add_copy cs c)
Proof
  strip_tac >> simp[add_copy_def] >> irule mm_local_merge_adjacent_coverage >>
  metis_tac[mm_local_insert_sorted_order, mm_local_insert_every]
QED

Definition mm_local_zero_capture_def:
  mm_local_zero_capture dfg is n j =
    if j < n /\ j < LENGTH is then
      if is_zero_store (EL j is) then
        (case (EL j is).inst_operands of
          [Lit dst; Lit value] => SOME (w2n dst, REPLICATE 32 (0w:word8))
        | _ => NONE)
      else if is_calldatasize_copy dfg (EL j is) then
        (case (EL j is).inst_operands of
          [Lit dst; Var v; Lit len] => SOME (w2n dst, REPLICATE (w2n len) (0w:word8))
        | _ => NONE)
      else NONE
    else NONE
End

Theorem mm_local_zero_capture_store[local]:
  j < n /\ j < LENGTH is /\ (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Lit 0w] ==>
  mm_local_zero_capture dfg is n j = SOME (w2n dst, REPLICATE 32 0w)
Proof
  simp[mm_local_zero_capture_def, is_zero_store_def, operand_lit_val_def]
QED

Theorem mm_local_zero_capture_calldata[local]:
  j < n /\ j < LENGTH is /\ is_calldatasize_copy dfg (EL j is) /\
  (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
  mm_local_zero_capture dfg is n j = SOME (w2n dst, REPLICATE (w2n len) 0w)
Proof
  strip_tac >>
  `(EL j is).inst_opcode = CALLDATACOPY` by fs[is_calldatasize_copy_def] >>
  simp[mm_local_zero_capture_def, is_zero_store_def]
QED

Theorem mm_local_zero_capture_future[local]:
  n <= j ==> mm_local_zero_capture dfg is n j = NONE
Proof
  simp[mm_local_zero_capture_def]
QED

Theorem mm_local_zero_capture_past:
  j < n /\ n <= m ==>
  mm_local_zero_capture dfg is m j = mm_local_zero_capture dfg is n j
Proof
  simp[mm_local_zero_capture_def]
QED

Theorem mm_local_zero_capture_cases:
  mm_local_zero_capture dfg is n j = SOME (d,bs) ==>
  j < n /\ j < LENGTH is /\
  ((?dst. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Lit 0w] /\
      d = w2n dst /\ bs = REPLICATE 32 0w) \/
   (?dst v len. is_calldatasize_copy dfg (EL j is) /\
      (EL j is).inst_operands = [Lit dst; Var v; Lit len] /\
      d = w2n dst /\ bs = REPLICATE (w2n len) 0w))
Proof
  simp[mm_local_zero_capture_def] >>
  rpt IF_CASES_TAC >> gvs[AllCaseEqs(), is_zero_store_def, operand_lit_val_def] >>
  rpt strip_tac >> gvs[operand_lit_val_def]
QED

Theorem mm_local_zero_inst_certificate[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) mz.mz_copies /\
  EVERY P (mz.mz_flushed ++ mz.mz_copies) /\
  (!cs c. SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
    EVERY P cs /\ P c ==> EVERY P (add_copy cs c)) /\
  (!dst. is_zero_store i /\ i.inst_operands = [Lit dst; Lit 0w] ==>
    P (copy_memzero (w2n dst) 32 [i.inst_id])) /\
  (!dst v len. is_calldatasize_copy dfg i /\
    i.inst_operands = [Lit dst; Var v; Lit len] ==>
    P (copy_memzero (w2n dst) (w2n len) [i.inst_id])) ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (scan_inst_memzero dfg mz i).mz_copies /\
  EVERY P ((scan_inst_memzero dfg mz i).mz_flushed ++
    (scan_inst_memzero dfg mz i).mz_copies)
Proof
  strip_tac >> simp[scan_inst_memzero_def] >>
  Cases_on `is_zero_store i`
  >- (fs[is_zero_store_def] >>
      rpt (CASE_TAC >> gvs[operand_lit_val_def, memzero_barrier_def, EVERY_APPEND]) >>
      gvs[oneline operand_lit_val_def, AllCaseEqs()] >>
      metis_tac[mm_local_add_copy_order]) >>
  Cases_on `is_calldatasize_copy dfg i`
  >- (fs[is_calldatasize_copy_def] >>
      rpt (CASE_TAC >> gvs[operand_lit_val_def, memzero_barrier_def, EVERY_APPEND]) >>
      gvs[oneline operand_lit_val_def, oneline operand_var_def, AllCaseEqs()] >>
      rename1 `i.inst_operands = [Lit dst; src; Lit len]` >>
      Cases_on `src` >> gvs[] >> metis_tac[mm_local_add_copy_order]) >>
  gvs[] >> IF_CASES_TAC >>
  gvs[memzero_barrier_def, EVERY_APPEND]
QED

Theorem mm_local_zero_fold_certificate[local]:
  !xs mz. SORTED (\a b. a.cg_dst <= b.cg_dst) mz.mz_copies /\
  EVERY P (mz.mz_flushed ++ mz.mz_copies) /\
  (!cs c. SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
    EVERY P cs /\ P c ==> EVERY P (add_copy cs c)) /\
  EVERY (\i.
    (!dst. is_zero_store i /\ i.inst_operands = [Lit dst; Lit 0w] ==>
      P (copy_memzero (w2n dst) 32 [i.inst_id])) /\
    (!dst v len. is_calldatasize_copy dfg i /\
      i.inst_operands = [Lit dst; Var v; Lit len] ==>
      P (copy_memzero (w2n dst) (w2n len) [i.inst_id]))) xs ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst)
    (FOLDL (scan_inst_memzero dfg) mz xs).mz_copies /\
  EVERY P ((FOLDL (scan_inst_memzero dfg) mz xs).mz_flushed ++
    (FOLDL (scan_inst_memzero dfg) mz xs).mz_copies)
Proof
  Induct_on `xs` >- simp[] >>
  pure_rewrite_tac[FOLDL, EVERY_DEF] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  metis_tac[mm_local_zero_inst_certificate]
QED

Theorem mm_local_zero_prefix_certificate[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) is) ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst)
    (FOLDL (scan_inst_memzero dfg) empty_memzero_state (TAKE n is)).mz_copies /\
  EVERY (\g.
    mm_local_group_captures is (mm_local_zero_capture dfg is n) (\a. 0w) g /\
    mm_local_group_coverage is n (mm_local_zero_capture dfg is n) g)
    ((FOLDL (scan_inst_memzero dfg) empty_memzero_state (TAKE n is)).mz_flushed ++
     (FOLDL (scan_inst_memzero dfg) empty_memzero_state (TAKE n is)).mz_copies)
Proof
  strip_tac >> irule mm_local_zero_fold_certificate >>
  simp[empty_memzero_state_def] >> conj_tac
  >- (simp[EVERY_CONJ] >> metis_tac[mm_local_add_copy_captures,
                                  mm_local_add_copy_coverage]) >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `?j. j < n /\ j < LENGTH is /\ i = EL j is` by
    (fs[MEM_EL, LENGTH_TAKE_EQ] >>
     rename1 `j < if n <= LENGTH is then n else LENGTH is` >>
     `j < n /\ j < LENGTH is` by (Cases_on `n <= LENGTH is` >> gvs[] >> decide_tac) >>
     qexists `j` >> simp[EL_TAKE]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `mm_local_zero_capture dfg is n j = SOME (w2n dst, REPLICATE 32 0w)` by
        (irule mm_local_zero_capture_store >> gvs[is_zero_store_def]) >>
      conj_tac
      >- (irule mm_local_group_captures_birth >> simp[] >> qexists `j` >>
          gvs[copy_memzero_def, mm_local_bytes_def, REPLICATE_GENLIST, combinTheory.K_DEF]) >>
      irule mm_local_group_coverage_birth >> simp[] >> qexistsl [`REPLICATE 32 0w`, `j`] >>
      gvs[copy_memzero_def]) >>
  rpt gen_tac >> strip_tac >>
  `mm_local_zero_capture dfg is n j = SOME (w2n dst, REPLICATE (w2n len) 0w)` by
    (irule mm_local_zero_capture_calldata >> metis_tac[]) >>
  conj_tac
  >- (irule mm_local_group_captures_birth >> simp[] >> qexists `j` >>
      gvs[copy_memzero_def, mm_local_bytes_def, REPLICATE_GENLIST, combinTheory.K_DEF]) >>
  irule mm_local_group_coverage_birth >> simp[] >> qexistsl [`REPLICATE (w2n len) 0w`, `j`] >>
  gvs[copy_memzero_def]
QED

Theorem mm_local_zero_block_certificate[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  (scan_block_memzero dfg bb).mz_copies = [] /\
  EVERY (\g.
    mm_local_group_captures bb.bb_instructions
      (mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions))
      (\a. 0w) g /\
    mm_local_group_coverage bb.bb_instructions (LENGTH bb.bb_instructions)
      (mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions)) g)
    (scan_block_memzero dfg bb).mz_flushed
Proof
  strip_tac >>
  mp_tac (Q.INST [`is` |-> `bb.bb_instructions`, `dfg` |-> `dfg`,
    `n` |-> `LENGTH bb.bb_instructions`] mm_local_zero_prefix_certificate) >>
  simp[scan_block_memzero_def, memzero_barrier_def]
QED

Theorem mm_local_zero_representative_certificate:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM g (scan_block_memzero dfg bb).mz_flushed /\
  r < LENGTH bb.bb_instructions /\
  rep_of_group bb.bb_instructions g = SOME ((EL r bb.bb_instructions).inst_id,g) ==>
  mm_local_group_captures bb.bb_instructions
    (mm_local_zero_capture dfg bb.bb_instructions (SUC r)) (\a. 0w) g /\
  mm_local_group_coverage bb.bb_instructions (SUC r)
    (mm_local_zero_capture dfg bb.bb_instructions (SUC r)) g
Proof
  strip_tac >>
  `mm_local_group_captures bb.bb_instructions
     (mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions))
     (\a. 0w) g /\
   mm_local_group_coverage bb.bb_instructions (LENGTH bb.bb_instructions)
     (mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions)) g` by
    (drule mm_local_zero_block_certificate >> simp[EVERY_MEM]) >>
  `!j. j < LENGTH bb.bb_instructions /\
      MEM (EL j bb.bb_instructions).inst_id g.cg_inst_ids ==> j < SUC r` by
    (rpt strip_tac >>
     `j <= r` by metis_tac[mm_local_rep_position_max] >> decide_tac) >>
  `!j. j < LENGTH bb.bb_instructions /\
      MEM (EL j bb.bb_instructions).inst_id g.cg_inst_ids ==>
      mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions) j =
      mm_local_zero_capture dfg bb.bb_instructions (SUC r) j` by
    (rpt strip_tac >> irule mm_local_zero_capture_past >> simp[]) >>
  conj_tac
  >- (fs[mm_local_group_captures_def] >> metis_tac[]) >>
  fs[mm_local_group_coverage_def] >> metis_tac[]
QED

Theorem mm_local_zero_capture_sound:
  ALL_DISTINCT (MAP (\i. i.inst_id) is) /\ mm_local_history is H n /\
  (!j dst v len. j < n /\ is_calldatasize_copy dfg (EL j is) /\
    (EL j is).inst_operands = [Lit dst; Var v; Lit len] ==>
    lookup_var v (H j) = SOME (n2w (LENGTH (H j).vs_call_ctx.cc_calldata)) /\
    LENGTH (H j).vs_call_ctx.cc_calldata < dimword (:256)) /\
  mm_local_zero_capture dfg is n j = SOME (d,bs) ==>
  j < n /\ j < LENGTH is /\
  (H (SUC j)).vs_memory = (write_memory_with_expansion d bs (H j)).vs_memory
Proof
  strip_tac >> drule mm_local_zero_capture_cases >> strip_tac >>
  simp[] >> fs[mm_local_history_def]
  >- (irule (cj 2 mm_local_zero_store_capture_birth) >> simp[] >> metis_tac[]) >>
  irule (cj 2 mm_local_zero_calldata_capture_birth) >> simp[] >> metis_tac[]
QED

Definition mm_local_copy_geometry_def:
  mm_local_copy_geometry a b <=>
    ~copy_overwrites a (copy_src_interval b) /\
    ~copy_overwrites b (copy_src_interval a) /\
    (~copy_overwrites a (copy_dst_interval b) \/
     a.cg_src + b.cg_dst = a.cg_dst + b.cg_src)
End

Theorem mm_local_copy_geometry_sym[local]:
  mm_local_copy_geometry a b <=> mm_local_copy_geometry b a
Proof
  simp[mm_local_copy_geometry_def, copy_overwrites_def,
    copy_dst_interval_def, copy_src_interval_def,
    mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
    mmIntervalTheory.interval_end_def,
    arithmeticTheory.MAX_COMM, arithmeticTheory.MIN_COMM] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem mm_local_interval_overlap_point[local]:
  interval_overlaps u v <=>
  ?x. u.iv_start <= x /\ x < interval_end u /\
      v.iv_start <= x /\ x < interval_end v
Proof
  rewrite_tac[mmIntervalTheory.interval_overlaps_def] >> eq_tac
  >- (strip_tac >> qexists `MAX u.iv_start v.iv_start` >>
      fs[arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  strip_tac >>
  fs[arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem mm_local_copy_merge_source_interval[local]:
  a.cg_dst <= b.cg_dst /\ copy_can_merge a b ==>
  (!x. ((copy_merge a b).cg_src <= x /\
        x < (copy_merge a b).cg_src + (copy_merge a b).cg_length) <=>
       (a.cg_src <= x /\ x < a.cg_src + a.cg_length) \/
       (b.cg_src <= x /\ x < b.cg_src + b.cg_length))
Proof
  simp[copy_can_merge_def, copy_merge_def, arithmeticTheory.MAX_DEF] >>
  rpt strip_tac >> IF_CASES_TAC >> decide_tac
QED

Theorem mm_local_copy_merge_overwrites[local]:
  a.cg_dst <= b.cg_dst /\ copy_can_merge a b ==>
  (copy_overwrites (copy_merge a b) iv <=>
   copy_overwrites a iv \/ copy_overwrites b iv)
Proof
  strip_tac >> drule_all mm_local_copy_merge_interval >> strip_tac >>
  simp[copy_overwrites_def, copy_dst_interval_def, mm_local_interval_overlap_point,
    mmIntervalTheory.mk_interval_def, mmIntervalTheory.interval_end_def] >>
  metis_tac[]
QED

Theorem mm_local_copy_merge_source_overwritten[local]:
  a.cg_dst <= b.cg_dst /\ copy_can_merge a b ==>
  (copy_overwrites c (copy_src_interval (copy_merge a b)) <=>
   copy_overwrites c (copy_src_interval a) \/
   copy_overwrites c (copy_src_interval b))
Proof
  strip_tac >> drule_all mm_local_copy_merge_source_interval >> strip_tac >>
  simp[copy_overwrites_def, copy_dst_interval_def, copy_src_interval_def,
    mm_local_interval_overlap_point,
    mmIntervalTheory.mk_interval_def, mmIntervalTheory.interval_end_def] >>
  metis_tac[arithmeticTheory.ADD_SYM]
QED

Theorem mm_local_copy_merge_destination_overwritten[local]:
  a.cg_dst <= b.cg_dst /\ copy_can_merge a b ==>
  (copy_overwrites c (copy_dst_interval (copy_merge a b)) <=>
   copy_overwrites c (copy_dst_interval a) \/
   copy_overwrites c (copy_dst_interval b))
Proof
  strip_tac >> drule_all mm_local_copy_merge_interval >> strip_tac >>
  simp[copy_overwrites_def, copy_dst_interval_def, mm_local_interval_overlap_point,
    mmIntervalTheory.mk_interval_def, mmIntervalTheory.interval_end_def] >>
  metis_tac[]
QED

Theorem mm_local_copy_geometry_merge[local]:
  a.cg_dst <= b.cg_dst /\ copy_can_merge a b /\
  mm_local_copy_geometry a c /\ mm_local_copy_geometry b c ==>
  mm_local_copy_geometry (copy_merge a b) c
Proof
  strip_tac >>
  drule_all mm_local_copy_merge_overwrites >>
  disch_then (qspec_then `copy_src_interval c` assume_tac) >>
  drule_all mm_local_copy_merge_source_overwritten >>
  disch_then (qspec_then `c` assume_tac) >>
  simp[mm_local_copy_geometry_def] >>
  conj_tac >- metis_tac[mm_local_copy_geometry_def] >>
  conj_tac >- metis_tac[mm_local_copy_geometry_def] >>
  drule_all mm_local_copy_merge_overwrites >>
  disch_then (qspec_then `copy_dst_interval c` assume_tac) >>
  Cases_on `copy_overwrites a (copy_dst_interval c)`
  >- (fs[mm_local_copy_geometry_def] >> simp[copy_merge_def]) >>
  Cases_on `copy_overwrites b (copy_dst_interval c)`
  >- (fs[mm_local_copy_geometry_def, copy_can_merge_def] >>
      simp[copy_merge_def] >> decide_tac) >>
  simp[]
QED

Theorem mm_local_write_log_realize:
  (!d bs. MEM (d,bs) ws ==> D <= d /\ d + LENGTH bs <= D+L /\
    bs = mm_local_bytes B (src+(d-D)) (LENGTH bs)) /\
  (!a. D <= a /\ a < D+L ==> ?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs) /\
  MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws) = D+L ==>
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws =
    write_memory_with_expansion D (mm_local_bytes B src L) v
Proof
  rpt strip_tac >>
  `!a. read_byte a (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory =
    read_byte a (write_memory_with_expansion D (mm_local_bytes B src L) v).vs_memory` by
   (gen_tac >>
    `!d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs ==>
      EL (a-d) bs = B (src+(a-D))` by
     (rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >>
      `a-d < LENGTH bs /\ src+(d-D)+(a-d) = src+(a-D)` by decide_tac >>
      qpat_x_assum `bs = mm_local_bytes _ _ _` (fn th => pure_once_rewrite_tac[th]) >>
      simp[mm_local_bytes_def, EL_GENLIST]) >>
    drule venomWriteReplayPropsTheory.write_log_byte >> disch_then (qspec_then `v` mp_tac) >>
    simp[regularCallEmitSimTheory.read_byte_write_memory_with_expansion] >>
    `(?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs) <=>
       D <= a /\ a < D+L` by
      (eq_tac >- (rpt strip_tac >>
         qpat_x_assum `!d bs. MEM (d,bs) ws ==> _` (drule_then strip_assume_tac) >> decide_tac) >>
       metis_tac[]) >>
    simp[] >> Cases_on `D <= a /\ a < D+L` >> simp[] >>
    `a-D < L` by decide_tac >> simp[mm_local_bytes_def, EL_GENLIST]) >>
  `LENGTH (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory =
   LENGTH (write_memory_with_expansion D (mm_local_bytes B src L) v).vs_memory` by
    simp[venomWriteReplayPropsTheory.write_log_length, venomMemPropsTheory.LENGTH_write_memory_with_expansion] >>
  ` (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory =
    (write_memory_with_expansion D (mm_local_bytes B src L) v).vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!a. read_byte a _ = _` (qspec_then `x` mp_tac) >>
     simp[codegenRelTheory.read_byte_def]) >>
  qspecl_then [`ws`,`v`] strip_assume_tac venomWriteReplayPropsTheory.write_log_frame >>
  gvs[write_as_replace, venomStateTheory.venom_state_component_equality]
QED

Theorem mm_local_write_log_endpoint_birth[local]:
  (!d bs. MEM (d,bs) [(g.cg_dst,mm_local_bytes B g.cg_src g.cg_length)] ==>
      d + LENGTH bs <= g.cg_dst + g.cg_length) /\
  (?d bs. MEM (d,bs) [(g.cg_dst,mm_local_bytes B g.cg_src g.cg_length)] /\
      d + LENGTH bs = g.cg_dst + g.cg_length)
Proof
  simp[]
QED

Theorem mm_local_write_log_endpoint_merge[local]:
  (!d bs. MEM (d,bs) xs ==> d + LENGTH bs <= a.cg_dst + a.cg_length) /\
  (?d bs. MEM (d,bs) xs /\ d + LENGTH bs = a.cg_dst + a.cg_length) /\
  (!d bs. MEM (d,bs) ys ==> d + LENGTH bs <= b.cg_dst + b.cg_length) /\
  (?d bs. MEM (d,bs) ys /\ d + LENGTH bs = b.cg_dst + b.cg_length) ==>
  (!d bs. MEM (d,bs) (xs ++ ys) ==>
      d + LENGTH bs <= (copy_merge a b).cg_dst + (copy_merge a b).cg_length) /\
  (?d bs. MEM (d,bs) (xs ++ ys) /\
      d + LENGTH bs = (copy_merge a b).cg_dst + (copy_merge a b).cg_length)
Proof
  rpt strip_tac >>
  `(copy_merge a b).cg_dst + (copy_merge a b).cg_length =
    MAX (a.cg_dst + a.cg_length) (b.cg_dst + b.cg_length)` by
    (simp[copy_merge_def, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  simp[MEM_APPEND] >>
  Cases_on `a.cg_dst + a.cg_length <= b.cg_dst + b.cg_length` >>
  simp[arithmeticTheory.MAX_DEF] >> metis_tac[MEM_APPEND]
QED

Theorem mm_local_canonical_selected_fragment[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n <= LENGTH is /\ n <= N /\ mm_local_history is H N /\
  MEM j (mm_local_pending_indices is gs n) /\
  MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids ==>
  ?h d bs. MEM h ss.ss_copies /\ mm_local_copy_ancestor h g /\
    MEM (EL j is).inst_id h.cg_inst_ids /\
    mm_local_write_capture is H N j = SOME (d,bs) /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length
Proof
  strip_tac >> drule_all mm_local_canonical_pending_owner >> strip_tac >>
  qexistsl [`h`,`d`,`bs`] >> simp[] >>
  irule mm_local_cut_selected_ancestor >>
  qexistsl [`bb`,`dfg_build_function fn0`,`(EL j is).inst_id`,`Mem2Mem`,
    `DROP n is`,`TAKE n is`,`ss`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule mm_local_prefix_write_group_owner >>
  goal_assum (drule_at Any) >>
  qpat_assum `MEM j (mm_local_pending_indices _ _ _)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  `j < LENGTH is` by decide_tac >> metis_tac[EL_MEM]
QED

(* Temporary refutation of the proposed hereditary irreducibility interface. *)
Theorem mm_local_hereditary_irreducibility_probe[local]:
  !dfg. ~(!xs pre a mid b post.
    (FOLDL (scan_inst dfg Mem2Mem) empty_scan_state xs).ss_copies =
      pre ++ [a] ++ mid ++ [b] ++ post ==> ~copy_can_merge a b)
Proof
  gen_tac >> strip_tac >>
  qspec_then `dfg` strip_assume_tac mm_local_empty_blocker_probe >>
  first_x_assum (qspecl_then
    [`[mk_inst 1 MCOPY [Lit 0w; Lit 1000w; Lit 100w] [];
       mk_inst 2 MCOPY [Lit 50w; Lit 3000w; Lit 0w] [];
       mk_inst 3 MCOPY [Lit 90w; Lit 1090w; Lit 10w] []]`,
     `[]`,
     `<|cg_dst := 0; cg_src := 1000; cg_length := 100; cg_inst_ids := [1]|>`,
     `[<|cg_dst := 50; cg_src := 3000; cg_length := 0; cg_inst_ids := [2]|>]`,
     `<|cg_dst := 90; cg_src := 1090; cg_length := 10; cg_inst_ids := [3]|>`,
     `[]`] mp_tac) >> simp[]
QED

Theorem mm_local_empty_copy_overwrites[local]:
  h.cg_length = 0 ==>
  ~copy_overwrites h iv /\ ~copy_overwrites c (copy_dst_interval h) /\
  ~copy_overwrites c (copy_src_interval h)
Proof
  simp[copy_overwrites_def, copy_dst_interval_def, copy_src_interval_def,
    mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.interval_end_def,
    mmIntervalTheory.mk_interval_def,
    arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem mm_local_empty_copy_hazards[local]:
  h.cg_length = 0 /\ MEM h ss.ss_copies ==>
  MEM h (flush_hazards mode ss c).ss_copies
Proof
  strip_tac >>
  `~copy_overwrites h (copy_src_interval c) /\
   ~copy_overwrites c (copy_dst_interval h) /\
   ~copy_overwrites c (copy_src_interval h)` by
    metis_tac[mm_local_empty_copy_overwrites] >>
  simp[flush_hazards_def] >> rpt IF_CASES_TAC >>
  gvs[flush_copies_def, MEM_FILTER, waw_hazards_def,
    raw_hazards_def, war_hazards_def, copies_that_overwrite_def]
QED

(* Temporary bounded continuation checks; remove at delivery. *)
Theorem mm_local_empty_blocker_continuations_probe[local]:
  !dfg. EVERY (\i.
    MEM <|cg_dst := 50; cg_src := 3000; cg_length := 0; cg_inst_ids := [2]|>
      (scan_inst dfg Mem2Mem
        (FOLDL (scan_inst dfg Mem2Mem) empty_scan_state
          [mk_inst 1 MCOPY [Lit 0w; Lit 1000w; Lit 100w] [];
           mk_inst 2 MCOPY [Lit 50w; Lit 3000w; Lit 0w] [];
           mk_inst 3 MCOPY [Lit 90w; Lit 1090w; Lit 10w] []]) i).ss_copies)
    [mk_inst 4 MCOPY [Lit 3000w; Lit 5000w; Lit 32w] [];
     mk_inst 4 MCOPY [Lit 50w; Lit 5000w; Lit 32w] [];
     mk_inst 4 MCOPY [Lit 5000w; Lit 50w; Lit 32w] [];
     mk_inst 4 MLOAD [Lit 50w] ["v"]]
Proof
  gen_tac >> EVAL_TAC
QED

Theorem mm_local_pending_hazard_read[local]:
  mm_local_pending cap js s t /\
  (!j. MEM j js ==> ?d bs h. cap j = SOME (d,bs) /\
    MEM h (flush_hazards Mem2Mem ss c).ss_copies /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length) ==>
  read_memory c.cg_src c.cg_length s = read_memory c.cg_src c.cg_length t
Proof
  strip_tac >>
  qpat_x_assum `mm_local_pending _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_def]) >>
  irule venomWriteReplayPropsTheory.read_write_log_memory >> qexists `ws` >> simp[] >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  qpat_x_assum `!j. MEM j js ==> _` (drule_then strip_assume_tac) >>
  gvs[] >> drule mm_local_hazards_source_exclusion >> strip_tac >>
  drule_all (INST_TYPE [alpha |-> ``:word8``] mm_local_capture_source_exclusion) >>
  simp[] >> metis_tac[LENGTH_NIL]
QED

Theorem mm_local_pending_cap_cong:
  mm_local_pending cap js s t /\ (!j. MEM j js ==> cap' j = cap j) ==>
  mm_local_pending cap' js s t
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >> qexists `ws` >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `MEM (EL n js) js` by simp[EL_MEM] >> metis_tac[]
QED

Theorem mm_local_bulk_deferred_capture[local]:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  i = EL j is /\ i.inst_opcode = MCOPY /\
  i.inst_operands = [Lit dst; Lit src; Lit len] /\ step_inst_base i s = OK s' /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [i.inst_id] |> /\
  hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c /\
  cap' = (\q. if q = j then SOME (w2n dst, read_memory (w2n src) (w2n len) s)
             else cap q) /\
  mm_local_pending cap js s t /\ ~MEM j js /\
  (!q. MEM q js ==> ?d bs h. cap q = SOME (d,bs) /\ MEM h hs.ss_copies /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length) /\
  (!a l. mm_local_bytes B a l = read_memory a l t) /\
  EVERY (mm_local_group_captures is cap B) hs.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) hs.ss_copies /\
  (!h. MEM h hs.ss_copies ==> ~MEM i.inst_id h.cg_inst_ids) ==>
  (scan_inst dfg Mem2Mem ss i).ss_copies = add_copy hs.ss_copies c /\
  EVERY (mm_local_group_captures is cap' B) (add_copy hs.ss_copies c) /\
  mm_local_pending cap' (js ++ [j]) s' t
Proof
  strip_tac >>
  `read_memory (w2n src) (w2n len) s = read_memory (w2n src) (w2n len) t` by
   (`read_memory c.cg_src c.cg_length s = read_memory c.cg_src c.cg_length t` by
     (irule (INST_TYPE [alpha |-> ``:num``] mm_local_pending_hazard_read) >>
      qexistsl [`cap`,`js`,`invalidate_loads ss (mk_interval (w2n dst) (w2n len))`] >>
      metis_tac[]) >>
    gvs[]) >>
  `mm_local_bytes B (w2n src) (w2n len) = read_memory (w2n src) (w2n len) s` by metis_tac[] >>
  drule_all mm_local_bulk_capture_birth >> strip_tac >>
  conj_tac >- simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  conj_tac
  >- (irule mm_local_add_copy_captures >> simp[] >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      irule mm_local_group_captures_extend >>
      qexistsl [`read_memory (w2n src) (w2n len) t`,`cap`,`w2n dst`,`j`] >>
      gvs[EVERY_MEM]) >>
  `mm_local_pending cap' js s t` by
    (irule mm_local_pending_cap_cong >> goal_assum (drule_at Any) >>
     rpt strip_tac >> simp[] >> metis_tac[]) >>
  irule mm_local_pending_create >> metis_tac[]
QED

Theorem mm_local_store_deferred_capture[local]:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  i = EL j is /\ i.inst_opcode = MSTORE /\ i.inst_operands = [Lit dst; Var v] /\
  FLOOKUP ss.ss_loads v = SOME src /\ lookup_var v s = SOME (mload src s) /\
  step_inst_base i s = OK s' /\
  lids = (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) /\
  ~MEM i.inst_id lids /\
  (!q. q < LENGTH is /\ MEM (EL q is).inst_id lids ==> cap q = NONE) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [i.inst_id] ++ lids |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) 32)) c /\
  cap' = (\q. if q = j then SOME (w2n dst, read_memory src 32 s) else cap q) /\
  mm_local_pending cap js s t /\ ~MEM j js /\
  (!q. MEM q js ==> ?d bs h. cap q = SOME (d,bs) /\ MEM h hs.ss_copies /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length) /\
  (!a l. mm_local_bytes B a l = read_memory a l t) /\
  EVERY (mm_local_group_captures is cap B) hs.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) hs.ss_copies /\
  (!h. MEM h hs.ss_copies ==> ~MEM i.inst_id h.cg_inst_ids) ==>
  (scan_inst dfg Mem2Mem ss i).ss_copies = add_copy hs.ss_copies c /\
  EVERY (mm_local_group_captures is cap' B) (add_copy hs.ss_copies c) /\
  mm_local_pending cap' (js ++ [j]) s' t
Proof
  strip_tac >>
  `read_memory src 32 s = read_memory src 32 t` by
   (`read_memory c.cg_src c.cg_length s = read_memory c.cg_src c.cg_length t` by
     (irule (INST_TYPE [alpha |-> ``:num``] mm_local_pending_hazard_read) >>
      qexistsl [`cap`,`js`,`invalidate_loads ss (mk_interval (w2n dst) 32)`] >>
      metis_tac[]) >> gvs[]) >>
  `mm_local_bytes B src 32 = read_memory src 32 s` by metis_tac[] >>
  drule_all mm_local_store_capture_birth >> strip_tac >>
  conj_tac >- simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  conj_tac
  >- (irule mm_local_add_copy_captures >> simp[] >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      irule mm_local_group_captures_extend >>
      qexistsl [`read_memory src 32 t`,`cap`,`w2n dst`,`j`] >>
      gvs[EVERY_MEM]) >>
  `mm_local_pending cap' js s t` by
    (irule mm_local_pending_cap_cong >> goal_assum (drule_at Any) >>
     rpt strip_tac >> simp[] >> metis_tac[]) >>
  irule mm_local_pending_create >> metis_tac[]
QED

Theorem mm_local_store_deferred_post_phis[local]:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  h = phi_prefix_length bb.bb_instructions /\ h <= j /\ j < LENGTH bb.bb_instructions /\
  LENGTH states = SUC (j-h) /\
  eval_phis entry bb.bb_instructions = OK s_phi /\
  EL 0 states = s_phi with vs_inst_idx := h /\
  (!r. r < j-h ==>
    ~is_terminator (EL (h+r) bb.bb_instructions).inst_opcode /\
    ?u. step_inst fuel ctx (EL (h+r) bb.bb_instructions) (EL r states) = OK u /\
        EL (SUC r) states = u with vs_inst_idx := SUC (EL r states).vs_inst_idx) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state
      (TAKE j bb.bb_instructions) /\
  s = EL (j-h) states /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  i = EL j bb.bb_instructions /\ i.inst_opcode = MSTORE /\
  i.inst_operands = [Lit dst; Var v] /\ FLOOKUP ss.ss_loads v = SOME src /\
  step_inst_base i s = OK s' /\
  lids = (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id]) /\
  ~MEM i.inst_id lids /\
  (!q. q < LENGTH bb.bb_instructions /\ MEM (EL q bb.bb_instructions).inst_id lids ==> cap q = NONE) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [i.inst_id] ++ lids |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) 32)) c /\
  cap' = (\q. if q = j then SOME (w2n dst, read_memory src 32 s) else cap q) /\
  mm_local_pending cap js s t /\ ~MEM j js /\
  (!q. MEM q js ==> ?d bs g. cap q = SOME (d,bs) /\ MEM g hs.ss_copies /\
    g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length) /\
  (!a l. mm_local_bytes B a l = read_memory a l t) /\
  EVERY (mm_local_group_captures bb.bb_instructions cap B) hs.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) hs.ss_copies /\
  (!g. MEM g hs.ss_copies ==> ~MEM i.inst_id g.cg_inst_ids) ==>
  (scan_inst (dfg_build_function fn0) Mem2Mem ss i).ss_copies = add_copy hs.ss_copies c /\
  EVERY (mm_local_group_captures bb.bb_instructions cap' B) (add_copy hs.ss_copies c) /\
  mm_local_pending cap' (js ++ [j]) s' t
Proof
  strip_tac >>
  `j <= LENGTH bb.bb_instructions` by decide_tac >>
  drule_all mm_local_live_load_post_phis >>
  strip_tac >>
  irule mm_local_store_deferred_capture >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem mm_local_hazards_captures_rebase[local]:
  !is cap B ss c payload t t' C.
  EVERY (mm_local_group_captures is cap B) ss.ss_copies /\
  (!a l. mm_local_bytes B a l = read_memory a l t) /\
  LENGTH payload = c.cg_length /\
  t'.vs_memory = (write_memory_with_expansion c.cg_dst payload t).vs_memory /\
  (!a l. mm_local_bytes C a l = read_memory a l t') ==>
  EVERY (mm_local_group_captures is cap C) (flush_hazards Mem2Mem ss c).ss_copies
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (mm_local_group_captures is cap B) (flush_hazards Mem2Mem ss c).ss_copies` by
   (simp[flush_hazards_def, mode_allows_overlap_def] >> rpt IF_CASES_TAC >>
    gvs[flush_copies_def, EVERY_FILTER, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule mm_local_group_captures_rebase >> qexists `B` >>
  conj_tac
  >- (drule_all mm_local_flush_hazards_read >>
      simp[venomStateTheory.read_memory_def]) >>
  gvs[EVERY_MEM]
QED

Theorem mm_local_hazards_capture_compatible[local]:
  MEM g (flush_hazards mode ss c).ss_copies /\
  mm_local_group_captures is cap B g /\
  j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
  cap j = SOME (d,bs) ==>
  mm_local_write_compatible d bs c.cg_dst (mm_local_bytes B c.cg_src c.cg_length)
Proof
  strip_tac >>
  `g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
   bs = mm_local_bytes B (g.cg_src + (d-g.cg_dst)) (LENGTH bs)` by
    metis_tac[mm_local_group_captures_def] >>
  drule mm_local_hazards_destination_alternative >> strip_tac
  >- (gvs[copy_overwrites_def, copy_dst_interval_def,
          mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
          mmIntervalTheory.interval_end_def, arithmeticTheory.MAX_DEF,
          arithmeticTheory.MIN_DEF, mm_local_write_compatible_def] >>
      rpt strip_tac >> gvs[] >> decide_tac)
  >- (gvs[copy_can_merge_def, mm_local_write_compatible_def,
          mm_local_bytes_def, EL_GENLIST] >> rpt strip_tac >>
      qpat_x_assum `bs = GENLIST _ _` (fn th => once_rewrite_tac[th]) >>
      simp[EL_GENLIST] >> AP_TERM_TAC >> decide_tac) >>
  gvs[copy_can_merge_def, mm_local_write_compatible_def,
      mm_local_bytes_def, EL_GENLIST] >> rpt strip_tac >>
      qpat_x_assum `bs = GENLIST _ _` (fn th => once_rewrite_tac[th]) >>
      simp[EL_GENLIST] >> AP_TERM_TAC >> decide_tac
QED

Theorem mm_local_hazards_new_geometry[local]:
  MEM g (flush_hazards Mem2Mem ss c).ss_copies ==>
  mm_local_copy_geometry g c
Proof
  strip_tac >>
  drule mm_local_flush_hazards_survivor >> strip_tac >>
  drule mm_local_hazards_source_exclusion >> strip_tac >>
  drule mm_local_hazards_destination_alternative >>
  simp[mm_local_copy_geometry_def, copy_can_merge_def,
    copy_overwrites_def, copy_dst_interval_def,
    mmIntervalTheory.interval_overlaps_def,
    arithmeticTheory.MAX_COMM, arithmeticTheory.MIN_COMM] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Definition mm_local_copies_geometry_def:
  (mm_local_copies_geometry [] = T) /\
  (mm_local_copies_geometry (g::gs) <=>
    EVERY (mm_local_copy_geometry g) gs /\ mm_local_copies_geometry gs)
End

Theorem mm_local_copies_geometry_filter[local]:
  !gs. mm_local_copies_geometry gs ==> mm_local_copies_geometry (FILTER P gs)
Proof
  Induct >> simp[mm_local_copies_geometry_def] >> rpt strip_tac >>
  IF_CASES_TAC >> gvs[mm_local_copies_geometry_def, EVERY_MEM, MEM_FILTER]
QED

Theorem mm_local_copies_geometry_split[local]:
  !pre a mid b post.
  mm_local_copies_geometry (pre ++ (a::(mid ++ (b::post)))) ==>
  mm_local_copy_geometry a b
Proof
  Induct >> simp[mm_local_copies_geometry_def, EVERY_APPEND] >> rpt strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem mm_local_geometry_merge_every[local]:
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
  EVERY (mm_local_copy_geometry c) cs ==>
  EVERY (mm_local_copy_geometry c) (merge_adjacent cs)
Proof
  recInduct merge_adjacent_ind >> simp[merge_adjacent_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2`
  >- (gvs[] >> first_x_assum irule >> conj_tac
      >- (gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
              copy_merge_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      simp[] >> once_rewrite_tac[mm_local_copy_geometry_sym] >>
      irule mm_local_copy_geometry_merge >>
      gvs[sortingTheory.SORTED_DEF] >> metis_tac[mm_local_copy_geometry_sym]) >>
  gvs[] >> first_x_assum irule >> gvs[sortingTheory.SORTED_DEF]
QED

Theorem mm_local_copies_geometry_merge[local]:
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\ mm_local_copies_geometry cs ==>
  mm_local_copies_geometry (merge_adjacent cs)
Proof
  recInduct merge_adjacent_ind >> simp[merge_adjacent_def, mm_local_copies_geometry_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2`
  >- (gvs[] >> first_x_assum irule >> conj_tac
      >- (simp[mm_local_copies_geometry_def] >>
          gvs[EVERY_MEM, sortingTheory.SORTED_DEF] >> rpt strip_tac >>
          irule mm_local_copy_geometry_merge >> metis_tac[]) >>
      gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
          copy_merge_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[mm_local_copies_geometry_def] >>
  irule mm_local_geometry_merge_every >> simp[]
QED

Theorem mm_local_copies_geometry_insert[local]:
  !gs c. mm_local_copies_geometry gs /\ EVERY (mm_local_copy_geometry c) gs ==>
  mm_local_copies_geometry (insert_sorted gs c)
Proof
  Induct >> simp[insert_sorted_def, mm_local_copies_geometry_def] >>
  rpt gen_tac >> strip_tac >> IF_CASES_TAC >>
  gvs[mm_local_copies_geometry_def] >>
  simp[mm_local_insert_every, mm_local_copy_geometry_sym]
QED

Theorem mm_local_copies_geometry_add[local]:
  mm_local_copies_geometry gs /\ EVERY (mm_local_copy_geometry c) gs /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) gs ==>
  mm_local_copies_geometry (add_copy gs c)
Proof
  strip_tac >> simp[add_copy_def] >> irule mm_local_copies_geometry_merge >>
  metis_tac[mm_local_insert_sorted_order, mm_local_copies_geometry_insert]
QED

Theorem mm_local_flush_geometry[local]:
  mm_local_copies_geometry ss.ss_copies ==>
  mm_local_copies_geometry (flush_copies ss cs).ss_copies
Proof
  simp[flush_copies_def, mm_local_copies_geometry_filter]
QED

Theorem mm_local_hazards_geometry[local]:
  mm_local_copies_geometry ss.ss_copies ==>
  mm_local_copies_geometry (flush_hazards mode ss c).ss_copies
Proof
  simp[flush_hazards_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> metis_tac[mm_local_flush_geometry]
QED

Theorem mm_local_load_geometry[local]:
  mm_local_copies_geometry ss.ss_copies ==>
  mm_local_copies_geometry (scan_load mode ss inst).ss_copies
Proof
  strip_tac >> simp[scan_load_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def, mm_local_copies_geometry_def] >>
  rpt IF_CASES_TAC >> simp[mm_local_flush_geometry]
QED

Theorem mm_local_hazards_add_geometry[local]:
  mm_local_copies_geometry ss.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  mm_local_copies_geometry (add_copy (flush_hazards Mem2Mem ss c).ss_copies c)
Proof
  strip_tac >> irule mm_local_copies_geometry_add >>
  simp[mm_local_hazards_geometry, mm_local_hazards_order, EVERY_MEM] >>
  metis_tac[mm_local_hazards_new_geometry, mm_local_copy_geometry_sym]
QED

Theorem mm_local_store_geometry[local]:
  mm_local_copies_geometry ss.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  mm_local_copies_geometry (scan_store dfg Mem2Mem ss inst).ss_copies
Proof
  strip_tac >> simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def, mm_local_copies_geometry_def] >>
  irule mm_local_hazards_add_geometry >> simp[invalidate_loads_def]
QED

Theorem mm_local_bulk_geometry[local]:
  mm_local_copies_geometry ss.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  mm_local_copies_geometry (scan_bulk_copy Mem2Mem ss inst).ss_copies
Proof
  strip_tac >> simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def, mm_local_copies_geometry_def] >>
  irule mm_local_hazards_add_geometry >> simp[invalidate_loads_def]
QED

Theorem mm_local_inst_geometry[local]:
  mm_local_copies_geometry ss.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  mm_local_copies_geometry (scan_inst dfg Mem2Mem ss inst).ss_copies
Proof
  strip_tac >> simp[scan_inst_def] >> rpt IF_CASES_TAC >>
  simp[mm_local_load_geometry, mm_local_store_geometry, mm_local_bulk_geometry,
       hard_barrier_def, mm_local_copies_geometry_def]
QED

Theorem mm_local_fold_geometry[local]:
  !is ss. mm_local_copies_geometry ss.ss_copies /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  mm_local_copies_geometry (FOLDL (scan_inst dfg Mem2Mem) ss is).ss_copies
Proof
  Induct >> simp[] >> metis_tac[mm_local_inst_geometry, mm_local_inst_order]
QED

Theorem mm_local_scan_geometry[local]:
  mm_local_copies_geometry
    (FOLDL (scan_inst dfg Mem2Mem) empty_scan_state is).ss_copies
Proof
  irule mm_local_fold_geometry >>
  simp[empty_scan_state_def, mm_local_copies_geometry_def]
QED

Theorem mm_local_copies_geometry_members[local]:
  !gs a b. mm_local_copies_geometry gs /\ MEM a gs /\ MEM b gs /\ a <> b ==>
  mm_local_copy_geometry a b
Proof
  Induct >> simp[mm_local_copies_geometry_def, EVERY_MEM] >>
  metis_tac[mm_local_copy_geometry_sym]
QED

Theorem mm_local_active_emission_captures[local]:
  mm_local_copies_geometry gs /\ MEM g gs /\
  EVERY (mm_local_group_captures is cap B) gs /\
  (!a l. mm_local_bytes B a l = read_memory a l t) /\
  LENGTH payload = g.cg_length /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst payload t).vs_memory /\
  (!a l. mm_local_bytes C a l = read_memory a l t') ==>
  EVERY (mm_local_group_captures is cap C) (FILTER (\h. h <> g) gs)
Proof
  simp[EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
  rename1 `mm_local_group_captures is cap C h` >>
  irule mm_local_group_captures_rebase >> qexists `B` >> simp[] >>
  `mm_local_copy_geometry g h` by
    (irule mm_local_copies_geometry_members >> metis_tac[]) >>
  `h.cg_length = 0 \/ payload = [] \/
   h.cg_src + h.cg_length <= g.cg_dst \/
   g.cg_dst + LENGTH payload <= h.cg_src` by
    (gvs[mm_local_copy_geometry_def, copy_overwrites_def,
       copy_src_interval_def, copy_dst_interval_def,
       mmIntervalTheory.interval_overlaps_def,
       mmIntervalTheory.mk_interval_def, mmIntervalTheory.interval_end_def,
       arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
     Cases_on `payload` >> gvs[] >> decide_tac) >>
  simp[venomStateTheory.read_memory_def] >>
  metis_tac[venomWriteReplayPropsTheory.read_write_disjoint, venomStateTheory.read_memory_def]
QED

Theorem mm_local_merge_partition[local]:
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs ==>
  ?chunks. FLAT chunks = cs /\
    LIST_REL (\parts g.
      parts <> [] /\ g = FOLDL copy_merge (HD parts) (TL parts) /\
      g.cg_inst_ids = FLAT (MAP (\h. h.cg_inst_ids) parts) /\
      EVERY (\h. mm_local_copy_ancestor h g) parts)
      chunks (merge_adjacent cs)
Proof
  recInduct merge_adjacent_ind >> rpt conj_tac
  >- (strip_tac >> qexists `[]` >> simp[merge_adjacent_def])
  >- (gen_tac >> strip_tac >> qexists `[[c]]` >>
      simp[merge_adjacent_def, mm_local_copy_ancestor_refl]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2` >> gvs[]
  >- (`SORTED (\a b. a.cg_dst <= b.cg_dst) (copy_merge c1 c2::rest)` by
        (gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
             copy_merge_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      first_x_assum (drule_then strip_assume_tac) >>
      rename1 `FLAT qs = copy_merge c1 c2::rest` >>
      namedCases_on `qs` ["", "ps qss"] >> gvs[] >>
      namedCases_on `ps` ["", "p ps'"] >> gvs[] >>
      qexists `(c1::c2::ps')::qss` >>
      simp[Once merge_adjacent_def] >>
      simp[GSYM APPEND_ASSOC] >>
      drule_all mm_local_copy_merge_ancestors >> strip_tac >>
      conj_tac >- gvs[copy_merge_def] >>
      metis_tac[mm_local_copy_ancestor_trans]) >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst) (c2::rest)` by
    gvs[sortingTheory.SORTED_DEF] >>
  rename1 `FLAT qs = c2::rest` >>
  qexists `[c1]::qs` >>
  simp[merge_adjacent_def, mm_local_copy_ancestor_refl]
QED

Theorem mm_local_add_partition[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) cs ==>
  ?chunks. FLAT chunks = insert_sorted cs c /\
    LIST_REL (\parts g.
      parts <> [] /\ g = FOLDL copy_merge (HD parts) (TL parts) /\
      g.cg_inst_ids = FLAT (MAP (\h. h.cg_inst_ids) parts) /\
      EVERY (\h. mm_local_copy_ancestor h g) parts)
      chunks (add_copy cs c)
Proof
  strip_tac >> simp[add_copy_def] >> irule mm_local_merge_partition >>
  simp[mm_local_insert_sorted_order]
QED

Theorem mm_local_add_constituents[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\ MEM g (add_copy cs c) ==>
  ?parts. parts <> [] /\
    g = FOLDL copy_merge (HD parts) (TL parts) /\
    g.cg_inst_ids = FLAT (MAP (\h. h.cg_inst_ids) parts) /\
    EVERY (\h. mm_local_copy_ancestor h g) parts /\
    EVERY (\h. h = c \/ MEM h cs) parts
Proof
  strip_tac >> drule mm_local_add_partition >>
  disch_then (qspec_then `c` strip_assume_tac) >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  qexists `x` >> simp[] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  `MEM h (insert_sorted cs c)` by metis_tac[MEM_FLAT] >>
  metis_tac[mm_local_insert_sorted_mem]
QED

Theorem mm_local_ancestral_interval_read_recurrence[local]:
  !b a. a <= b /\ b <= n /\ b <= LENGTH is /\
  (!q. a <= q /\ q < b ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H n q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  (!q. a <= q /\ q < b ==>
    ?h. MEM h (cuts q).ss_copies /\ mm_local_copy_ancestor c h /\
        ~MEM h (scan_inst dfg Mem2Mem (cuts q) (EL q is)).ss_flushed) ==>
  read_memory c.cg_src c.cg_length (H b) =
  read_memory c.cg_src c.cg_length (H a)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `a = SUC b` >- simp[] >>
  `a <= b /\ b < n` by decide_tac >>
  `read_memory c.cg_src c.cg_length (H b) =
   read_memory c.cg_src c.cg_length (H a)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `?h. MEM h (cuts b).ss_copies /\ mm_local_copy_ancestor c h /\
       ~MEM h (scan_inst dfg Mem2Mem (cuts b) (EL b is)).ss_flushed` by
    (first_x_assum irule >> simp[]) >>
  `h.cg_src <= c.cg_src /\
   c.cg_src + c.cg_length <= h.cg_src + h.cg_length` by
    (gvs[mm_local_copy_ancestor_def] >> decide_tac) >>
  `b < LENGTH is` by decide_tac >>
  `(H (SUC b)).vs_memory =
    (case mm_local_write_capture is H n b of NONE => H b
     | SOME (d,bs) => write_memory_with_expansion d bs (H b)).vs_memory` by
    (first_x_assum irule >> simp[]) >>
  drule_all mm_local_surviving_source_read_recurrence >> simp[]
QED

Theorem mm_local_ancestral_interval_read[local]:
  !b a. mm_local_history is H n /\ a <= b /\ b <= n /\
  (!q. a <= q /\ q < b ==>
    ?h. MEM h (cuts q).ss_copies /\ mm_local_copy_ancestor c h /\
        ~MEM h (scan_inst dfg Mem2Mem (cuts q) (EL q is)).ss_flushed) ==>
  read_memory c.cg_src c.cg_length (H b) =
  read_memory c.cg_src c.cg_length (H a)
Proof
  rpt strip_tac >>
  `b <= LENGTH is` by gvs[mm_local_history_def] >>
  `!q. a <= q /\ q < b ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H n q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (rpt strip_tac >> `q < n` by decide_tac >>
     `?h. MEM h (cuts q).ss_copies /\ mm_local_copy_ancestor c h /\
        ~MEM h (scan_inst dfg Mem2Mem (cuts q) (EL q is)).ss_flushed` by
       metis_tac[] >>
     Cases_on `mm_local_write_capture is H n q`
     >- (simp[] >> metis_tac[mm_local_surviving_history_frame]) >>
     PairCases_on `x` >> simp[] >> metis_tac[mm_local_write_capture_sound]) >>
  metis_tac[mm_local_ancestral_interval_read_recurrence]
QED

Theorem mm_local_ancestral_interval_captures[local]:
  mm_local_history is H n /\ a <= b /\ b <= n /\
  (!q. a <= q /\ q < b ==>
    ?h. MEM h (cuts q).ss_copies /\ mm_local_copy_ancestor c h /\
        ~MEM h (scan_inst dfg Mem2Mem (cuts q) (EL q is)).ss_flushed) /\
  mm_local_group_captures is cap B c /\
  (!x l. mm_local_bytes B x l = read_memory x l (H a)) /\
  (!x l. mm_local_bytes C x l = read_memory x l (H b)) ==>
  mm_local_group_captures is cap C c
Proof
  strip_tac >> irule mm_local_group_captures_rebase >> qexists `B` >>
  simp[] >> drule_all mm_local_ancestral_interval_read >> simp[]
QED

Theorem mm_local_indexed_pending_ancestor[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n <= r /\ r < LENGTH is /\ j < LENGTH is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE n is) /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) /\ MEM (EL j is).inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  MEM h ss.ss_copies /\ mm_local_copy_ancestor h g
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule venomTransformStructurePropsTheory.future_id_not_prefix >> simp[]) >>
  `bb.bb_instructions = TAKE n is ++ DROP n is` by simp[] >>
  `MEM (EL j is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `rep_of_group bb.bb_instructions g = SOME ((EL r is).inst_id,g)` by metis_tac[] >>
  drule_all mm_local_prefix_write_pending_ancestor >> simp[]
QED

Theorem mm_local_indexed_bulk_ancestry[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < q /\ q <= r /\ r < LENGTH is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE q is) /\
  (EL j is).inst_opcode = mode_copy_opcode mode /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  c = <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id]|> /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
      mm_local_copy_ancestor c h /\ mm_local_copy_ancestor h g
Proof
  strip_tac >> drule_all mm_local_indexed_bulk_owner >> strip_tac >>
  `MEM h ss.ss_copies /\ mm_local_copy_ancestor h g` by
    (`MEM h (ss.ss_copies ++ ss.ss_flushed)` by simp[MEM_APPEND] >>
     `j < LENGTH is` by decide_tac >>
     `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
       (Cases_on `mode` >> gvs[mode_copy_opcode_def]) >>
     drule_all mm_local_indexed_pending_ancestor >> simp[]) >>
  qexists `h` >> gvs[]
QED

Theorem mm_local_indexed_store_ancestry[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < q /\ q <= r /\ r < LENGTH is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE q is) /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads v = SOME src /\
  c = <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id])|> /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
      mm_local_copy_ancestor c h /\ mm_local_copy_ancestor h g
Proof
  strip_tac >>
  `?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor c h` by
    (irule mm_local_store_cut_fragment >>
     goal_assum (drule_at Any) >> simp[] >> qexistsl [`mode`, `q`] >> gvs[] >> decide_tac) >>
  `MEM (EL j is).inst_id h.cg_inst_ids` by
    (gvs[mm_local_copy_ancestor_def] >> metis_tac[MEM_APPEND, MEM]) >>
  `MEM h ss.ss_copies /\ mm_local_copy_ancestor h g` by
    (`j < LENGTH is` by decide_tac >>
     `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by simp[] >>
     drule_all mm_local_indexed_pending_ancestor >> simp[]) >>
  qexists `h` >> gvs[]
QED

Theorem mm_local_indexed_bulk_trajectory[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ SUC j <= q /\ q < r /\ r < LENGTH is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE q is) /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  c = <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id]|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ?h. MEM h ss.ss_copies /\ mm_local_copy_ancestor c h /\
      ~MEM h (scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is)).ss_flushed
Proof
  strip_tac >>
  `j < q /\ q <= r` by decide_tac >>
  drule_all (REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_bulk_ancestry)) >> strip_tac >>
  `scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is) =
     FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE (SUC q) is)` by
    (`q < LENGTH is` by decide_tac >>
     simp[rich_listTheory.TAKE_SUC, rich_listTheory.DROP_EL_CONS, FOLDL_APPEND]) >>
  `~MEM h (scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is)).ss_flushed` by
    (`SUC q <= r /\ j < LENGTH is` by decide_tac >>
     `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by simp[] >>
     drule_all mm_local_indexed_future_not_flushed >> simp[]) >>
  qexists `h` >> simp[]
QED

Theorem mm_local_indexed_store_trajectory[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ SUC j <= q /\ q < r /\ r < LENGTH is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE q is) /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads v = SOME src /\
  c = <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id])|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ?h. MEM h ss.ss_copies /\ mm_local_copy_ancestor c h /\
      ~MEM h (scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is)).ss_flushed
Proof
  strip_tac >>
  `j < q /\ q <= r` by decide_tac >>
  drule_all mm_local_indexed_store_ancestry >> strip_tac >>
  `scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is) =
     FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE (SUC q) is)` by
    (`q < LENGTH is` by decide_tac >>
     simp[rich_listTheory.TAKE_SUC, rich_listTheory.DROP_EL_CONS, FOLDL_APPEND]) >>
  `~MEM h (scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is)).ss_flushed` by
    (`SUC q <= r /\ j < LENGTH is` by decide_tac >>
     `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by simp[] >>
     drule_all mm_local_indexed_future_not_flushed >> simp[]) >>
  qexists `h` >> simp[]
QED

Theorem mm_local_indexed_bulk_source_survival[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < r /\ r < LENGTH is /\ r <= N /\
  mm_local_history is H N /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  read_memory (w2n src) (w2n len) (H r) =
    read_memory (w2n src) (w2n len) (H (SUC j))
Proof
  strip_tac >>
  qabbrev_tac `c = <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
                    cg_inst_ids := [(EL j is).inst_id]|>` >>
  qabbrev_tac `cuts = \q. FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
                    empty_scan_state (TAKE q is)` >>
  `!q. SUC j <= q /\ q < r ==>
    ?h. MEM h (cuts q).ss_copies /\ mm_local_copy_ancestor c h /\
        ~MEM h (scan_inst (dfg_build_function fn0) Mem2Mem (cuts q) (EL q is)).ss_flushed` by
    (rpt strip_tac >>
     `cuts q = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
                  empty_scan_state (TAKE q is)` by simp[Abbr `cuts`] >>
     `c = <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
            cg_inst_ids := [(EL j is).inst_id]|>` by simp[Abbr `c`] >>
     drule_all mm_local_indexed_bulk_trajectory >> simp[]) >>
  `SUC j <= r` by decide_tac >>
  drule_all mm_local_ancestral_interval_read >> simp[Abbr `c`]
QED

Definition mm_local_write_footprint_def:
  mm_local_write_footprint inst =
    if inst.inst_opcode = MCOPY then
      (case inst.inst_operands of
         [Lit dst; Lit src; Lit len] => SOME (w2n dst,w2n len)
       | _ => NONE)
    else if inst.inst_opcode = MSTORE then
      (case inst.inst_operands of
         [Lit dst; value] => SOME (w2n dst,32)
       | _ => NONE)
    else NONE
End

Theorem mm_local_write_footprint_copy[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [Lit dst; Lit src; Lit len] ==>
  mm_local_write_footprint inst = SOME (w2n dst,w2n len)
Proof
  simp[mm_local_write_footprint_def]
QED

Theorem mm_local_write_footprint_store[local]:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [Lit dst; value] ==>
  mm_local_write_footprint inst = SOME (w2n dst,32)
Proof
  simp[mm_local_write_footprint_def]
QED

Theorem mm_local_write_footprint_nonwrite[local]:
  inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> MSTORE ==>
  mm_local_write_footprint inst = NONE
Proof
  simp[mm_local_write_footprint_def]
QED

Theorem mm_local_write_capture_footprint[local]:
  mm_local_write_capture is H n j = SOME (d,bs) /\
  mm_local_write_footprint (EL j is) = SOME (a,l) ==>
  d = a /\ LENGTH bs = l
Proof
  simp[mm_local_write_capture_def, mm_local_write_footprint_def] >>
  rpt IF_CASES_TAC >> gvs[AllCaseEqs(), venomStateTheory.eval_operand_def,
    venomStateTheory.read_memory_def] >>
  strip_tac >> gvs[venomStateTheory.eval_operand_def, venomStateTheory.read_memory_def]
QED

Theorem mm_local_group_coverage_birth_extra:
  j < n /\ j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  g.cg_inst_ids = (EL j is).inst_id :: extra /\
  cap j = SOME (g.cg_dst,bs) /\ LENGTH bs = g.cg_length /\
  (!p d cs. p < n /\ p < LENGTH is /\ MEM (EL p is).inst_id extra ==>
     cap p <> SOME (d,cs)) ==>
  mm_local_group_coverage is n cap g
Proof
  simp[mm_local_group_coverage_def] >> strip_tac >> gen_tac >> eq_tac
  >- (strip_tac >> qexistsl [`j`,`g.cg_dst`,`bs`] >> simp[]) >>
  strip_tac >>
  `j' = j` by
    (gvs[] >> metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]) >>
  gvs[]
QED

Theorem mm_local_hazards_add_coverage[local]:
  mm_local_scan_every (mm_local_group_coverage is n cap) ss /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  mm_local_group_coverage is n cap c ==>
  mm_local_scan_every (mm_local_group_coverage is n cap)
    ((flush_hazards mode ss c) with ss_copies :=
      add_copy (flush_hazards mode ss c).ss_copies c)
Proof
  strip_tac >> drule mm_local_hazards_every >>
  disch_then (qspecl_then [`mode`,`c`] assume_tac) >>
  gvs[mm_local_scan_every_def] >> irule mm_local_add_copy_coverage >>
  simp[mm_local_hazards_order]
QED

Theorem mm_local_store_coverage[local]:
  mm_local_scan_every (mm_local_group_coverage is n cap) ss /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  (!dst v src. inst.inst_operands = [Lit dst; Var v] /\
    FLOOKUP ss.ss_loads v = SOME src ==>
    mm_local_group_coverage is n cap
      <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
        cg_inst_ids := inst.inst_id ::
          (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id])|>) ==>
  mm_local_scan_every (mm_local_group_coverage is n cap) (scan_store dfg Mem2Mem ss inst)
Proof
  strip_tac >> simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[mm_local_barrier_every] >>
  irule mm_local_hazards_add_coverage >>
  simp[invalidate_loads_def, mm_local_invalidate_every] >>
  gvs[oneline operand_lit_val_def, oneline operand_var_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem mm_local_bulk_coverage[local]:
  mm_local_scan_every (mm_local_group_coverage is n cap) ss /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  (!dst src len. inst.inst_operands = [Lit dst; Lit src; Lit len] ==>
    mm_local_group_coverage is n cap
      <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
        cg_inst_ids := [inst.inst_id]|>) ==>
  mm_local_scan_every (mm_local_group_coverage is n cap) (scan_bulk_copy Mem2Mem ss inst)
Proof
  strip_tac >> simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[mm_local_barrier_every] >>
  irule mm_local_hazards_add_coverage >>
  simp[invalidate_loads_def, mm_local_invalidate_every] >>
  gvs[oneline operand_lit_val_def, oneline operand_var_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem mm_local_inst_coverage[local]:
  mm_local_scan_every (mm_local_group_coverage is n cap) ss /\
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  ((EL j is).inst_opcode = MSTORE ==>
    !dst v src. (EL j is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP ss.ss_loads v = SOME src ==>
      mm_local_group_coverage is n cap
        <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
          cg_inst_ids := (EL j is).inst_id ::
            (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id])|>) /\
  ((EL j is).inst_opcode = MCOPY ==>
    !dst src len. (EL j is).inst_operands = [Lit dst; Lit src; Lit len] ==>
      mm_local_group_coverage is n cap
        <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
          cg_inst_ids := [(EL j is).inst_id]|>) ==>
  mm_local_scan_every (mm_local_group_coverage is n cap)
    (scan_inst dfg Mem2Mem ss (EL j is))
Proof
  strip_tac >> simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  IF_CASES_TAC >- (irule mm_local_load_every >> simp[]) >>
  IF_CASES_TAC >- (irule mm_local_store_coverage >> metis_tac[]) >>
  IF_CASES_TAC >- (irule mm_local_bulk_coverage >> metis_tac[]) >>
  rpt IF_CASES_TAC >> simp[mm_local_barrier_every]
QED

Theorem mm_local_write_footprint_opcode:
  mm_local_write_footprint inst = SOME (d,l) ==>
  inst.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  simp[mm_local_write_footprint_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem mm_local_footprint_def_excluded[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ p < LENGTH is /\
  dfg_get_def (dfg_build_function fn0) v = SOME li /\
  (EL p is).inst_id = li.inst_id ==>
  mm_local_write_footprint (EL p is) = NONE
Proof
  strip_tac >> Cases_on `mm_local_write_footprint (EL p is)` >> simp[] >>
  PairCases_on `x` >>
  drule mm_local_write_footprint_opcode >> strip_tac >>
  `MEM (EL p is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  drule_all mm_local_prefix_write_not_def >> simp[]
QED

Theorem mm_local_footprint_store_coverage[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\ (EL j is).inst_operands = [Lit dst; Var v] /\
  cap = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                    (mm_local_write_footprint (EL p is))) ==>
  mm_local_group_coverage is (LENGTH is) cap
    <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
      cg_inst_ids := (EL j is).inst_id ::
        (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id])|>
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  irule mm_local_group_coverage_birth_extra >> (conj_tac >- simp[]) >>
  qexistsl [`REPLICATE 32 (0w:word8)`,
    `case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id]`, `j`] >>
  simp[] >> reverse conj_tac
  >- gvs[mm_local_write_footprint_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `dfg_get_def (dfg_build_function fn0) v` >> gvs[] >>
  `mm_local_write_footprint (EL p bb.bb_instructions) = NONE` by
    metis_tac[mm_local_footprint_def_excluded] >> simp[]
QED

Theorem mm_local_footprint_bulk_coverage[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) is) /\ j < LENGTH is /\
  (EL j is).inst_opcode = MCOPY /\ (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  cap = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                    (mm_local_write_footprint (EL p is))) ==>
  mm_local_group_coverage is (LENGTH is) cap
    <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
      cg_inst_ids := [(EL j is).inst_id]|>
Proof
  strip_tac >> irule mm_local_group_coverage_birth >> (conj_tac >- simp[]) >>
  qexistsl [`REPLICATE (w2n len) (0w:word8)`,`j`] >>
  simp[mm_local_write_footprint_def]
QED

Theorem mm_local_scan_footprint_coverage[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  cap = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                    (mm_local_write_footprint (EL p is))) ==>
  !t. t <= LENGTH is ==>
    mm_local_scan_every (mm_local_group_coverage is (LENGTH is) cap)
      (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE t is))
Proof
  strip_tac >> Induct >- simp[mm_local_scan_every_def, empty_scan_state_def] >>
  strip_tac >> `t < LENGTH is /\ t <= LENGTH is` by decide_tac >>
  simp[rich_listTheory.TAKE_SUC, FOLDL_APPEND] >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst)
     (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE t is)).ss_copies` by
    (irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  irule mm_local_inst_coverage >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule (Q.INST [`j` |-> `t`, `is` |-> `bb.bb_instructions`]
        mm_local_footprint_store_coverage) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  gvs[mm_local_footprint_bulk_coverage]
QED

Definition mm_local_group_endpoint_def:
  mm_local_group_endpoint is n cap g <=>
    (!j d bs. j < n /\ j < LENGTH is /\
      MEM (EL j is).inst_id g.cg_inst_ids /\ cap j = SOME (d,bs) ==>
      d + LENGTH bs <= g.cg_dst + g.cg_length) /\
    (?j d bs. j < n /\ j < LENGTH is /\
      MEM (EL j is).inst_id g.cg_inst_ids /\ cap j = SOME (d,bs) /\
      d + LENGTH bs = g.cg_dst + g.cg_length)
End

Theorem mm_local_group_endpoint_birth_extra:
  j < n /\ j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  g.cg_inst_ids = (EL j is).inst_id :: extra /\
  cap j = SOME (g.cg_dst,bs) /\ LENGTH bs = g.cg_length /\
  (!p d cs. p < n /\ p < LENGTH is /\ MEM (EL p is).inst_id extra ==>
     cap p <> SOME (d,cs)) ==>
  mm_local_group_endpoint is n cap g
Proof
  strip_tac >> simp[mm_local_group_endpoint_def] >> conj_tac
  >- (rpt strip_tac >>
      `j' = j` by
        (gvs[] >> metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]) >>
      gvs[]) >>
  qexistsl [`j`,`g.cg_dst`,`bs`] >> simp[]
QED

Theorem mm_local_group_endpoint_merge:
  mm_local_group_endpoint is n cap a /\ mm_local_group_endpoint is n cap b ==>
  mm_local_group_endpoint is n cap (copy_merge a b)
Proof
  strip_tac >>
  `(copy_merge a b).cg_dst + (copy_merge a b).cg_length =
     MAX (a.cg_dst + a.cg_length) (b.cg_dst + b.cg_length)` by
    (simp[copy_merge_def, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  gvs[mm_local_group_endpoint_def] >>
  simp[copy_merge_def, MEM_APPEND] >>
  Cases_on `a.cg_dst + a.cg_length <= b.cg_dst + b.cg_length` >>
  simp[arithmeticTheory.MAX_DEF] >> metis_tac[]
QED

Theorem mm_local_zero_prefix_endpoint[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) is) ==>
  EVERY (mm_local_group_endpoint is n (mm_local_zero_capture dfg is n))
    ((FOLDL (scan_inst_memzero dfg) empty_memzero_state (TAKE n is)).mz_flushed ++
     (FOLDL (scan_inst_memzero dfg) empty_memzero_state (TAKE n is)).mz_copies)
Proof
  strip_tac >> irule (cj 2 mm_local_zero_fold_certificate) >>
  simp[empty_memzero_state_def] >> conj_tac
  >- (rpt strip_tac >> irule mm_local_add_every >>
      metis_tac[mm_local_group_endpoint_merge]) >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `?j. j < n /\ j < LENGTH is /\ i = EL j is` by
    (fs[MEM_EL, LENGTH_TAKE_EQ] >>
     rename1 `j < if n <= LENGTH is then n else LENGTH is` >>
     `j < n /\ j < LENGTH is` by (Cases_on `n <= LENGTH is` >> gvs[] >> decide_tac) >>
     qexists `j` >> simp[EL_TAKE]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule mm_local_group_endpoint_birth_extra >> (conj_tac >- simp[]) >>
      qexistsl [`REPLICATE 32 0w`,`[]`,`j`] >>
      simp[copy_memzero_def] >>
      irule mm_local_zero_capture_store >> gvs[is_zero_store_def]) >>
  rpt gen_tac >> strip_tac >>
  irule mm_local_group_endpoint_birth_extra >>
  (conj_tac >- simp[]) >>
  qexistsl [`REPLICATE (w2n len) 0w`,`[]`,`j`] >>
  simp[copy_memzero_def] >>
  irule mm_local_zero_capture_calldata >> metis_tac[]
QED

Theorem mm_local_zero_rep_index_eq[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  j < LENGTH bb.bb_instructions /\ MEM g gs /\
  MEM (EL j bb.bb_instructions).inst_id g.cg_inst_ids /\
  r < LENGTH bb.bb_instructions /\
  rep_of_group bb.bb_instructions g = SOME ((EL r bb.bb_instructions).inst_id,g) ==>
  mm_local_rep_index bb.bb_instructions gs j = r
Proof
  strip_tac >>
  `ALL_DISTINCT (FILTER (\x:num. T) (mm_local_group_ids gs))` by
    gvs[mm_local_zero_scan_unique] >>
  simp[mm_local_rep_index_def] >> SELECT_ELIM_TAC >>
  (conj_tac >- metis_tac[]) >> rpt strip_tac >>
  `g' = g` by
    (irule mm_local_projected_owner >> qexistsl [`gs`,`(EL j bb.bb_instructions).inst_id`,`\x:num. T`] >> simp[]) >>
  gvs[] >> metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]
QED

Theorem mm_local_zero_member_capture:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM g (scan_block_memzero dfg bb).mz_flushed /\
  j < n /\ j < LENGTH bb.bb_instructions /\
  MEM (EL j bb.bb_instructions).inst_id g.cg_inst_ids ==>
  (EL j bb.bb_instructions).inst_opcode IN {MSTORE; CALLDATACOPY} /\
  ?d bs. mm_local_zero_capture dfg bb.bb_instructions n j = SOME (d,bs)
Proof
  strip_tac >>
  SUBGOAL_THEN
    ``is_zero_store (EL j bb.bb_instructions) \/
      is_calldatasize_copy dfg (EL j bb.bb_instructions)`` assume_tac
  >- (drule_all mm_local_memzero_group_roles >> strip_tac >>
      `i = EL j bb.bb_instructions` by
        metis_tac[mmWfProofsTheory.all_distinct_map_inv, EL_MEM] >> gvs[]) >>
  conj_tac >- gvs[is_zero_store_def, is_calldatasize_copy_def] >>
  simp[mm_local_zero_capture_def] >>
  Cases_on `is_zero_store (EL j bb.bb_instructions)`
  >- (fs[is_zero_store_def] >> rpt (CASE_TAC >> gvs[operand_lit_val_def])) >>
  fs[is_calldatasize_copy_def] >>
  rpt (CASE_TAC >> gvs[operand_lit_val_def, operand_var_def]) >>
  gvs[oneline operand_lit_val_def, oneline operand_var_def, AllCaseEqs()]
QED

Theorem mm_local_zero_due_indices[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r) ==>
  !j. MEM j due <=> j < r /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM (EL j is).inst_id g.cg_inst_ids
Proof
  strip_tac >>
  `ALL_DISTINCT (FILTER (\x:num. T) (mm_local_group_ids gs))` by
    gvs[mm_local_zero_scan_unique] >>
  gen_tac >>
  qpat_x_assum `due = _` SUBST1_TAC >>
  pure_rewrite_tac[MEM_FILTER, mm_local_pending_indices_mem] >> eq_tac
  >- (strip_tac >>
      rename1 `rep_of_group is g' = SOME ((EL rr is).inst_id,g')` >>
      `j < LENGTH is` by decide_tac >>
      `mm_local_rep_index is gs j = rr` by
        (qpat_assum `is = _` SUBST1_TAC >>
         irule mm_local_zero_rep_index_eq >> metis_tac[]) >>
      `rr = r` by metis_tac[] >>
      `MEM (EL r is).inst_id g'.cg_inst_ids /\
       MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
      `g' = g` by
        (irule mm_local_projected_owner >>
         qexistsl [`gs`,`(EL r is).inst_id`,`\x:num. T`] >> simp[]) >>
      gvs[]) >>
  strip_tac >>
  `j < LENGTH is` by decide_tac >>
  conj_tac
  >- (qpat_assum `is = _` SUBST1_TAC >> BETA_TAC >>
      irule mm_local_zero_rep_index_eq >> metis_tac[]) >>
  simp[] >> qexistsl [`g`,`r`] >> gvs[]
QED

Theorem mm_local_zero_representative_pending_suc[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  mm_local_pending_indices is gs (SUC r) =
    FILTER (\j. mm_local_rep_index is gs j <> r) (mm_local_pending_indices is gs r)
Proof
  strip_tac >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `!j h q. j < LENGTH is /\ MEM h gs /\ MEM (EL j is).inst_id h.cg_inst_ids /\
      q < LENGTH is /\ rep_of_group is h = SOME ((EL q is).inst_id,h) ==>
      mm_local_rep_index is gs j = q` by
    (rpt strip_tac >> qpat_assum `is = _` SUBST1_TAC >>
     irule mm_local_zero_rep_index_eq >> metis_tac[]) >>
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
      `mm_local_rep_index is gs j = rr` by metis_tac[] >>
      `mm_local_rep_index is gs j <> r` by decide_tac >>
      simp[] >> qexistsl [`h`,`rr`] >> gvs[]) >>
  strip_tac >>
  rename1 `rep_of_group is h = SOME ((EL rr is).inst_id,h)` >>
  `mm_local_rep_index is gs j = rr` by metis_tac[] >>
  `SUC r <= rr` by decide_tac >>
  simp[] >> qexistsl [`h`,`rr`] >> gvs[]
QED

Theorem mm_local_zero_due_members[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r) ==>
  (!j. MEM j (due ++ [r]) <=>
    j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids) /\
  (!j. MEM j (due ++ [r]) ==>
    ?d bs. mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs))
Proof
  strip_tac >>
  `!j. MEM j due <=> j < r /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM (EL j is).inst_id g.cg_inst_ids` by
    (irule mm_local_zero_due_indices >> metis_tac[]) >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `!j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids ==> j <= r` by
    metis_tac[mm_local_rep_position_max] >>
  `!j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids ==>
    (EL j is).inst_opcode IN {MSTORE; CALLDATACOPY} /\
    ?d bs. mm_local_zero_capture dfg is (SUC r) j = SOME (d,bs)` by
    (gen_tac >> strip_tac >> qpat_assum `is = _` SUBST1_TAC >>
     irule mm_local_zero_member_capture >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_IFF_LESS_SUC]) >>
  conj_asm1_tac
  >- (gen_tac >> simp[MEM_APPEND] >> eq_tac
      >- (strip_tac >> gvs[] >> res_tac >> decide_tac) >>
      strip_tac >> Cases_on `j = r` >> simp[] >>
      `j < r` by metis_tac[arithmeticTheory.LESS_OR_EQ] >>
      first_x_assum (qspec_then `j` mp_tac) >>
      simp[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem mm_local_zero_block_endpoint[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  EVERY (mm_local_group_endpoint bb.bb_instructions (LENGTH bb.bb_instructions)
    (mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions)))
    (scan_block_memzero dfg bb).mz_flushed
Proof
  strip_tac >>
  mp_tac (Q.INST [`is` |-> `bb.bb_instructions`, `dfg` |-> `dfg`,
    `n` |-> `LENGTH bb.bb_instructions`] mm_local_zero_prefix_endpoint) >>
  simp[scan_block_memzero_def, memzero_barrier_def]
QED

Theorem mm_local_zero_representative_endpoint:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM g (scan_block_memzero dfg bb).mz_flushed /\
  r < LENGTH bb.bb_instructions /\
  rep_of_group bb.bb_instructions g = SOME ((EL r bb.bb_instructions).inst_id,g) ==>
  mm_local_group_endpoint bb.bb_instructions (SUC r)
    (mm_local_zero_capture dfg bb.bb_instructions (SUC r)) g
Proof
  strip_tac >>
  `mm_local_group_endpoint bb.bb_instructions (LENGTH bb.bb_instructions)
    (mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions)) g` by
    (drule mm_local_zero_block_endpoint >> simp[EVERY_MEM]) >>
  `!j. j < LENGTH bb.bb_instructions /\
      MEM (EL j bb.bb_instructions).inst_id g.cg_inst_ids ==> j < SUC r` by
    (rpt strip_tac >>
     `j <= r` by metis_tac[mm_local_rep_position_max] >> decide_tac) >>
  `!j. j < LENGTH bb.bb_instructions /\
      MEM (EL j bb.bb_instructions).inst_id g.cg_inst_ids ==>
      mm_local_zero_capture dfg bb.bb_instructions (LENGTH bb.bb_instructions) j =
      mm_local_zero_capture dfg bb.bb_instructions (SUC r) j` by
    (rpt strip_tac >> irule mm_local_zero_capture_past >> simp[]) >>
  fs[mm_local_group_endpoint_def] >> metis_tac[]
QED

Theorem mm_local_zero_due_records[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r) /\
  cap = mm_local_zero_capture dfg is (SUC r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  !d bs. MEM (d,bs) ws <=>
    ?j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\ cap j = SOME (d,bs)
Proof
  strip_tac >>
  `(!j. MEM j (due ++ [r]) <=>
    j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids) /\
   (!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs))` by
    (qpat_assum `cap = _` SUBST1_TAC >>
     irule mm_local_zero_due_members >> metis_tac[]) >>
  rpt gen_tac >> eq_tac
  >- (strip_tac >>
      `?j. MEM j (due ++ [r]) /\ (d,bs) = (THE o cap) j` by
        (gvs[MEM_MAP] >> metis_tac[]) >>
      `?a cs. cap j = SOME (a,cs)` by metis_tac[] >>
      qexists `j` >> gvs[] >> metis_tac[]) >>
  strip_tac >> qpat_x_assum `ws = _` SUBST1_TAC >>
  simp[MEM_MAP] >> qexists `j` >> gvs[]
QED

Theorem mm_local_zero_due_geometry[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r) /\
  cap = mm_local_zero_capture dfg is (SUC r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  (!d bs. MEM (d,bs) ws ==> g.cg_dst <= d /\
    d + LENGTH bs <= g.cg_dst + g.cg_length /\ bs = REPLICATE (LENGTH bs) 0w) /\
  (!a. (g.cg_dst <= a /\ a < g.cg_dst + g.cg_length) <=>
    ?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs) /\
  MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws) = g.cg_dst + g.cg_length
Proof
  strip_tac >>
  `!d bs. MEM (d,bs) ws <=> ?j. j < LENGTH is /\
    MEM (EL j is).inst_id g.cg_inst_ids /\ cap j = SOME (d,bs)` by
    (irule mm_local_zero_due_records >> metis_tac[]) >>
  `mm_local_group_captures is cap (\a. 0w) g /\
   mm_local_group_coverage is (SUC r) cap g` by
    (map_every (fn q => qpat_assum q SUBST1_TAC) [`cap = _`, `is = _`] >>
     irule mm_local_zero_representative_certificate >> metis_tac[]) >>
  `mm_local_group_endpoint is (SUC r) cap g` by
    (map_every (fn q => qpat_assum q SUBST1_TAC) [`cap = _`, `is = _`] >>
     irule mm_local_zero_representative_endpoint >> metis_tac[]) >>
  `!p. p < LENGTH is /\ MEM (EL p is).inst_id g.cg_inst_ids ==> p < SUC r` by
    (rpt strip_tac >> `p <= r` by metis_tac[mm_local_rep_position_max] >> decide_tac) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`is = _`, `gs = _`, `cap = _`, `due = _`, `ws = _`] >>
  fs[mm_local_group_captures_def, mm_local_group_coverage_def,
    mm_local_group_endpoint_def, mm_local_bytes_def, REPLICATE_GENLIST,
    combinTheory.K_DEF] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  irule venomWriteReplayPropsTheory.write_log_endpoint >> metis_tac[]
QED

Theorem mm_local_zero_capture_payload[local]:
  mm_local_zero_capture dfg is n j = SOME (d,bs) ==>
  bs = REPLICATE (LENGTH bs) 0w
Proof
  strip_tac >> drule mm_local_zero_capture_cases >> strip_tac >> gvs[]
QED

Theorem mm_local_zero_capture_compatible[local]:
  mm_local_zero_capture dfg is n j = SOME (d,bs) ==>
  mm_local_write_compatible d bs a (REPLICATE l 0w)
Proof
  strip_tac >> drule mm_local_zero_capture_payload >> strip_tac >>
  simp[mm_local_write_compatible_def] >> rpt strip_tac >>
  `x - d < LENGTH bs /\ x - a < l` by (gvs[] >> decide_tac) >>
  metis_tac[rich_listTheory.EL_REPLICATE]
QED

Theorem mm_local_zero_due_realize[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r) /\
  cap = mm_local_zero_capture dfg is (SUC r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws =
    write_memory_with_expansion g.cg_dst (REPLICATE g.cg_length 0w) v
Proof
  strip_tac >> drule_all mm_local_zero_due_geometry >> strip_tac >>
  `REPLICATE g.cg_length (0w:word8) = mm_local_bytes (\a. 0w) 0 g.cg_length` by
    simp[mm_local_bytes_def, REPLICATE_GENLIST, combinTheory.K_DEF] >>
  pop_assum SUBST1_TAC >> irule mm_local_write_log_realize >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`is = _`, `gs = _`, `cap = _`, `due = _`, `ws = _`] >>
  fs[mm_local_bytes_def, REPLICATE_GENLIST, combinTheory.K_DEF] >> metis_tac[]
QED

Theorem mm_local_zero_representative_discharge:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  gs = (scan_block_memzero dfg bb).mz_flushed /\
  is = bb.bb_instructions /\ r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_zero_capture dfg is (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  cap r = SOME (d,bs) /\ mm_local_pending cap js s t /\
  s'.vs_memory = (write_memory_with_expansion d bs s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (REPLICATE g.cg_length 0w) t).vs_memory ==>
  mm_local_pending cap (mm_local_pending_indices is gs (SUC r)) s' t'
Proof
  strip_tac >>
  `!j a cs. cap j = SOME (a,cs) ==> cs = REPLICATE (LENGTH cs) 0w` by
    metis_tac[mm_local_zero_capture_payload] >>
  `!j k a cs b ds. cap j = SOME (a,cs) /\ cap k = SOME (b,ds) ==>
      mm_local_write_compatible a cs b ds` by
    (rpt strip_tac >> `ds = REPLICATE (LENGTH ds) 0w` by metis_tac[] >>
     pop_assum SUBST1_TAC >> metis_tac[mm_local_zero_capture_compatible]) >>
  `EVERY (\j. IS_SOME (cap j)) js` by
    (gvs[mm_local_pending_def] >> metis_tac[venomWriteReplayPropsTheory.capture_log_canonical]) >>
  `!P. LIST_REL (\j w. cap j = SOME w) (FILTER P js)
      (MAP (THE o cap) (FILTER P js))` by
    (gen_tac >> simp[LIST_REL_MAP2] >> irule EVERY2_refl >>
     simp[EVERY_MEM, MEM_FILTER] >> qx_gen_tac `j` >> strip_tac >>
     `IS_SOME (cap j)` by
       (qpat_x_assum `EVERY _ js` mp_tac >>
        gvs[EVERY_MEM] >> metis_tac[]) >>
     Cases_on `cap j` >> gvs[]) >>
  `mm_local_pending_indices is gs (SUC r) =
      FILTER (\j. mm_local_rep_index is gs j <> r) js` by
    metis_tac[mm_local_zero_representative_pending_suc] >>
  pop_assum SUBST1_TAC >>
  irule (BETA_RULE (Q.INST [`P` |-> `\j. mm_local_rep_index is gs j = r`]
    (INST_TYPE [alpha |-> ``:num``] mm_local_pending_compatible_discharge_filter))) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  qexistsl [`d`,`g.cg_dst`,`REPLICATE g.cg_length 0w`,
    `MAP (THE o cap) (FILTER (\j. mm_local_rep_index is gs j = r) js)`,
    `bs`,
    `MAP (THE o cap) (FILTER (\j. mm_local_rep_index is gs j <> r) js)`,
    `s`,`t`] >>
  simp[] >> conj_tac
  >- (gen_tac >>
      `FOLDL (\st (a,cs). write_memory_with_expansion a cs st) v
        (MAP (THE o cap)
          (FILTER (\j. mm_local_rep_index is gs j = r) js ++ [r])) =
        write_memory_with_expansion g.cg_dst (REPLICATE g.cg_length 0w) v` by
        (irule mm_local_zero_due_realize >> simp[] >>
         qexistsl [`bb`,`dfg`,`r`] >> gvs[]) >>
      gvs[MAP_APPEND, FOLDL_APPEND]) >>
  simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `j` >> strip_tac >>
  `IS_SOME (cap j)` by
    (qpat_x_assum `EVERY _ js` mp_tac >>
     gvs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  Cases_on `cap j` >> gvs[] >> PairCases_on `x` >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_footprint_store_endpoint[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\ (EL j is).inst_operands = [Lit dst; Var v] /\
  cap = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                    (mm_local_write_footprint (EL p is))) ==>
  mm_local_group_endpoint is (LENGTH is) cap
    <|cg_dst := w2n dst; cg_src := src; cg_length := 32;
      cg_inst_ids := (EL j is).inst_id ::
        (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id])|>
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  irule mm_local_group_endpoint_birth_extra >> (conj_tac >- simp[]) >>
  qexistsl [`REPLICATE 32 (0w:word8)`,
    `case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id]`, `j`] >>
  simp[] >> reverse conj_tac
  >- gvs[mm_local_write_footprint_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `dfg_get_def (dfg_build_function fn0) v` >> gvs[] >>
  `mm_local_write_footprint (EL p bb.bb_instructions) = NONE` by
    metis_tac[mm_local_footprint_def_excluded] >> simp[]
QED

Theorem mm_local_footprint_bulk_endpoint[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) is) /\ j < LENGTH is /\
  (EL j is).inst_opcode = MCOPY /\ (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  cap = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                    (mm_local_write_footprint (EL p is))) ==>
  mm_local_group_endpoint is (LENGTH is) cap
    <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
      cg_inst_ids := [(EL j is).inst_id]|>
Proof
  strip_tac >> irule mm_local_group_endpoint_birth_extra >> (conj_tac >- simp[]) >>
  qexistsl [`REPLICATE (w2n len) (0w:word8)`,`[]`,`j`] >>
  simp[mm_local_write_footprint_def]
QED

Theorem mm_local_scan_footprint_endpoint[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  cap = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                    (mm_local_write_footprint (EL p is))) ==>
  !t. t <= LENGTH is ==>
    mm_local_scan_every (mm_local_group_endpoint is (LENGTH is) cap)
      (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE t is))
Proof
  strip_tac >> Induct >- simp[mm_local_scan_every_def, empty_scan_state_def] >>
  strip_tac >> `t < LENGTH is /\ t <= LENGTH is` by decide_tac >>
  simp[rich_listTheory.TAKE_SUC, FOLDL_APPEND] >>
  irule (REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_inst_birth_every)) >>
  conj_tac >- metis_tac[mm_local_group_endpoint_merge] >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule (Q.INST [`j` |-> `t`, `is` |-> `bb.bb_instructions`]
        mm_local_footprint_store_endpoint) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  gvs[mm_local_footprint_bulk_endpoint]
QED

Theorem mm_local_final_footprint_extent:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  cap = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                    (mm_local_write_footprint (EL p is))) /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed ==>
  mm_local_group_coverage is (LENGTH is) cap g /\
  mm_local_group_endpoint is (LENGTH is) cap g
Proof
  strip_tac >>
  `mm_local_scan_every (mm_local_group_coverage is (LENGTH is) cap)
    (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state is)` by
    (qsuff_tac `!t. t <= LENGTH is ==>
       mm_local_scan_every (mm_local_group_coverage is (LENGTH is) cap)
         (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE t is))`
     >- (disch_then (qspec_then `LENGTH is` mp_tac) >> simp[]) >>
     metis_tac[mm_local_scan_footprint_coverage]) >>
  `mm_local_scan_every (mm_local_group_endpoint is (LENGTH is) cap)
    (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state is)` by
    (qsuff_tac `!t. t <= LENGTH is ==>
       mm_local_scan_every (mm_local_group_endpoint is (LENGTH is) cap)
         (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE t is))`
     >- (disch_then (qspec_then `LENGTH is` mp_tac) >> simp[]) >>
     metis_tac[mm_local_scan_footprint_endpoint]) >>
  gvs[scan_block_def, hard_barrier_def, mm_local_scan_every_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem mm_local_canonical_due_footprint_indices:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) ==>
  !j. MEM j (due ++ [r]) <=>
    j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    ?d l. mm_local_write_footprint (EL j is) = SOME (d,l)
Proof
  strip_tac >>
  `due = FILTER (\j. j < r /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM (EL j is).inst_id g.cg_inst_ids) (COUNT_LIST r)` by
    metis_tac[mm_local_canonical_due_group] >>
  qpat_x_assum `due = FILTER (\j. mm_local_rep_index _ _ j = _) _` kall_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  drule_all mm_local_canonical_rep_write >> strip_tac >>
  qx_gen_tac `j` >> eq_tac
  >- (strip_tac >>
      `j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
        (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
        (gvs[MEM_APPEND, MEM_FILTER, MEM_COUNT_LIST] >> decide_tac) >>
      `MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
      drule_all (REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >> strip_tac >>
      gvs[mm_local_write_footprint_def]) >>
  strip_tac >>
  `j <= r` by metis_tac[mm_local_rep_position_max] >>
  drule mm_local_write_footprint_opcode >> strip_tac >>
  simp[MEM_APPEND, MEM_FILTER, MEM_COUNT_LIST] >> gvs[]
QED

Theorem mm_local_canonical_due_footprint_records[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) ==>
  !j. MEM j (due ++ [r]) ==> ?d bs.
    cap j = SOME (d,bs) /\ mm_local_write_footprint (EL j is) = SOME (d,LENGTH bs)
Proof
  strip_tac >>
  `LIST_REL (\j w. cap j = SOME w) (due ++ [r]) (MAP (THE o cap) (due ++ [r]))` by
    metis_tac[mm_local_canonical_due_records] >>
  `!j. MEM j (due ++ [r]) <=> j < LENGTH is /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    ?d l. mm_local_write_footprint (EL j is) = SOME (d,l)` by
    metis_tac[mm_local_canonical_due_footprint_indices] >>
  gen_tac >> strip_tac >> drule_all LIST_REL_MEM_IMP >> strip_tac >>
  PairCases_on `y` >>
  `?d l. mm_local_write_footprint (EL j is) = SOME (d,l)` by metis_tac[] >>
  `y0 = d /\ LENGTH y1 = l` by metis_tac[mm_local_write_capture_footprint] >>
  qexistsl [`y0`,`y1`] >> gvs[]
QED

Theorem mm_local_canonical_due_log_footprint_captures[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  (!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs)) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  !d l. (?bs. MEM (d,bs) ws /\ LENGTH bs = l) <=>
    ?j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      mm_local_write_footprint (EL j is) = SOME (d,l)
Proof
  strip_tac >>
  `!j. MEM j (due ++ [r]) <=> j < LENGTH is /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    ?d l. mm_local_write_footprint (EL j is) = SOME (d,l)` by
    metis_tac[mm_local_canonical_due_footprint_indices] >>
  `!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs) /\
      mm_local_write_footprint (EL j is) = SOME (d,LENGTH bs)` by
    (rpt strip_tac >>
     `?d bs. cap j = SOME (d,bs)` by metis_tac[] >>
     `?a l. mm_local_write_footprint (EL j is) = SOME (a,l)` by metis_tac[] >>
     `d = a /\ LENGTH bs = l` by metis_tac[mm_local_write_capture_footprint] >>
     metis_tac[]) >>
  rpt gen_tac >> eq_tac
  >- (strip_tac >>
      `?j. MEM j (due ++ [r]) /\ (d,bs) = (THE o cap) j` by
        (gvs[MEM_MAP] >> metis_tac[]) >>
      `?a cs. cap j = SOME (a,cs) /\
        mm_local_write_footprint (EL j is) = SOME (a,LENGTH cs)` by metis_tac[] >>
      qexists `j` >> gvs[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  strip_tac >> `MEM j (due ++ [r])` by metis_tac[] >>
  `?a cs. cap j = SOME (a,cs) /\
    mm_local_write_footprint (EL j is) = SOME (a,LENGTH cs)` by metis_tac[] >>
  qexists `cs` >> reverse conj_tac >- gvs[] >>
  qpat_x_assum `ws = _` SUBST1_TAC >> pure_rewrite_tac[MEM_MAP] >>
  qexists `j` >> simp[] >> gvs[]
QED

Theorem mm_local_canonical_due_log_footprint[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  !d l. (?bs. MEM (d,bs) ws /\ LENGTH bs = l) <=>
    ?j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      mm_local_write_footprint (EL j is) = SOME (d,l)
Proof
  strip_tac >>
  `!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs)` by
    metis_tac[mm_local_canonical_due_footprint_records] >>
  mp_tac (SPEC_ALL mm_local_canonical_due_log_footprint_captures) >> simp[]
QED

Theorem mm_local_canonical_due_log_coverage_endpoint_captures:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  (!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs)) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  (!a. (g.cg_dst <= a /\ a < g.cg_dst + g.cg_length) <=>
    ?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs) /\
  (!d bs. MEM (d,bs) ws ==> d + LENGTH bs <= g.cg_dst + g.cg_length) /\
  MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws) = g.cg_dst + g.cg_length
Proof
  strip_tac >>
  `!d l. (?bs. MEM (d,bs) ws /\ LENGTH bs = l) <=>
    ?j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      mm_local_write_footprint (EL j is) = SOME (d,l)` by
    metis_tac[mm_local_canonical_due_log_footprint_captures] >>
  qabbrev_tac `fp = (\p. OPTION_MAP (\(d,l). (d,REPLICATE l (0w:word8)))
                      (mm_local_write_footprint (EL p is)))` >>
  `mm_local_group_coverage is (LENGTH is) fp g /\
   mm_local_group_endpoint is (LENGTH is) fp g` by
    (irule mm_local_final_footprint_extent >> simp[Abbr `fp`] >> metis_tac[]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`is = _`, `gs = _`, `cap = _`, `due = _`, `ws = _`] >>
  fs[mm_local_group_coverage_def, mm_local_group_endpoint_def,
     Abbr `fp`, pairTheory.EXISTS_PROD] >>
  fs[GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
  gvs[] >>
  conj_tac >- metis_tac[] >>
  conj_asm1_tac
  >- (qx_gen_tac `a` >> qx_gen_tac `cs` >> strip_tac >>
      `?j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
        mm_local_write_footprint (EL j is) = SOME (a,LENGTH cs)` by metis_tac[] >>
      qpat_x_assum `!p d bs. _ ==> _` (qspecl_then
        [`j`,`a`,`REPLICATE (LENGTH cs) (0w:word8)`] mp_tac) >> simp[] >> metis_tac[]) >>
  irule venomWriteReplayPropsTheory.write_log_endpoint >> simp[] >> metis_tac[]
QED


Theorem mm_local_canonical_due_log_coverage_endpoint[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  (!a. (g.cg_dst <= a /\ a < g.cg_dst + g.cg_length) <=>
    ?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs) /\
  (!d bs. MEM (d,bs) ws ==> d + LENGTH bs <= g.cg_dst + g.cg_length) /\
  MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws) = g.cg_dst + g.cg_length
Proof
  strip_tac >>
  `!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs)` by
    metis_tac[mm_local_canonical_due_footprint_records] >>
  mp_tac (SPEC_ALL mm_local_canonical_due_log_coverage_endpoint_captures) >> simp[] >>
  metis_tac[]
QED

Theorem mm_local_footprint_store_lower[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\ (EL j is).inst_operands = [Lit dst; Var v] ==>
  !p d l. p < LENGTH is /\
    MEM (EL p is).inst_id ((EL j is).inst_id ::
      (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id])) /\
    mm_local_write_footprint (EL p is) = SOME (d,l) ==> w2n dst <= d
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >> drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `(EL p is).inst_id = (EL j is).inst_id`
  >- (`p = j` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
      gvs[mm_local_write_footprint_def]) >>
  Cases_on `dfg_get_def (dfg_build_function fn0) v` >> gvs[] >>
  `mm_local_write_footprint (EL p bb.bb_instructions) = NONE` by
    metis_tac[mm_local_footprint_def_excluded] >> gvs[]
QED

Theorem mm_local_merge_adjacent_ordered_every[local]:
  (!a b. copy_can_merge a b /\ a.cg_dst <= b.cg_dst /\ P a /\ P b ==> P (copy_merge a b)) ==>
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\ EVERY P cs ==>
    EVERY P (merge_adjacent cs)
Proof
  strip_tac >> recInduct merge_adjacent_ind >> simp[merge_adjacent_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2`
  >- (gvs[] >> first_x_assum irule >>
      gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def, copy_merge_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[] >> first_x_assum irule >> gvs[sortingTheory.SORTED_DEF]
QED

Theorem mm_local_hazards_add_ordered_every[local]:
  (!a b. copy_can_merge a b /\ a.cg_dst <= b.cg_dst /\ P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\ SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\ P c ==>
  mm_local_scan_every P ((flush_hazards mode ss c) with ss_copies :=
    add_copy (flush_hazards mode ss c).ss_copies c)
Proof
  strip_tac >> drule mm_local_hazards_every >>
  disch_then (qspecl_then [`mode`,`c`] assume_tac) >>
  gvs[mm_local_scan_every_def] >> simp[add_copy_def] >>
  irule mm_local_merge_adjacent_ordered_every >>
  metis_tac[mm_local_insert_sorted_order, mm_local_insert_every, mm_local_hazards_order]
QED

Theorem mm_local_store_ordered_every[local]:
  (!a b. copy_can_merge a b /\ a.cg_dst <= b.cg_dst /\ P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\ SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  (!dst v src. inst.inst_operands = [Lit dst; Var v] /\ FLOOKUP ss.ss_loads v = SOME src ==>
    P <|cg_dst := w2n dst; cg_src := src; cg_length := 32; cg_inst_ids := inst.inst_id ::
      (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id])|>) ==>
  mm_local_scan_every P (scan_store dfg mode ss inst)
Proof
  strip_tac >> simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[mm_local_barrier_every] >> Cases_on `mode_allows_overlap mode` >> simp[] >>
  irule mm_local_hazards_add_ordered_every >>
  simp[invalidate_loads_def, mm_local_invalidate_every] >>
  gvs[oneline operand_lit_val_def, oneline operand_var_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem mm_local_bulk_ordered_every[local]:
  (!a b. copy_can_merge a b /\ a.cg_dst <= b.cg_dst /\ P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\ SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  (!dst src len. inst.inst_operands = [Lit dst; Lit src; Lit len] ==>
    P <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
      cg_inst_ids := [inst.inst_id]|>) ==>
  mm_local_scan_every P (scan_bulk_copy mode ss inst)
Proof
  strip_tac >> simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[mm_local_barrier_every] >> Cases_on `mode_allows_overlap mode` >> simp[] >>
  irule mm_local_hazards_add_ordered_every >>
  simp[invalidate_loads_def, mm_local_invalidate_every] >>
  gvs[oneline operand_lit_val_def, oneline operand_var_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem mm_local_inst_ordered_every:
  (!a b. copy_can_merge a b /\ a.cg_dst <= b.cg_dst /\ P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\ SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  (inst.inst_opcode = MSTORE ==>
    !dst v src. inst.inst_operands = [Lit dst; Var v] /\ FLOOKUP ss.ss_loads v = SOME src ==>
      P <|cg_dst := w2n dst; cg_src := src; cg_length := 32; cg_inst_ids := inst.inst_id ::
        (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id])|>) /\
  (inst.inst_opcode = mode_copy_opcode mode ==>
    !dst src len. inst.inst_operands = [Lit dst; Lit src; Lit len] ==>
      P <|cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
        cg_inst_ids := [inst.inst_id]|>) ==>
  mm_local_scan_every P (scan_inst dfg mode ss inst)
Proof
  strip_tac >> simp[scan_inst_def] >>
  IF_CASES_TAC >- (irule mm_local_load_every >> simp[]) >>
  IF_CASES_TAC >- (irule mm_local_store_ordered_every >> metis_tac[]) >>
  IF_CASES_TAC >- (irule mm_local_bulk_ordered_every >> metis_tac[]) >>
  rpt IF_CASES_TAC >> simp[mm_local_barrier_every]
QED

Theorem mm_local_scan_footprint_lower[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions ==>
  !t. t <= LENGTH is ==>
    mm_local_scan_every
      (\g. !j d l. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
         mm_local_write_footprint (EL j is) = SOME (d,l) ==> g.cg_dst <= d)
      (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE t is))
Proof
  strip_tac >> Induct >- simp[mm_local_scan_every_def, empty_scan_state_def] >>
  strip_tac >> `t < LENGTH is /\ t <= LENGTH is` by decide_tac >>
  simp[rich_listTheory.TAKE_SUC, FOLDL_APPEND] >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst)
     (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE t is)).ss_copies` by
    (irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  irule mm_local_inst_ordered_every >>
  conj_tac
  >- (simp[copy_merge_def, MEM_APPEND] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[mode_copy_opcode_def] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule (Q.INST [`j` |-> `t`, `is` |-> `bb.bb_instructions`]
        mm_local_footprint_store_lower) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `j = t` by
    (gvs[] >> metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]) >>
  gvs[mm_local_write_footprint_def]
QED

Theorem mm_local_final_footprint_lower[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed ==>
  !j d l. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    mm_local_write_footprint (EL j is) = SOME (d,l) ==> g.cg_dst <= d
Proof
  strip_tac >>
  `mm_local_scan_every
      (\g. !j d l. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
         mm_local_write_footprint (EL j is) = SOME (d,l) ==> g.cg_dst <= d)
      (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state is)` by
    (qsuff_tac `!t. t <= LENGTH is ==>
      mm_local_scan_every
        (\g. !j d l. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
           mm_local_write_footprint (EL j is) = SOME (d,l) ==> g.cg_dst <= d)
        (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE t is))`
     >- (disch_then (qspec_then `LENGTH is` mp_tac) >> simp[]) >>
     metis_tac[mm_local_scan_footprint_lower]) >>
  gvs[scan_block_def, hard_barrier_def, mm_local_scan_every_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem mm_local_canonical_due_log_lower[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  ws = MAP (THE o cap) (due ++ [r]) ==>
  !d bs. MEM (d,bs) ws ==> g.cg_dst <= d
Proof
  strip_tac >>
  `!d l. (?bs. MEM (d,bs) ws /\ LENGTH bs = l) <=>
    ?j. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      mm_local_write_footprint (EL j is) = SOME (d,l)` by
    metis_tac[mm_local_canonical_due_log_footprint] >>
  `!j d l. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    mm_local_write_footprint (EL j is) = SOME (d,l) ==> g.cg_dst <= d` by
    metis_tac[mm_local_final_footprint_lower] >>
  metis_tac[]
QED

Theorem mm_local_ancestor_destination_geometry[local]:
  mm_local_copy_ancestor c A /\
  (~copy_overwrites A (copy_dst_interval h) \/ copy_can_merge A h \/ copy_can_merge h A) ==>
  ~copy_overwrites c (copy_dst_interval h) \/
  c.cg_src + h.cg_dst = c.cg_dst + h.cg_src
Proof
  simp[mm_local_copy_ancestor_def, copy_can_merge_def,
    copy_overwrites_def, copy_dst_interval_def,
    mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
    mmIntervalTheory.interval_end_def, arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem mm_local_ancestor_source_exclusion[local]:
  mm_local_copy_ancestor c A /\ ~copy_overwrites A iv ==>
  ~copy_overwrites c iv
Proof
  simp[mm_local_copy_ancestor_def, copy_overwrites_def, copy_dst_interval_def,
    mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
    mmIntervalTheory.interval_end_def, arithmeticTheory.MAX_DEF,
    arithmeticTheory.MIN_DEF] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem mm_local_ancestor_hazard_geometry[local]:
  mm_local_copy_ancestor c A /\ ~copy_overwrites A (copy_src_interval h) /\
  (~copy_overwrites A (copy_dst_interval h) \/ copy_can_merge A h \/ copy_can_merge h A) ==>
  ~copy_overwrites c (copy_src_interval h) /\
  (~copy_overwrites c (copy_dst_interval h) \/
   c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)
Proof
  metis_tac[mm_local_ancestor_source_exclusion,
    mm_local_ancestor_destination_geometry]
QED

Theorem mm_local_overlap_chronology[local]:
  p = read_memory c.cg_src c.cg_length s /\
  q = read_memory h.cg_src h.cg_length v /\
  u.vs_memory = (write_memory_with_expansion c.cg_dst p s).vs_memory /\
  read_memory c.cg_src c.cg_length u = read_memory c.cg_src c.cg_length v /\
  ~copy_overwrites c (copy_src_interval h) /\
  (~copy_overwrites c (copy_dst_interval h) \/
    c.cg_src + h.cg_dst = c.cg_dst + h.cg_src) ==>
  mm_local_write_compatible c.cg_dst p h.cg_dst q
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `read_memory h.cg_src h.cg_length u = read_memory h.cg_src h.cg_length s` by
    (irule venomWriteReplayPropsTheory.read_write_log_memory >> qexists `[(c.cg_dst,p)]` >>
     simp[] >>
     gvs[copy_overwrites_def, copy_src_interval_def, copy_dst_interval_def,
       mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
       mmIntervalTheory.interval_end_def, mm_local_read_memory_bytes,
       mm_local_bytes_def, arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
     decide_tac) >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (gvs[copy_overwrites_def, copy_dst_interval_def,
       mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
       mmIntervalTheory.interval_end_def, mm_local_read_memory_bytes,
       mm_local_bytes_def, arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF,
       mm_local_write_compatible_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  qpat_x_assum `u.vs_memory = _` kall_tac >>
  gvs[mm_local_read_memory_bytes, mm_local_bytes_def, GENLIST_FUN_EQ] >>
  pure_rewrite_tac[mm_local_write_compatible_def, LENGTH_GENLIST] >> rpt strip_tac >>
  `x-c.cg_dst < c.cg_length /\ x-h.cg_dst < h.cg_length /\
   (x-c.cg_dst)+c.cg_src = (x-h.cg_dst)+h.cg_src` by decide_tac >>
  qpat_x_assum `!i. i < c.cg_length ==> _` (qspec_then `x-c.cg_dst` mp_tac) >>
  qpat_x_assum `!i. i < h.cg_length ==> _` (qspec_then `x-h.cg_dst` mp_tac) >>
  asm_simp_tac bool_ss [EL_GENLIST] >> metis_tac[]
QED

Theorem mm_local_indexed_bulk_hazard_geometry[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
  (EL l is).inst_opcode = MCOPY /\
  (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
  c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
         cg_inst_ids := [(EL j is).inst_id]|> /\
  h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
         cg_inst_ids := [(EL l is).inst_id]|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ~copy_overwrites c (copy_src_interval h) /\
  (~copy_overwrites c (copy_dst_interval h) \/ c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)
Proof
  strip_tac >>
  qabbrev_tac `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
                    empty_scan_state (TAKE l is)` >>
  `?A. MEM A ss.ss_copies /\ MEM (EL j is).inst_id A.cg_inst_ids /\
      mm_local_copy_ancestor c A /\ mm_local_copy_ancestor A g` by
    (irule (REWRITE_RULE [mode_copy_opcode_def]
      (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_bulk_ancestry)) >> simp[Abbr `ss`] >> metis_tac[]) >>
  qabbrev_tac `hs = flush_hazards Mem2Mem
     (invalidate_loads ss (mk_interval h.cg_dst h.cg_length)) h` >>
  `(scan_inst (dfg_build_function fn0) Mem2Mem ss (EL l is)).ss_flushed = hs.ss_flushed` by
    gvs[Abbr `hs`, scan_inst_def, scan_bulk_copy_def, mode_load_opcode_def,
        mode_copy_opcode_def, operand_lit_val_def, mode_allows_overlap_def] >>
  `MEM A hs.ss_copies /\ ~copy_overwrites A (copy_src_interval h)` by
    (`l < LENGTH is` by decide_tac >>
     `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by simp[] >>
     `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is)` by
       simp[Abbr `ss`] >>
     `hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval h.cg_dst h.cg_length)) h` by
       simp[Abbr `hs`] >>
     metis_tac[mm_local_indexed_future_hazard]) >>
  `~copy_overwrites A (copy_dst_interval h) \/ copy_can_merge A h \/ copy_can_merge h A` by
    (fs[Abbr `hs`] >> drule mm_local_hazards_destination_alternative >>
     simp[copy_overwrites_def, copy_dst_interval_def,
       mmIntervalTheory.interval_overlaps_def, arithmeticTheory.MAX_COMM,
       arithmeticTheory.MIN_COMM] >> metis_tac[]) >>
  metis_tac[mm_local_ancestor_hazard_geometry]
QED

Theorem mm_local_indexed_selected_hazard_geometry:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE j is) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE l is) /\
  ((?dj sj lj. (EL j is).inst_opcode = mode_copy_opcode mode /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  ((?dl sl ll. (EL l is).inst_opcode = mode_copy_opcode mode /\
      (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
      h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
             cg_inst_ids := [(EL l is).inst_id]|>) \/
   (?dl vl srcl. (EL l is).inst_opcode = MSTORE /\
      (EL l is).inst_operands = [Lit dl; Var vl] /\
      FLOOKUP ss.ss_loads vl = SOME srcl /\
      h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
             cg_inst_ids := [(EL l is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vl of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  (mode = Mem2Mem ==> ~copy_overwrites c (copy_src_interval h)) /\
  (~copy_overwrites c (copy_dst_interval h) \/ c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?A. MEM A ss.ss_copies /\ MEM (EL j is).inst_id A.cg_inst_ids /\
      mm_local_copy_ancestor c A` by
    (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = mode_copy_opcode mode /\ _) \/ _` strip_assume_tac
     >- metis_tac[mm_local_indexed_bulk_ancestry] >>
     metis_tac[mm_local_indexed_store_ancestry]) >>
  qabbrev_tac `hs = flush_hazards mode
     (invalidate_loads ss (mk_interval h.cg_dst h.cg_length)) h` >>
  `(scan_inst (dfg_build_function fn0) mode ss (EL l is)).ss_flushed = hs.ss_flushed` by
    (qpat_x_assum `ss = FOLDL _ _ _` kall_tac >>
     qpat_x_assum `s0 = FOLDL _ _ _` kall_tac >>
     qpat_x_assum `is = bb.bb_instructions` kall_tac >>
     qpat_x_assum `(?dl sl ll. (EL l is).inst_opcode = mode_copy_opcode mode /\ _) \/ _` strip_assume_tac >>
     Cases_on `mode` >>
     simp[Abbr `hs`, scan_inst_def, scan_bulk_copy_def, scan_store_def,
       mode_load_opcode_def, mode_copy_opcode_def, operand_lit_val_def,
       operand_var_def, mode_allows_overlap_def] >>
     simp[flush_hazards_def, invalidate_loads_def, mode_allows_overlap_def,
       flush_copies_def] >> rpt IF_CASES_TAC >> simp[]) >>
  `MEM A hs.ss_copies` by
    (`l < LENGTH is` by decide_tac >>
     `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
       (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = mode_copy_opcode mode /\ _) \/ _` strip_assume_tac >>
        Cases_on `mode` >> gvs[mode_copy_opcode_def]) >>
     `hs = flush_hazards mode (invalidate_loads ss (mk_interval h.cg_dst h.cg_length)) h` by
       simp[Abbr `hs`] >>
     metis_tac[mm_local_indexed_future_survivor]) >>
  `~copy_overwrites A (copy_dst_interval h) \/ copy_can_merge A h \/ copy_can_merge h A` by
    (fs[Abbr `hs`] >> drule mm_local_hazards_destination_alternative >>
     simp[copy_overwrites_def, copy_dst_interval_def,
       mmIntervalTheory.interval_overlaps_def, arithmeticTheory.MAX_COMM,
       arithmeticTheory.MIN_COMM] >> metis_tac[]) >>
  (reverse conj_tac >- metis_tac[mm_local_ancestor_destination_geometry] >>
  Cases_on `mode = Mem2Mem` >> simp[] >>
  qpat_x_assum `is = bb.bb_instructions` kall_tac >>
  qpat_x_assum `ss = FOLDL _ _ _` kall_tac >>
  qpat_x_assum `s0 = FOLDL _ _ _` kall_tac >>
  qpat_x_assum `(?dj sj lj. _ /\ _ /\ _) \/ _` kall_tac >>
  qpat_x_assum `(?dl sl ll. _ /\ _ /\ _) \/ _` kall_tac >>
  fs[Abbr `hs`] >>
  irule mm_local_ancestor_source_exclusion >> qexists `A` >>
  reverse conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  irule mm_local_hazards_source_exclusion >>
  qexists `invalidate_loads ss (mk_interval h.cg_dst h.cg_length)` >>
  first_assum MATCH_ACCEPT_TAC)
QED

Theorem mm_local_indexed_store_bulk_hazard_geometry[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dj; Var vj] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads vj = SOME srcj /\
  c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vj of NONE => [] | SOME li => [li.inst_id])|> /\
  (EL l is).inst_opcode = MCOPY /\
  (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
  h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
         cg_inst_ids := [(EL l is).inst_id]|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ~copy_overwrites c (copy_src_interval h) /\
  (~copy_overwrites c (copy_dst_interval h) \/ c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)
Proof
  strip_tac >> metis_tac[REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_selected_hazard_geometry)]
QED

Theorem mm_local_indexed_bulk_store_hazard_geometry[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
  c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
         cg_inst_ids := [(EL j is).inst_id]|> /\
  (EL l is).inst_opcode = MSTORE /\
  (EL l is).inst_operands = [Lit dl; Var vl] /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is) /\
  FLOOKUP ss.ss_loads vl = SOME srcl /\
  h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
         cg_inst_ids := [(EL l is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vl of NONE => [] | SOME li => [li.inst_id])|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ~copy_overwrites c (copy_src_interval h) /\
  (~copy_overwrites c (copy_dst_interval h) \/ c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)
Proof
  strip_tac >> metis_tac[REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_selected_hazard_geometry)]
QED

Theorem mm_local_indexed_store_store_hazard_geometry[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dj; Var vj] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads vj = SOME srcj /\
  c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vj of NONE => [] | SOME li => [li.inst_id])|> /\
  (EL l is).inst_opcode = MSTORE /\
  (EL l is).inst_operands = [Lit dl; Var vl] /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is) /\
  FLOOKUP ss.ss_loads vl = SOME srcl /\
  h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
         cg_inst_ids := [(EL l is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vl of NONE => [] | SOME li => [li.inst_id])|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ~copy_overwrites c (copy_src_interval h) /\
  (~copy_overwrites c (copy_dst_interval h) \/ c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)
Proof
  strip_tac >> metis_tac[REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_selected_hazard_geometry)]
QED

Theorem mm_local_indexed_bulk_capture_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
  (EL l is).inst_opcode = MCOPY /\
  (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  mm_local_write_compatible (w2n dj) (read_memory (w2n sj) (w2n lj) (H j))
    (w2n dl) (read_memory (w2n sl) (w2n ll) (H l))
Proof
  strip_tac >>
  qabbrev_tac `c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
                    cg_inst_ids := [(EL j is).inst_id]|>` >>
  qabbrev_tac `h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
                    cg_inst_ids := [(EL l is).inst_id]|>` >>
  `~copy_overwrites c (copy_src_interval h) /\
   (~copy_overwrites c (copy_dst_interval h) \/ c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)` by
    (irule mm_local_indexed_bulk_hazard_geometry >>
     simp[Abbr `c`, Abbr `h`] >> metis_tac[]) >>
  qabbrev_tac `cuts = \q. FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
                    empty_scan_state (TAKE q is)` >>
  `!q. SUC j <= q /\ q < l ==>
    ?A. MEM A (cuts q).ss_copies /\ mm_local_copy_ancestor c A /\
        ~MEM A (scan_inst (dfg_build_function fn0) Mem2Mem (cuts q) (EL q is)).ss_flushed` by
    (rpt strip_tac >> `q < r` by decide_tac >>
     `cuts q = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
                  empty_scan_state (TAKE q is)` by simp[Abbr `cuts`] >>
     `c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
            cg_inst_ids := [(EL j is).inst_id]|>` by simp[Abbr `c`] >>
     drule_all mm_local_indexed_bulk_trajectory >> simp[]) >>
  `SUC j <= l /\ l <= N /\ j < N` by decide_tac >>
  `read_memory c.cg_src c.cg_length (H l) =
    read_memory c.cg_src c.cg_length (H (SUC j))` by
    (drule_all mm_local_ancestral_interval_read >> simp[]) >>
  `mm_local_write_capture is H N j =
    SOME (w2n dj,read_memory (w2n sj) (w2n lj) (H j))` by
    (irule (cj 1 mm_local_write_capture_copy) >> simp[]) >>
  drule_all mm_local_write_capture_sound >> strip_tac >>
  `mm_local_write_compatible c.cg_dst (read_memory c.cg_src c.cg_length (H j))
     h.cg_dst (read_memory h.cg_src h.cg_length (H l))` by
    (irule mm_local_overlap_chronology >>
     simp[] >> qexistsl [`H j`, `H (SUC j)`, `H l`] >>
     simp[Abbr `c`] >> metis_tac[]) >>
  gvs[Abbr `c`, Abbr `h`]
QED

Theorem mm_local_indexed_bulk_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
  (EL l is).inst_opcode = MCOPY /\
  (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,q) ==>
  mm_local_write_compatible a p b q
Proof
  strip_tac >>
  `j < N` by decide_tac >>
  `mm_local_write_capture is H N j =
    SOME (w2n dj,read_memory (w2n sj) (w2n lj) (H j))` by
    (irule (cj 1 mm_local_write_capture_copy) >> simp[]) >>
  `mm_local_write_capture is H N l =
    SOME (w2n dl,read_memory (w2n sl) (w2n ll) (H l))` by
    (irule (cj 1 mm_local_write_capture_copy) >> simp[]) >>
  gvs[] >> metis_tac[mm_local_indexed_bulk_capture_compatible]
QED

Theorem mm_local_write_capture_store_post_phis[local]:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  h = phi_prefix_length bb.bb_instructions /\ h <= j /\ j <= LENGTH bb.bb_instructions /\
  LENGTH states = SUC (j-h) /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  EL 0 states = s_phi with vs_inst_idx := h /\
  (!r. r < j-h ==>
    ~is_terminator (EL (h+r) bb.bb_instructions).inst_opcode /\
    ?t. step_inst fuel ctx (EL (h+r) bb.bb_instructions) (EL r states) = OK t /\
        EL (SUC r) states = t with vs_inst_idx := SUC (EL r states).vs_inst_idx) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state
      (TAKE j bb.bb_instructions) /\
  is = bb.bb_instructions /\ mm_local_history is H N /\ j < N /\
  H j = EL (j-h) states /\ (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\ FLOOKUP ss.ss_loads v = SOME src ==>
  mm_local_write_capture is H N j = SOME (w2n dst,read_memory src 32 (H j))
Proof
  strip_tac >>
  `!u a. FLOOKUP ss.ss_loads u = SOME a ==>
     lookup_var u (EL (j-h) states) = SOME (mload a (EL (j-h) states))` by
    (match_mp_tac mm_local_live_load_post_phis >> simp[]) >>
  `lookup_var v (H j) = SOME (mload src (H j))` by metis_tac[] >>
  drule_all mm_local_write_capture_store >> simp[venomWriteReplayPropsTheory.mload_bytes]
QED

Theorem mm_local_selected_write_capture_bounds:
  j < N /\ j < LENGTH is /\
  (((?d s n. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit d; Lit s; Lit n] /\
      c.cg_dst = w2n d /\ c.cg_src = w2n s /\ c.cg_length = w2n n)) \/
   (?d v src. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit d; Var v] /\
      lookup_var v (H j) = SOME (mload src (H j)) /\
      c.cg_dst = w2n d /\ c.cg_src = src /\ c.cg_length = 32)) ==>
  mm_local_write_capture is H N j =
    SOME (c.cg_dst,read_memory c.cg_src c.cg_length (H j))
Proof
  strip_tac
  >- metis_tac[mm_local_write_capture_copy_bounds] >>
  metis_tac[mm_local_write_capture_store_bounds, venomWriteReplayPropsTheory.mload_bytes]
QED

Theorem mm_local_selected_write_capture[local]:
  j < N /\ mm_local_history is H N /\
  (((?d s n. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit d; Lit s; Lit n] /\
      c.cg_dst = w2n d /\ c.cg_src = w2n s /\ c.cg_length = w2n n)) \/
   (?d v src. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit d; Var v] /\
      lookup_var v (H j) = SOME (mload src (H j)) /\
      c.cg_dst = w2n d /\ c.cg_src = src /\ c.cg_length = 32)) ==>
  mm_local_write_capture is H N j =
    SOME (c.cg_dst,read_memory c.cg_src c.cg_length (H j))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule mm_local_selected_write_capture_bounds >>
  gvs[mm_local_history_def]
QED

Theorem mm_local_indexed_selected_captures_compatible_interval:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\
  (!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      lookup_var vj (H j) = SOME (mload srcj (H j)) /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  ((?dl sl ll. (EL l is).inst_opcode = MCOPY /\
      (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
      h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
             cg_inst_ids := [(EL l is).inst_id]|>) \/
   (?dl vl srcl. (EL l is).inst_opcode = MSTORE /\
      (EL l is).inst_operands = [Lit dl; Var vl] /\
      FLOOKUP ss.ss_loads vl = SOME srcl /\
      lookup_var vl (H l) = SOME (mload srcl (H l)) /\
      h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
             cg_inst_ids := [(EL l is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vl of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `~copy_overwrites c (copy_src_interval h) /\
   (~copy_overwrites c (copy_dst_interval h) \/ c.cg_src + h.cg_dst = c.cg_dst + h.cg_src)` by
    metis_tac[REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_selected_hazard_geometry)] >>
  qabbrev_tac `cuts = \q. FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
                    empty_scan_state (TAKE q is)` >>
  `!q. SUC j <= q /\ q < l ==>
    ?A. MEM A (cuts q).ss_copies /\ mm_local_copy_ancestor c A /\
        ~MEM A (scan_inst (dfg_build_function fn0) Mem2Mem (cuts q) (EL q is)).ss_flushed` by
    (rpt strip_tac >> `q < r` by decide_tac >>
     `cuts q = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
                  empty_scan_state (TAKE q is)` by simp[Abbr `cuts`] >>
     qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac
     >- metis_tac[mm_local_indexed_bulk_trajectory] >>
     metis_tac[mm_local_indexed_store_trajectory]) >>
  `SUC j <= l /\ l <= N /\ j < N` by decide_tac >>
  `read_memory c.cg_src c.cg_length (H l) =
    read_memory c.cg_src c.cg_length (H (SUC j))` by
    (irule mm_local_ancestral_interval_read_recurrence >>
     (conj_tac >- simp[]) >>
     qexistsl [`cuts`, `dfg_build_function fn0`, `is`, `N`] >>
     gvs[]) >>
  `mm_local_write_capture is H N j =
    SOME (c.cg_dst,read_memory c.cg_src c.cg_length (H j))` by
    (irule mm_local_selected_write_capture_bounds >> simp[] >>
     qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac >>
     gvs[] >> metis_tac[]) >>
  `mm_local_write_capture is H N l =
    SOME (h.cg_dst,read_memory h.cg_src h.cg_length (H l))` by
    (irule mm_local_selected_write_capture_bounds >> simp[] >>
     qpat_x_assum `(?dl sl ll. (EL l is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac >>
     gvs[] >> metis_tac[]) >>
  `(H (SUC j)).vs_memory =
     (write_memory_with_expansion c.cg_dst (read_memory c.cg_src c.cg_length (H j)) (H j)).vs_memory` by
    (first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  `mm_local_write_compatible c.cg_dst (read_memory c.cg_src c.cg_length (H j))
     h.cg_dst (read_memory h.cg_src h.cg_length (H l))` by
    (irule mm_local_overlap_chronology >>
     simp[] >> qexistsl [`H j`, `H (SUC j)`, `H l`] >> simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem mm_local_indexed_selected_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      lookup_var vj (H j) = SOME (mload srcj (H j)) /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  ((?dl sl ll. (EL l is).inst_opcode = MCOPY /\
      (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
      h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
             cg_inst_ids := [(EL l is).inst_id]|>) \/
   (?dl vl srcl. (EL l is).inst_opcode = MSTORE /\
      (EL l is).inst_operands = [Lit dl; Var vl] /\
      FLOOKUP ss.ss_loads vl = SOME srcl /\
      lookup_var vl (H l) = SOME (mload srcl (H l)) /\
      h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
             cg_inst_ids := [(EL l is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vl of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (rpt strip_tac >> `q < N /\ q < r` by decide_tac >>
     Cases_on `q = j`
     >- (gvs[] >> metis_tac[mm_local_write_capture_sound]) >>
     `SUC j <= q` by decide_tac >>
     `?A. MEM A (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
         empty_scan_state (TAKE q is)).ss_copies /\ mm_local_copy_ancestor c A /\
       ~MEM A (scan_inst (dfg_build_function fn0) Mem2Mem
         (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
           empty_scan_state (TAKE q is)) (EL q is)).ss_flushed` by
       (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac
        >- metis_tac[mm_local_indexed_bulk_trajectory] >>
        metis_tac[mm_local_indexed_store_trajectory]) >>
     Cases_on `mm_local_write_capture is H N q`
     >- (simp[] >> metis_tac[mm_local_surviving_history_frame]) >>
     PairCases_on `x` >> simp[] >> metis_tac[mm_local_write_capture_sound]) >>
  mp_tac (SPEC_ALL mm_local_indexed_selected_captures_compatible_interval) >> simp[]
QED

Theorem mm_local_indexed_store_bulk_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dj; Var vj] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads vj = SOME srcj /\
  lookup_var vj (H j) = SOME (mload srcj (H j)) /\
  c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vj of NONE => [] | SOME li => [li.inst_id])|> /\
  (EL l is).inst_opcode = MCOPY /\
  (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
  h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
         cg_inst_ids := [(EL l is).inst_id]|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >> metis_tac[mm_local_indexed_selected_captures_compatible]
QED

Theorem mm_local_indexed_bulk_store_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
  c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
         cg_inst_ids := [(EL j is).inst_id]|> /\
  (EL l is).inst_opcode = MSTORE /\
  (EL l is).inst_operands = [Lit dl; Var vl] /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is) /\
  FLOOKUP ss.ss_loads vl = SOME srcl /\
  lookup_var vl (H l) = SOME (mload srcl (H l)) /\
  h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
         cg_inst_ids := [(EL l is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vl of NONE => [] | SOME li => [li.inst_id])|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >> metis_tac[mm_local_indexed_selected_captures_compatible]
QED

Theorem mm_local_indexed_store_store_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dj; Var vj] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads vj = SOME srcj /\
  lookup_var vj (H j) = SOME (mload srcj (H j)) /\
  c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vj of NONE => [] | SOME li => [li.inst_id])|> /\
  (EL l is).inst_opcode = MSTORE /\
  (EL l is).inst_operands = [Lit dl; Var vl] /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is) /\
  FLOOKUP ss.ss_loads vl = SOME srcl /\
  lookup_var vl (H l) = SOME (mload srcl (H l)) /\
  h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
         cg_inst_ids := [(EL l is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) vl of NONE => [] | SOME li => [li.inst_id])|> /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >> metis_tac[mm_local_indexed_selected_captures_compatible]
QED

Theorem mm_local_indexed_selected_captures_post_phis[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= r /\ r < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE l is) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  ((?dl sl ll. (EL l is).inst_opcode = MCOPY /\
      (EL l is).inst_operands = [Lit dl; Lit sl; Lit ll] /\
      h = <|cg_dst := w2n dl; cg_src := w2n sl; cg_length := w2n ll;
             cg_inst_ids := [(EL l is).inst_id]|>) \/
   (?dl vl srcl. (EL l is).inst_opcode = MSTORE /\
      (EL l is).inst_operands = [Lit dl; Var vl] /\
      FLOOKUP ss.ss_loads vl = SOME srcl /\
      h = <|cg_dst := w2n dl; cg_src := srcl; cg_length := 32;
             cg_inst_ids := [(EL l is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vl of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  hp = phi_prefix_length bb.bb_instructions /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  (!x. x = j \/ x = l ==>
    ?states. hp <= x /\ x <= LENGTH bb.bb_instructions /\
      LENGTH states = SUC (x-hp) /\ EL 0 states = s_phi with vs_inst_idx := hp /\
      H x = EL (x-hp) states /\
      (!z. z < x-hp ==>
        ~is_terminator (EL (hp+z) bb.bb_instructions).inst_opcode /\
        ?t. step_inst fuel ctx (EL (hp+z) bb.bb_instructions) (EL z states) = OK t /\
            EL (SUC z) states = t with vs_inst_idx := SUC (EL z states).vs_inst_idx)) ==>
  mm_local_write_compatible a p b qbytes
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x v src. (x = j \/ x = l) /\
     FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE x bb.bb_instructions)).ss_loads v = SOME src ==>
     lookup_var v (H x) = SOME (mload src (H x))` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     qpat_assum `!x. x = j \/ x = l ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `!u a. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE x bb.bb_instructions)).ss_loads u = SOME a ==>
       lookup_var u (EL (x-hp) states) = SOME (mload a (EL (x-hp) states))` by
       (match_mp_tac mm_local_live_load_post_phis >> simp[]) >>
     metis_tac[]) >>
  `!v src. FLOOKUP s0.ss_loads v = SOME src ==>
     lookup_var v (H j) = SOME (mload src (H j))` by metis_tac[] >>
  `!v src. FLOOKUP ss.ss_loads v = SOME src ==>
     lookup_var v (H l) = SOME (mload src (H l))` by metis_tac[] >>
  qpat_x_assum `!x. x = j \/ x = l ==> _` kall_tac >>
  qpat_x_assum `!x v src. _` kall_tac >>
  qpat_x_assum `eval_phis _ _ = _` kall_tac >>
  qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac >>
  qpat_x_assum `(?dl sl ll. (EL l is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac
  >- (drule_all mm_local_indexed_bulk_captures_compatible >> simp[])
  >- (`lookup_var vl (H l) = SOME (mload srcl (H l))` by metis_tac[] >>
      drule_all mm_local_indexed_bulk_store_captures_compatible >> simp[])
  >- (`lookup_var vj (H j) = SOME (mload srcj (H j))` by metis_tac[] >>
      drule_all mm_local_indexed_store_bulk_captures_compatible >> simp[]) >>
  `lookup_var vj (H j) = SOME (mload srcj (H j))` by metis_tac[] >>
  `lookup_var vl (H l) = SOME (mload srcl (H l))` by metis_tac[] >>
  drule_all mm_local_indexed_store_store_captures_compatible >> simp[]
QED

Theorem mm_local_pending_prefix_source_exclusion:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ q < j /\ j <= r /\ r < LENGTH is /\ r < N /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP ss.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  MEM q (mm_local_pending_indices is
    (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed r) /\
  mm_local_write_capture is H N q = SOME (d,bs) ==>
  c.cg_src+c.cg_length <= d \/ d+LENGTH bs <= c.cg_src \/ c.cg_length = 0 \/ bs = []
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `MEM q (mm_local_pending_indices is
    (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed j)` by
    (gvs[mm_local_pending_indices_mem] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `j <= LENGTH is /\ j <= N` by decide_tac >>
  `?h. MEM h ss.ss_copies /\ MEM (EL q is).inst_id h.cg_inst_ids /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length` by
    (mp_tac (Q.INST [`gs` |->
       `(scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed`,
       `n` |-> `j`, `j` |-> `q`] (SPEC_ALL mm_local_canonical_pending_capture_owner)) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `MEM q (mm_local_pending_indices _ _ r)`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
  qabbrev_tac `hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval c.cg_dst c.cg_length)) c` >>
  `(scan_inst (dfg_build_function fn0) Mem2Mem ss (EL j is)).ss_flushed = hs.ss_flushed` by
    (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac >>
     gvs[Abbr `hs`, scan_inst_def, scan_bulk_copy_def, scan_store_def,
       mode_load_opcode_def, mode_copy_opcode_def, operand_lit_val_def,
       operand_var_def, mode_allows_overlap_def]) >>
  `~copy_overwrites h (copy_src_interval c)` by
    (rename1 `rep_of_group is g = SOME ((EL owner_r is).inst_id,g)` >>
     `j < LENGTH is /\ j <= owner_r` by decide_tac >>
     `hs = flush_hazards Mem2Mem
       (invalidate_loads ss (mk_interval c.cg_dst c.cg_length)) c` by simp[Abbr `hs`] >>
     metis_tac[mm_local_indexed_future_hazard]) >>
  metis_tac[mm_local_capture_source_exclusion, LENGTH_NIL]
QED

Theorem mm_local_pending_suffix_source_exclusion:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j <= q /\ q < r /\ r < LENGTH is /\ r < N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE q is) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  ~MEM q (mm_local_pending_indices is
    (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed r) /\
  mm_local_write_capture is H N q = SOME (d,bs) ==>
  c.cg_src+c.cg_length <= d \/ d+LENGTH bs <= c.cg_src \/ c.cg_length = 0 \/ bs = []
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `j < q` by
    (Cases_on `j = q` >> simp[] >>
     `MEM j (mm_local_pending_indices is
       (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed r)` by
       (pure_rewrite_tac[mm_local_pending_indices_mem] >>
        conj_tac >- decide_tac >> conj_tac
        >- (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _`
              strip_assume_tac >> simp[]) >>
        qexistsl [`g`,`r`] >> simp[]) >> metis_tac[]) >>
  `SUC j <= q` by decide_tac >>
  `?h. MEM h ss.ss_copies /\ mm_local_copy_ancestor c h /\
    ~MEM h (scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is)).ss_flushed` by
    (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac
     >- (drule_all mm_local_indexed_bulk_trajectory >> simp[]) >>
     drule_all mm_local_indexed_store_trajectory >> simp[]) >>
  `q < N /\ q < LENGTH is` by decide_tac >>
  `h.cg_length = 0 \/ LENGTH bs = 0 \/
    h.cg_src+h.cg_length <= d \/ d+LENGTH bs <= h.cg_src` by
    metis_tac[mm_local_scan_step_war_exclusion] >>
  `h.cg_src <= c.cg_src /\
   c.cg_src+c.cg_length <= h.cg_src+h.cg_length` by
    (qpat_assum `mm_local_copy_ancestor c h` mp_tac >>
     pure_rewrite_tac[mm_local_copy_ancestor_def] >> strip_tac >> decide_tac) >>
  Cases_on `LENGTH bs = 0` >- gvs[] >>
  Cases_on `h.cg_length = 0`
  >- (`c.cg_length = 0` by simp[] >> simp[]) >>
  gvs[] >> decide_tac
QED

Theorem mm_local_live_segment_capture_recurrence:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM b (mm_local_pending_indices is gs r) /\ b <= q /\ q < r ==>
  (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory
Proof
  strip_tac >> Cases_on `mm_local_write_capture is H N q`
  >- (simp[] >>
      `r <= LENGTH is /\ r <= N` by decide_tac >>
      Cases_on `b = q`
      >- (mp_tac (Q.INST [`n` |-> `r`, `j` |-> `b`, `ss` |->
             `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE r is)`]
             (SPEC_ALL mm_local_canonical_pending_owner)) >>
          simp[] >> gvs[]) >>
      `MEM b (mm_local_pending_indices is gs q)` by
        (pure_rewrite_tac[mm_local_pending_indices_mem] >>
         qpat_assum `MEM b (mm_local_pending_indices _ _ r)`
           (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
         conj_tac >- decide_tac >> conj_tac >- first_assum ACCEPT_TAC >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qabbrev_tac `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE q is)` >>
      `q <= LENGTH is /\ q <= N` by decide_tac >>
      `?h d bs. MEM h ss.ss_copies /\ MEM (EL b is).inst_id h.cg_inst_ids /\
        mm_local_write_capture is H N b = SOME (d,bs) /\
        h.cg_dst <= d /\ d+LENGTH bs <= h.cg_dst+h.cg_length` by
        (metis_tac[mm_local_canonical_pending_owner]) >>
      `~MEM h (scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is)).ss_flushed` by
        (qpat_x_assum `MEM b (mm_local_pending_indices _ _ r)`
           (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
         `b < LENGTH is` by decide_tac >>
         `scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is) =
          FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
            empty_scan_state (TAKE (SUC q) is)` by
           (`q < LENGTH is` by decide_tac >>
            gvs[Abbr `ss`, rich_listTheory.TAKE_SUC,
              rich_listTheory.DROP_EL_CONS, FOLDL_APPEND]) >>
         rename1 `rep_of_group is g = SOME ((EL owner_r is).inst_id,g)` >>
         `SUC q <= owner_r` by decide_tac >>
         metis_tac[mm_local_indexed_future_not_flushed]) >>
      irule mm_local_surviving_history_frame >>
      goal_assum (drule_at Any) >> qexists `N` >> simp[]) >>
  PairCases_on `x` >> simp[] >> metis_tac[mm_local_write_capture_sound]
QED

Theorem mm_local_fixed_cut_capture_recurrence:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ a <= r /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))) ==>
  !q. a <= q /\ q < r ==>
  (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?b. MEM b (mm_local_pending_indices is gs (SUC q))` by metis_tac[] >>
  `b < SUC q` by metis_tac[mm_local_pending_indices_mem] >>
  `b <= q /\ q < SUC q /\ SUC q < LENGTH is /\ SUC q < N` by decide_tac >>
  drule_all mm_local_live_segment_capture_recurrence >> simp[]
QED

Theorem mm_local_pending_replay_start[local]:
  b = MIN_LIST (mm_local_pending_indices is gs r ++ [r]) ==>
  b <= r /\ (!j. MEM j (mm_local_pending_indices is gs r) ==> b <= j) /\
  (b = r \/ MEM b (mm_local_pending_indices is gs r))
Proof
  strip_tac >>
  `mm_local_pending_indices is gs r ++ [r] <> []` by simp[] >>
  drule rich_listTheory.MIN_LIST_MEM >>
  drule rich_listTheory.MIN_LIST_PROPERTY >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_pending_source_replay:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ b <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (b = r \/ MEM b (mm_local_pending_indices is gs r)) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  t = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H b) (MAP (\q. b+q) (COUNT_LIST (r-b))) ==>
  read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule venomWriteReplayPropsTheory.selective_segment_replay >>
  qexistsl [`\q. MEM q (mm_local_pending_indices is gs r)`, `b`,
    `mm_local_write_capture is H N`, `r`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `c.cg_src+c.cg_length <= d \/ d+LENGTH bs <= c.cg_src \/ c.cg_length = 0 \/ bs = []`
        suffices_by simp[arithmeticTheory.ADD_COMM] >>
      mp_tac (Q.INST [`j` |-> `j`, `r` |-> `r`, `ss` |-> `s0`]
        (SPEC_ALL mm_local_pending_prefix_source_exclusion)) >>
      simp[] >> gvs[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `MEM b (mm_local_pending_indices is gs r)` by gvs[] >>
      metis_tac[mm_local_live_segment_capture_recurrence]) >>
  rpt strip_tac >>
  `j < r` by decide_tac >>
  `?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g)` by (gvs[] >> metis_tac[]) >>
  `c.cg_src+c.cg_length <= d \/ d+LENGTH bs <= c.cg_src \/ c.cg_length = 0 \/ bs = []`
    suffices_by simp[arithmeticTheory.ADD_COMM] >>
  mp_tac (Q.INST [`j` |-> `j`, `r` |-> `r`, `s0` |-> `s0`,
    `ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE q is)`]
    (SPEC_ALL mm_local_pending_suffix_source_exclusion)) >>
  simp[] >> gvs[]
QED

