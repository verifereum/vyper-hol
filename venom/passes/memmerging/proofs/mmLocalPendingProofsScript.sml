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

Theorem mm_local_hazards_destination_alternative[local]:
  MEM h (flush_hazards mode ss c).ss_copies ==>
  ~copy_overwrites c (copy_dst_interval h) \/
  copy_can_merge h c \/ copy_can_merge c h
Proof
  simp[flush_hazards_def] >> rpt IF_CASES_TAC >>
  gvs[flush_copies_def, MEM_FILTER, waw_hazards_def, FILTER_EQ_NIL, EVERY_MEM] >>
  metis_tac[]
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

Theorem mm_local_pending_cap_cong:
  mm_local_pending cap js s t /\ (!j. MEM j js ==> cap' j = cap j) ==>
  mm_local_pending cap' js s t
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >> qexists `ws` >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `MEM (EL n js) js` by simp[EL_MEM] >> metis_tac[]
QED

Definition mm_local_copies_geometry_def:
  (mm_local_copies_geometry [] = T) /\
  (mm_local_copies_geometry (g::gs) <=>
    EVERY (mm_local_copy_geometry g) gs /\ mm_local_copies_geometry gs)
End

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

