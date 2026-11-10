(* Each local merging phase with its actual original-DFG provenance. *)
Theory mmLocalScanProofs
Ancestors
  mmSupplyWfProofs mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner allocaRemapSSA o1MakeSsaCfg makeSsaCurrentWfSsa
  cfgWf venomWf stateEquiv rich_list mmTransform mmScan mmCopy list sorting
  simplifyCfgPhiSemantics basePtrProofs mmTraceProofs frameViewMemory dftCommutation
  regularMemorySim
Libs
  wordsLib finite_mapLib

Definition mm_local_phase_def:
  mm_local_phase dfg phase (b,t) =
    case phase of
      NONE => transform_block_memzero_supply dfg t b
    | SOME m => transform_block_mode_supply dfg m t b
End

Definition mm_local_prefix_def:
  mm_local_prefix fn0 supply index k =
    FOLDL (\bt phase. mm_local_phase (dfg_build_function fn0) phase bt)
      (EL index fn0.fn_blocks,supply)
      (TAKE k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
End

Theorem mm_local_prefix_zero[local]:
  mm_local_prefix fn0 supply index 0 = (EL index fn0.fn_blocks,supply)
Proof
  simp[mm_local_prefix_def]
QED

Theorem mm_local_prefix_suc[local]:
  k < 4 ==>
  mm_local_prefix fn0 supply index (SUC k) =
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (mm_local_prefix fn0 supply index k)
Proof
  simp[mm_local_prefix_def, TAKE_SUC_BY_TAKE, FOLDL_SNOC]
QED

Theorem mm_local_phase_label[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) ==> cc.bb_label = bb.bb_label
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Definition mm_local_group_roles_def:
  mm_local_group_roles dfg mode xs cg <=>
    !id. MEM id cg.cg_inst_ids ==>
      (?st dst v. MEM st xs /\ st.inst_id = id /\ st.inst_opcode = MSTORE /\
                  st.inst_operands = [Lit dst; Var v]) \/
      (?cp dst src len. MEM cp xs /\ cp.inst_id = id /\
        cp.inst_opcode = mode_copy_opcode mode /\
        cp.inst_operands = [Lit dst; Lit src; Lit len]) \/
      (?pre q mid st post v addr dst li.
        xs = pre ++ [q] ++ mid ++ [st] ++ post /\
        q.inst_opcode = mode_load_opcode mode /\
        q.inst_operands = [Lit addr] /\ q.inst_outputs = [v] /\
        st.inst_opcode = MSTORE /\ st.inst_operands = [Lit dst; Var v] /\
        dfg_get_def dfg v = SOME li /\ li.inst_id = id /\
        MEM st.inst_id cg.cg_inst_ids)
End

Theorem mm_local_roles_merge[local]:
  mm_local_group_roles dfg mode xs a /\ mm_local_group_roles dfg mode xs b ==>
  mm_local_group_roles dfg mode xs (copy_merge a b)
Proof
  simp[mm_local_group_roles_def, copy_merge_def, MEM_APPEND] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  rpt (qpat_x_assum `!id. _` kall_tac) >> metis_tac[]
QED

Theorem mm_local_insert_every[local]:
  !cs cg. EVERY P cs /\ P cg ==> EVERY P (insert_sorted cs cg)
Proof
  Induct_on `cs` >> simp[insert_sorted_def] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem mm_local_merge_every[local]:
  (!a b. P a /\ P b ==> P (copy_merge a b)) ==>
  !cs. EVERY P cs ==> EVERY P (merge_adjacent cs)
Proof
  strip_tac >> recInduct merge_adjacent_ind >>
  simp[merge_adjacent_def] >> rpt strip_tac >>
  Cases_on `copy_can_merge c1 c2` >> gvs[] >> metis_tac[]
QED

Theorem mm_local_add_every[local]:
  (!a b. P a /\ P b ==> P (copy_merge a b)) /\ EVERY P cs /\ P cg ==>
  EVERY P (add_copy cs cg)
Proof
  simp[add_copy_def] >> metis_tac[mm_local_insert_every, mm_local_merge_every]
QED

Definition mm_local_scan_every_def:
  mm_local_scan_every P ss <=> EVERY P ss.ss_copies /\ EVERY P ss.ss_flushed
End

Theorem mm_local_barrier_every[local]:
  mm_local_scan_every P ss ==> mm_local_scan_every P (hard_barrier ss)
Proof
  simp[mm_local_scan_every_def, hard_barrier_def, EVERY_APPEND]
QED

Theorem mm_local_flush_every[local]:
  mm_local_scan_every P ss /\ EVERY P cs ==>
  mm_local_scan_every P (flush_copies ss cs)
Proof
  simp[mm_local_scan_every_def, flush_copies_def, EVERY_APPEND,
       EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_hazards_every[local]:
  mm_local_scan_every P ss ==>
  mm_local_scan_every P (flush_hazards mode ss cg)
Proof
  `!ss Q. mm_local_scan_every P ss ==>
    mm_local_scan_every P (flush_copies ss (FILTER Q ss.ss_copies))` by
    (rpt strip_tac >> irule mm_local_flush_every >>
     gvs[mm_local_scan_every_def, EVERY_MEM, MEM_FILTER]) >>
  simp[flush_hazards_def, waw_hazards_def, raw_hazards_def,
       war_hazards_def, copies_that_overwrite_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> metis_tac[]
QED

Theorem mm_local_invalidate_every[local]:
  mm_local_scan_every P (invalidate_loads ss iv) = mm_local_scan_every P ss
Proof
  simp[mm_local_scan_every_def, invalidate_loads_def]
QED

Theorem mm_local_load_every[local]:
  mm_local_scan_every P ss ==> mm_local_scan_every P (scan_load mode ss inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[scan_load_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = src::ops` >>
  Cases_on `ops`
  >- (
    Cases_on `operand_lit_val src`
    >- simp[scan_load_def, mm_local_barrier_every] >>
    Cases_on `inst.inst_outputs`
    >- simp[scan_load_def, mm_local_barrier_every] >>
    rename1 `inst.inst_outputs = out::outs` >>
    Cases_on `outs` >> simp[scan_load_def, mm_local_barrier_every] >>
    rpt IF_CASES_TAC >>
    gvs[mm_local_scan_every_def, flush_copies_def, copies_that_overwrite_def,
        EVERY_APPEND, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  simp[scan_load_def, mm_local_barrier_every]
QED

Theorem mm_local_store_group_roles[local]:
  MEM inst xs /\ inst.inst_opcode = MSTORE /\
  inst.inst_operands = [Lit dst; Var v] /\
  (?pre q mid post addr. xs = pre ++ [q] ++ mid ++ [inst] ++ post /\
    q.inst_opcode = mode_load_opcode mode /\
    q.inst_operands = [Lit addr] /\ q.inst_outputs = [v]) ==>
  mm_local_group_roles dfg mode xs
    <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
       cg_inst_ids := inst.inst_id ::
         (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) |>
Proof
  strip_tac >> Cases_on `dfg_get_def dfg v` >>
  simp[mm_local_group_roles_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem mm_local_store_roles[local]:
  MEM inst xs /\ inst.inst_opcode = MSTORE /\
  (!v a. FLOOKUP ss.ss_loads v = SOME a ==>
    ?pre q mid post addr. xs = pre ++ [q] ++ mid ++ [inst] ++ post /\
      q.inst_opcode = mode_load_opcode mode /\
      q.inst_operands = [Lit addr] /\ q.inst_outputs = [v]) /\
  mm_local_scan_every (mm_local_group_roles dfg mode xs) ss ==>
  mm_local_scan_every (mm_local_group_roles dfg mode xs)
    (scan_store dfg mode ss inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands`
  >- simp[scan_store_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::ops` >>
  Cases_on `ops` >- simp[scan_store_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::value::ops` >>
  Cases_on `ops`
  >- (
    Cases_on `dst` >> Cases_on `value` >>
    simp[scan_store_def, operand_var_name_def, operand_lit_val_def,
         mm_local_barrier_every] >>
    rename1 `inst.inst_operands = [Lit addr; Var v]` >>
    Cases_on `FLOOKUP ss.ss_loads v`
    >- simp[mm_local_barrier_every] >>
    simp[] >>
    qmatch_goalsub_abbrev_tac `flush_hazards mode ss0 cg` >>
    `mm_local_group_roles dfg mode xs cg` by
      (simp[Abbr `cg`] >> irule mm_local_store_group_roles >>
       simp[] >> metis_tac[]) >>
    `mm_local_scan_every (mm_local_group_roles dfg mode xs) ss0` by
      (simp[Abbr `ss0`] >> IF_CASES_TAC >>
       simp[mm_local_invalidate_every]) >>
    drule mm_local_hazards_every >>
    disch_then (qspecl_then [`mode`, `cg`] assume_tac) >>
    gvs[mm_local_scan_every_def] >>
    irule mm_local_add_every >> simp[mm_local_roles_merge]) >>
  simp[scan_store_def, mm_local_barrier_every]
QED

Theorem mm_local_bulk_roles[local]:
  MEM inst xs /\ inst.inst_opcode = mode_copy_opcode mode /\
  mm_local_scan_every (mm_local_group_roles dfg mode xs) ss ==>
  mm_local_scan_every (mm_local_group_roles dfg mode xs)
    (scan_bulk_copy mode ss inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands`
  >- simp[scan_bulk_copy_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::ops` >>
  Cases_on `ops` >- simp[scan_bulk_copy_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::src::ops` >>
  Cases_on `ops` >- simp[scan_bulk_copy_def, mm_local_barrier_every] >>
  rename1 `inst.inst_operands = dst::src::len::ops` >>
  Cases_on `ops`
  >- (
    Cases_on `dst` >>
    simp[scan_bulk_copy_def, operand_lit_val_def, mm_local_barrier_every] >>
    Cases_on `src` >>
    simp[operand_lit_val_def, mm_local_barrier_every] >>
    Cases_on `len` >>
    simp[operand_lit_val_def, mm_local_barrier_every] >>
    qmatch_goalsub_abbrev_tac `flush_hazards mode ss0 cg` >>
    `mm_local_group_roles dfg mode xs cg` by
      (simp[Abbr `cg`, mm_local_group_roles_def] >> metis_tac[]) >>
    `mm_local_scan_every (mm_local_group_roles dfg mode xs) ss0` by
      (simp[Abbr `ss0`] >> IF_CASES_TAC >>
       simp[mm_local_invalidate_every]) >>
    drule mm_local_hazards_every >>
    disch_then (qspecl_then [`mode`, `cg`] assume_tac) >>
    gvs[mm_local_scan_every_def] >>
    irule mm_local_add_every >> simp[mm_local_roles_merge]) >>
  simp[scan_bulk_copy_def, mm_local_barrier_every]
QED

Theorem mm_local_inst_roles[local]:
  MEM inst xs /\
  (!v a. FLOOKUP ss.ss_loads v = SOME a ==>
    ?pre q mid post addr. xs = pre ++ [q] ++ mid ++ [inst] ++ post /\
      q.inst_opcode = mode_load_opcode mode /\
      q.inst_operands = [Lit addr] /\ q.inst_outputs = [v]) /\
  mm_local_scan_every (mm_local_group_roles dfg mode xs) ss ==>
  mm_local_scan_every (mm_local_group_roles dfg mode xs)
    (scan_inst dfg mode ss inst)
Proof
  strip_tac >> simp[scan_inst_def] >>
  rpt IF_CASES_TAC >>
  metis_tac[mm_local_load_every, mm_local_store_roles,
            mm_local_bulk_roles, mm_local_barrier_every]
QED


Definition mm_local_zero_every_def:
  mm_local_zero_every P mz <=>
    EVERY (\cg. EVERY P cg.cg_inst_ids) mz.mz_copies /\
    EVERY (\cg. EVERY P cg.cg_inst_ids) mz.mz_flushed
End

Theorem mm_local_zero_barrier_every[local]:
  mm_local_zero_every P mz ==> mm_local_zero_every P (memzero_barrier mz)
Proof
  simp[mm_local_zero_every_def, memzero_barrier_def, EVERY_APPEND]
QED

Theorem mm_local_zero_add_every[local]:
  mm_local_zero_every P mz /\ P id ==>
  mm_local_zero_every P
    (mz with mz_copies := add_copy mz.mz_copies (copy_memzero dst len [id]))
Proof
  simp[mm_local_zero_every_def] >> strip_tac >>
  irule mm_local_add_every >>
  simp[copy_merge_def, EVERY_APPEND, copy_memzero_def]
QED

Theorem mm_local_zero_inst_every[local]:
  mm_local_zero_every P mz /\
  ((is_zero_store inst \/ is_calldatasize_copy dfg inst) ==> P inst.inst_id) ==>
  mm_local_zero_every P (scan_inst_memzero dfg mz inst)
Proof
  strip_tac >> simp[scan_inst_memzero_def] >>
  rpt IF_CASES_TAC >> simp[mm_local_zero_barrier_every] >>
  rpt (CASE_TAC >> gvs[mm_local_zero_barrier_every, mm_local_zero_add_every])
QED

Theorem mm_local_zero_fold_every[local]:
  !is mz. mm_local_zero_every P mz /\
  EVERY (\inst. (is_zero_store inst \/ is_calldatasize_copy dfg inst) ==>
                P inst.inst_id) is ==>
  mm_local_zero_every P (FOLDL (scan_inst_memzero dfg) mz is)
Proof
  Induct_on `is` >> simp[] >> metis_tac[mm_local_zero_inst_every]
QED

Theorem mm_local_zero_inst_flushed_prefix[local]:
  scan_inst_memzero dfg (mz with mz_flushed := old ++ mz.mz_flushed) i =
  (scan_inst_memzero dfg mz i) with
    mz_flushed := old ++ (scan_inst_memzero dfg mz i).mz_flushed
Proof
  Cases_on `mz` >>
  simp[scan_inst_memzero_def, memzero_scan_state_fn_updates] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (CASE_TAC >> simp[memzero_barrier_def, APPEND_ASSOC,
                       memzero_scan_state_fn_updates]) >>
  simp[memzero_scan_state_component_equality, memzero_barrier_def, APPEND_ASSOC]
QED

Theorem mm_local_zero_fold_flushed_prefix[local]:
  !is mz. FOLDL (scan_inst_memzero dfg)
    (mz with mz_flushed := old ++ mz.mz_flushed) is =
  (FOLDL (scan_inst_memzero dfg) mz is) with
    mz_flushed := old ++ (FOLDL (scan_inst_memzero dfg) mz is).mz_flushed
Proof
  Induct_on `is` >> simp[mm_local_zero_inst_flushed_prefix]
QED

Theorem mm_local_zero_fold_barrier[local]:
  (memzero_barrier (FOLDL (scan_inst_memzero dfg)
     (memzero_barrier mz) post)).mz_flushed =
  mz.mz_flushed ++ mz.mz_copies ++
    (memzero_barrier (FOLDL (scan_inst_memzero dfg)
       empty_memzero_state post)).mz_flushed
Proof
  `memzero_barrier mz = empty_memzero_state with mz_flushed :=
     (mz.mz_flushed ++ mz.mz_copies) ++ empty_memzero_state.mz_flushed` by
    simp[memzero_barrier_def, empty_memzero_state_def] >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[mm_local_zero_fold_flushed_prefix] >>
  simp[memzero_barrier_def, APPEND_ASSOC]
QED

Theorem mm_local_memzero_barrier_localization[local]:
  bb.bb_instructions = pre ++ [i] ++ post /\
  is_volatile_memory i /\ ~is_zero_store i /\
  ~is_calldatasize_copy dfg i /\
  MEM cg (scan_block_memzero dfg bb).mz_flushed ==>
  EVERY (\id. MEM id (MAP (\x. x.inst_id) pre)) cg.cg_inst_ids \/
  EVERY (\id. MEM id (MAP (\x. x.inst_id) post)) cg.cg_inst_ids
Proof
  strip_tac >>
  `mm_local_zero_every (\id. MEM id (MAP (\x. x.inst_id) pre))
    (FOLDL (scan_inst_memzero dfg) empty_memzero_state pre)` by
    (irule mm_local_zero_fold_every >>
     simp[mm_local_zero_every_def, empty_memzero_state_def, EVERY_MEM,
          MEM_MAP] >> metis_tac[]) >>
  `mm_local_zero_every (\id. MEM id (MAP (\x. x.inst_id) post))
    (memzero_barrier (FOLDL (scan_inst_memzero dfg) empty_memzero_state post))` by
    (irule mm_local_zero_barrier_every >>
     irule mm_local_zero_fold_every >>
     simp[mm_local_zero_every_def, empty_memzero_state_def, EVERY_MEM,
          MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `MEM cg _` mp_tac >>
  simp[scan_block_memzero_def, FOLDL_APPEND, scan_inst_memzero_def,
       mm_local_zero_fold_barrier, MEM_APPEND] >>
  gvs[mm_local_zero_every_def, EVERY_MEM] >> metis_tac[]
QED

Theorem mm_local_memzero_group_roles[local]:
  MEM cg (scan_block_memzero dfg bb).mz_flushed /\ MEM id cg.cg_inst_ids ==>
  ?i. MEM i bb.bb_instructions /\ i.inst_id = id /\
      (is_zero_store i \/ is_calldatasize_copy dfg i)
Proof
  qabbrev_tac `P = \id. ?i. MEM i bb.bb_instructions /\ i.inst_id = id /\
                              (is_zero_store i \/ is_calldatasize_copy dfg i)` >>
  `mm_local_zero_every P (scan_block_memzero dfg bb)` by
    (simp[scan_block_memzero_def] >> irule mm_local_zero_barrier_every >>
     irule mm_local_zero_fold_every >>
     simp[mm_local_zero_every_def, empty_memzero_state_def, EVERY_MEM,
          Abbr `P`] >> metis_tac[]) >>
  gvs[mm_local_zero_every_def, EVERY_MEM, Abbr `P`] >> metis_tac[]
QED

Definition mm_local_group_ids_def:
  mm_local_group_ids cs = FLAT (MAP (\cg. cg.cg_inst_ids) cs)
End

Theorem mm_local_group_ids_append[local]:
  mm_local_group_ids (a ++ b) = mm_local_group_ids a ++ mm_local_group_ids b
Proof
  simp[mm_local_group_ids_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem mm_local_merge_ids_exact[local]:
  !cs. mm_local_group_ids (merge_adjacent cs) = mm_local_group_ids cs
Proof
  recInduct merge_adjacent_ind >>
  simp[merge_adjacent_def, mm_local_group_ids_def] >>
  rpt strip_tac >> Cases_on `copy_can_merge c1 c2` >>
  gvs[copy_merge_def, APPEND_ASSOC]
QED

Theorem mm_local_insert_ids_perm[local]:
  !cs cg. PERM (mm_local_group_ids (insert_sorted cs cg))
              (cg.cg_inst_ids ++ mm_local_group_ids cs)
Proof
  Induct_on `cs` >> simp[insert_sorted_def, mm_local_group_ids_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  irule PERM_TRANS >>
  qexists `h.cg_inst_ids ++ cg.cg_inst_ids ++
    FLAT (MAP (\cg. cg.cg_inst_ids) cs)` >>
  conj_tac >- (
    pure_rewrite_tac[GSYM APPEND_ASSOC, PERM_APPEND_IFF] >>
    gvs[mm_local_group_ids_def]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, PERM_SWAP_L_AT_FRONT] >> simp[]
QED

Theorem mm_local_add_ids_perm[local]:
  PERM (mm_local_group_ids (add_copy cs cg))
       (cg.cg_inst_ids ++ mm_local_group_ids cs)
Proof
  simp[add_copy_def, mm_local_merge_ids_exact, mm_local_insert_ids_perm]
QED

Theorem mm_local_partition_ids_perm[local]:
  !cs. PERM (mm_local_group_ids (FILTER Q cs) ++
             mm_local_group_ids (FILTER (\cg. ~Q cg) cs))
            (mm_local_group_ids cs)
Proof
  Induct_on `cs` >> simp[mm_local_group_ids_def] >>
  Cases_on `Q h`
  >- (simp[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, PERM_APPEND_IFF] >>
      gvs[mm_local_group_ids_def]) >>
  simp[] >> irule PERM_TRANS >>
  qexists `h.cg_inst_ids ++
    (FLAT (MAP (\cg. cg.cg_inst_ids) (FILTER Q cs)) ++
     FLAT (MAP (\cg. cg.cg_inst_ids) (FILTER (\cg. ~Q cg) cs)))` >>
  conj_tac >- simp[PERM_SWAP_L_AT_FRONT] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, PERM_APPEND_IFF] >>
  gvs[mm_local_group_ids_def]
QED

Theorem mm_local_flush_ids_perm[local]:
  PERM (mm_local_group_ids (flush_copies ss (FILTER Q ss.ss_copies)).ss_flushed ++
        mm_local_group_ids (flush_copies ss (FILTER Q ss.ss_copies)).ss_copies)
       (mm_local_group_ids ss.ss_flushed ++ mm_local_group_ids ss.ss_copies)
Proof
  simp[flush_copies_def, mm_local_group_ids_append, MEM_FILTER] >>
  `FILTER (\cg. ~(Q cg /\ MEM cg ss.ss_copies)) ss.ss_copies =
   FILTER (\cg. ~Q cg) ss.ss_copies` by
    (simp[rich_listTheory.FILTER_EQ]) >>
  simp[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, PERM_APPEND_IFF] >>
  gvs[mm_local_partition_ids_perm]
QED

Definition mm_local_scan_unique_def:
  mm_local_scan_unique proj todo ss <=>
    ALL_DISTINCT (FILTER proj (mm_local_group_ids ss.ss_flushed ++
                               mm_local_group_ids ss.ss_copies ++ todo))
End

Theorem mm_local_unique_perm[local]:
  PERM a b ==> (ALL_DISTINCT (FILTER proj (a ++ todo)) =
                 ALL_DISTINCT (FILTER proj (b ++ todo)))
Proof
  strip_tac >> irule ALL_DISTINCT_PERM >>
  irule PERM_FILTER >> simp[PERM_APPEND_IFF]
QED

Theorem mm_local_flush_unique[local]:
  mm_local_scan_unique proj todo (flush_copies ss (FILTER Q ss.ss_copies)) =
  mm_local_scan_unique proj todo ss
Proof
  simp[mm_local_scan_unique_def, APPEND_ASSOC] >>
  irule mm_local_unique_perm >> irule mm_local_flush_ids_perm
QED

Theorem mm_local_barrier_unique[local]:
  mm_local_scan_unique proj todo (hard_barrier ss) = mm_local_scan_unique proj todo ss
Proof
  simp[mm_local_scan_unique_def, hard_barrier_def,
       mm_local_group_ids_append, mm_local_group_ids_def, APPEND_ASSOC]
QED

Theorem mm_local_invalidate_unique[local]:
  mm_local_scan_unique proj todo (invalidate_loads ss iv) = mm_local_scan_unique proj todo ss
Proof
  simp[mm_local_scan_unique_def, invalidate_loads_def]
QED

Theorem mm_local_hazards_unique[local]:
  mm_local_scan_unique proj todo (flush_hazards mode ss cg) =
  mm_local_scan_unique proj todo ss
Proof
  simp[flush_hazards_def, waw_hazards_def, raw_hazards_def, war_hazards_def,
       copies_that_overwrite_def] >>
  rpt IF_CASES_TAC >> simp[mm_local_flush_unique]
QED

Theorem mm_local_add_unique[local]:
  ALL_DISTINCT (FILTER proj (cg.cg_inst_ids ++ mm_local_group_ids ss.ss_flushed ++
                            mm_local_group_ids ss.ss_copies ++ todo)) ==>
  mm_local_scan_unique proj todo (ss with ss_copies := add_copy ss.ss_copies cg)
Proof
  strip_tac >> simp[mm_local_scan_unique_def] >>
  `PERM (mm_local_group_ids ss.ss_flushed ++
         mm_local_group_ids (add_copy ss.ss_copies cg))
        (cg.cg_inst_ids ++ mm_local_group_ids ss.ss_flushed ++
         mm_local_group_ids ss.ss_copies)` by
    (irule PERM_TRANS >>
     qexists `mm_local_group_ids ss.ss_flushed ++
       (cg.cg_inst_ids ++ mm_local_group_ids ss.ss_copies)` >>
     conj_tac >- simp[PERM_APPEND_IFF, mm_local_add_ids_perm] >>
     simp[PERM_SWAP_L_AT_FRONT]) >>
  drule mm_local_unique_perm >>
  simp[]
QED

Theorem mm_local_unique_drop[local]:
  mm_local_scan_unique proj (id::todo) ss ==> mm_local_scan_unique proj todo ss
Proof
  simp[mm_local_scan_unique_def, FILTER_APPEND_DISTRIB, ALL_DISTINCT_APPEND] >>
  Cases_on `proj id` >> simp[] >> metis_tac[]
QED

Theorem mm_local_add_current_unique[local]:
  mm_local_scan_unique proj (id::todo) ss /\
  FILTER proj cg.cg_inst_ids = FILTER proj [id] ==>
  mm_local_scan_unique proj todo (ss with ss_copies := add_copy ss.ss_copies cg)
Proof
  strip_tac >> irule mm_local_add_unique >>
  gvs[mm_local_scan_unique_def, FILTER_APPEND_DISTRIB, ALL_DISTINCT_APPEND] >>
  Cases_on `proj id` >> gvs[MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_loads_update_unique[local]:
  mm_local_scan_unique proj todo (ss with ss_loads := loads) =
  mm_local_scan_unique proj todo ss
Proof
  simp[mm_local_scan_unique_def]
QED

Theorem mm_local_load_unique[local]:
  mm_local_scan_unique proj todo ss ==>
  mm_local_scan_unique proj todo (scan_load mode ss inst)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >- simp[scan_load_def, mm_local_barrier_unique] >>
  rename1 `inst.inst_operands = src::ops` >>
  Cases_on `ops`
  >- (
    Cases_on `operand_lit_val src`
    >- simp[scan_load_def, mm_local_barrier_unique] >>
    Cases_on `inst.inst_outputs`
    >- simp[scan_load_def, mm_local_barrier_unique] >>
    rename1 `inst.inst_outputs = out::outs` >>
    Cases_on `outs` >> simp[scan_load_def, mm_local_barrier_unique] >>
    rpt IF_CASES_TAC >>
    simp[mm_local_loads_update_unique, copies_that_overwrite_def,
         mm_local_flush_unique]) >>
  simp[scan_load_def, mm_local_barrier_unique]
QED

Theorem mm_local_store_unique[local]:
  mm_local_scan_unique proj (inst.inst_id::todo) ss /\
  (!v li. dfg_get_def dfg v = SOME li ==> ~proj li.inst_id) ==>
  mm_local_scan_unique proj todo (scan_store dfg mode ss inst)
Proof
  strip_tac >>
  `mm_local_scan_unique proj todo ss` by metis_tac[mm_local_unique_drop] >>
  Cases_on `inst.inst_operands`
  >- simp[scan_store_def, mm_local_barrier_unique] >>
  rename1 `inst.inst_operands = dst::ops` >>
  Cases_on `ops` >- simp[scan_store_def, mm_local_barrier_unique] >>
  rename1 `inst.inst_operands = dst::value::ops` >>
  Cases_on `ops`
  >- (
    Cases_on `dst` >> Cases_on `value` >>
    simp[scan_store_def, operand_var_name_def, operand_lit_val_def,
         mm_local_barrier_unique] >>
    rename1 `inst.inst_operands = [Lit addr; Var v]` >>
    Cases_on `FLOOKUP ss.ss_loads v`
    >- simp[mm_local_barrier_unique] >>
    simp[] >> irule mm_local_add_current_unique >>
    qexists `inst.inst_id` >>
    conj_tac
    >- (Cases_on `dfg_get_def dfg v` >> simp[] >>
        rename1 `dfg_get_def dfg v = SOME li` >>
        `~proj li.inst_id` by metis_tac[] >> simp[]) >>
    simp[mm_local_hazards_unique] >>
    IF_CASES_TAC >> simp[mm_local_invalidate_unique]) >>
  simp[scan_store_def, mm_local_barrier_unique]
QED

Theorem mm_local_bulk_unique[local]:
  mm_local_scan_unique proj (inst.inst_id::todo) ss ==>
  mm_local_scan_unique proj todo (scan_bulk_copy mode ss inst)
Proof
  strip_tac >>
  `mm_local_scan_unique proj todo ss` by metis_tac[mm_local_unique_drop] >>
  Cases_on `inst.inst_operands`
  >- simp[scan_bulk_copy_def, mm_local_barrier_unique] >>
  rename1 `inst.inst_operands = dst::ops` >>
  Cases_on `ops` >- simp[scan_bulk_copy_def, mm_local_barrier_unique] >>
  rename1 `inst.inst_operands = dst::src::ops` >>
  Cases_on `ops` >- simp[scan_bulk_copy_def, mm_local_barrier_unique] >>
  rename1 `inst.inst_operands = dst::src::len::ops` >>
  Cases_on `ops`
  >- (
    Cases_on `dst` >>
    simp[scan_bulk_copy_def, operand_lit_val_def, mm_local_barrier_unique] >>
    Cases_on `src` >> simp[operand_lit_val_def, mm_local_barrier_unique] >>
    Cases_on `len` >> simp[operand_lit_val_def, mm_local_barrier_unique] >>
    irule mm_local_add_current_unique >> qexists `inst.inst_id` >>
    simp[mm_local_hazards_unique] >>
    IF_CASES_TAC >> simp[mm_local_invalidate_unique]) >>
  simp[scan_bulk_copy_def, mm_local_barrier_unique]
QED

Theorem mm_local_inst_unique[local]:
  mm_local_scan_unique proj (inst.inst_id::todo) ss /\
  (!v li. dfg_get_def dfg v = SOME li ==> ~proj li.inst_id) ==>
  mm_local_scan_unique proj todo (scan_inst dfg mode ss inst)
Proof
  strip_tac >> simp[scan_inst_def] >> rpt IF_CASES_TAC >>
  metis_tac[mm_local_store_unique, mm_local_bulk_unique,
            mm_local_load_unique, mm_local_unique_drop, mm_local_barrier_unique]
QED

Theorem mm_local_fold_unique[local]:
  !xs ss. mm_local_scan_unique proj (MAP (\i. i.inst_id) xs ++ todo) ss /\
  (!v li. dfg_get_def dfg v = SOME li ==> ~proj li.inst_id) ==>
  mm_local_scan_unique proj todo (FOLDL (scan_inst dfg mode) ss xs)
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[mm_local_inst_unique]
QED

Theorem mm_local_scan_projected_unique[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  (!v li. dfg_get_def dfg v = SOME li ==> ~proj li.inst_id) ==>
  ALL_DISTINCT (FILTER proj
    (mm_local_group_ids (scan_block dfg mode bb).ss_flushed))
Proof
  strip_tac >>
  `mm_local_scan_unique proj [] (scan_block dfg mode bb)` by
    (simp[scan_block_def, mm_local_barrier_unique] >>
     irule mm_local_fold_unique >>
     simp[mm_local_scan_unique_def, empty_scan_state_def,
          mm_local_group_ids_def] >> metis_tac[FILTER_ALL_DISTINCT]) >>
  gvs[mm_local_scan_unique_def, FILTER_APPEND_DISTRIB, ALL_DISTINCT_APPEND]
QED

Theorem mm_local_projected_owner[local]:
  !groups a b. ALL_DISTINCT (FILTER proj (mm_local_group_ids groups)) /\
  proj id /\ MEM a groups /\ MEM b groups /\
  MEM id a.cg_inst_ids /\ MEM id b.cg_inst_ids ==> a = b
Proof
  Induct_on `groups` >> simp[mm_local_group_ids_def,
    FILTER_APPEND_DISTRIB, ALL_DISTINCT_APPEND, MEM_FILTER, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[mm_local_group_ids_def]
QED

Theorem mm_local_scan_group_owner[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  (!v li. dfg_get_def dfg v = SOME li ==> ~proj li.inst_id) /\
  proj id /\ MEM a (scan_block dfg mode bb).ss_flushed /\
  MEM b (scan_block dfg mode bb).ss_flushed /\
  MEM id a.cg_inst_ids /\ MEM id b.cg_inst_ids ==> a = b
Proof
  metis_tac[mm_local_scan_projected_unique, mm_local_projected_owner]
QED

Theorem mm_local_rep_member[local]:
  rep_of_group xs cg = SOME (id,other) ==>
  other = cg /\ MEM id cg.cg_inst_ids /\ MEM id (MAP (\i. i.inst_id) xs)
Proof
  simp[rep_of_group_def] >>
  Cases_on `REVERSE (sort_ids_by_block xs cg.cg_inst_ids)` >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `REVERSE (sort_ids_by_block xs cg.cg_inst_ids) = rep::tail` >>
  `MEM rep (REVERSE (sort_ids_by_block xs cg.cg_inst_ids))` by metis_tac[MEM] >>
  gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER]
QED

Theorem mm_local_memzero_rep_before_barrier[local]:
  bb.bb_instructions = pre ++ [i] ++ post /\
  ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions) /\
  is_volatile_memory i /\ ~is_zero_store i /\
  ~is_calldatasize_copy dfg i /\
  MEM cg (scan_block_memzero dfg bb).mz_flushed /\
  MEM id cg.cg_inst_ids /\ MEM id (MAP (\x. x.inst_id) pre) ==>
  ?r. rep_of_group bb.bb_instructions cg = SOME (r,cg) /\
      MEM r (MAP (\x. x.inst_id) pre)
Proof
  strip_tac >>
  drule_all mm_local_memzero_barrier_localization >> strip_tac
  >- (
    `FILTER (\id. MEM id cg.cg_inst_ids)
       (MAP (\x. x.inst_id) (i::post)) = []` by
      (simp[FILTER_EQ_NIL, EVERY_MEM] >>
       gvs[EVERY_MEM, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    `FILTER (\id. MEM id cg.cg_inst_ids)
       (MAP (\x. x.inst_id) pre) <> []` by
      (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
    gvs[AllCaseEqs()] >>
    simp[rep_of_group_def, sort_ids_by_block_def, MAP_APPEND,
         FILTER_APPEND_DISTRIB] >>
    Cases_on `REVERSE (FILTER (\id. MEM id cg.cg_inst_ids)
      (MAP (\x. x.inst_id) pre))` >> gvs[] >>
    `MEM h (REVERSE (FILTER (\id. MEM id cg.cg_inst_ids)
      (MAP (\x. x.inst_id) pre)))` by metis_tac[MEM] >>
    gvs[MEM_REVERSE, MEM_FILTER]) >>
  gvs[EVERY_MEM, ALL_DISTINCT_APPEND] >> metis_tac[]
QED
Theorem mm_local_rep_position_max[local]:
  !xs j k. ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  j < LENGTH xs /\ k < LENGTH xs /\
  MEM (EL j xs).inst_id cg.cg_inst_ids /\
  rep_of_group xs cg = SOME ((EL k xs).inst_id,cg) ==> j <= k
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `k` >- (
    Cases_on `j` >- simp[] >>
    gvs[] >>
    `FILTER (\id. MEM id cg.cg_inst_ids) (MAP (\i. i.inst_id) xs) <> []` by
      (simp[FILTER_EQ_NIL, EVERY_MEM] >> qexists `(EL n xs).inst_id` >>
       simp[MEM_MAP] >> qexists `EL n xs` >> simp[EL_MEM]) >>
    gvs[rep_of_group_def, sort_ids_by_block_def] >>
    Cases_on `REVERSE (FILTER (\id. MEM id cg.cg_inst_ids)
      (MAP (\i. i.inst_id) xs))` >>
    gvs[REVERSE_APPEND] >>
    Cases_on `MEM h.inst_id cg.cg_inst_ids` >> gvs[REVERSE_APPEND] >>
    `MEM h.inst_id (REVERSE (FILTER (\id. MEM id cg.cg_inst_ids)
      (MAP (\i. i.inst_id) xs)))` by metis_tac[MEM] >>
    gvs[MEM_REVERSE, MEM_FILTER]) >>
  Cases_on `j` >- simp[] >> gvs[] >>
  `rep_of_group xs cg = SOME ((EL n xs).inst_id,cg)` by
    (gvs[rep_of_group_def, sort_ids_by_block_def] >>
     Cases_on `MEM h.inst_id cg.cg_inst_ids` >> gvs[REVERSE_APPEND] >>
     Cases_on `REVERSE (FILTER (\id. MEM id cg.cg_inst_ids)
       (MAP (\i. i.inst_id) xs))` >> gvs[] >>
     qpat_x_assum `~MEM _ (MAP _ xs)` mp_tac >>
     simp[MEM_MAP] >> qexists `EL n xs` >> simp[EL_MEM]) >>
  metis_tac[]
QED
Theorem mm_local_memzero_barrier_position[local]:
  bb.bb_instructions = pre ++ [i] ++ post /\
  ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions) /\
  is_volatile_memory i /\ ~is_zero_store i /\
  ~is_calldatasize_copy dfg i /\
  MEM cg (scan_block_memzero dfg bb).mz_flushed /\
  MEM id cg.cg_inst_ids /\ MEM id (MAP (\x. x.inst_id) pre) ==>
  ?k. k < LENGTH pre /\
      rep_of_group bb.bb_instructions cg =
        SOME ((EL k bb.bb_instructions).inst_id,cg) /\
      (!j. j < LENGTH bb.bb_instructions /\
           MEM (EL j bb.bb_instructions).inst_id cg.cg_inst_ids ==> j <= k)
Proof
  strip_tac >> drule_all mm_local_memzero_rep_before_barrier >>
  strip_tac >>
  qpat_x_assum `MEM r (MAP _ pre)` mp_tac >>
  simp[MEM_EL] >> strip_tac >>
  qexists `n` >>
  `n < LENGTH bb.bb_instructions /\
   (EL n bb.bb_instructions).inst_id = r` by
    (gvs[] >> simp[EL_APPEND_EQN, EL_MAP]) >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule mm_local_rep_position_max >>
  qexistsl [`cg`, `bb.bb_instructions`] >>
  gvs[] >> simp[MEM_EL] >> metis_tac[]
QED



Theorem mm_local_rep_lookup[local]:
  !groups cg. ALL_DISTINCT (FILTER proj (mm_local_group_ids groups)) /\
  proj id /\ MEM cg groups /\ rep_of_group xs cg = SOME (id,cg) ==>
  ALOOKUP (rep_map_of_groups xs groups) id = SOME cg
Proof
  Induct_on `groups` >- simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `cg = h`
  >- gvs[rep_map_of_groups_def] >>
  `MEM cg groups` by gvs[] >>
  `ALOOKUP (rep_map_of_groups xs groups) id = SOME cg` by
    (first_x_assum irule >>
     gvs[mm_local_group_ids_def, FILTER_APPEND_DISTRIB, ALL_DISTINCT_APPEND]) >>
  Cases_on `rep_of_group xs h`
  >- gvs[rep_map_of_groups_def] >>
  rename1 `rep_of_group xs h = SOME result` >>
  PairCases_on `result` >>
  drule mm_local_rep_member >> strip_tac >> gvs[] >>
  `result0 <> id` by
    (strip_tac >> gvs[] >>
     imp_res_tac mm_local_rep_member >>
     `h = cg` by (irule mm_local_projected_owner >>
       qexistsl [`h::groups`, `id`, `proj`] >> simp[]) >> gvs[]) >>
  gvs[rep_map_of_groups_def]
QED

Theorem mm_local_scan_rep_lookup[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  (!v li. dfg_get_def dfg v = SOME li ==> ~proj li.inst_id) /\
  proj id /\ MEM cg (scan_block dfg mode bb).ss_flushed /\
  rep_of_group bb.bb_instructions cg = SOME (id,cg) ==>
  ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block dfg mode bb).ss_flushed) id = SOME cg
Proof
  metis_tac[mm_local_scan_projected_unique, mm_local_rep_lookup]
QED

Theorem mm_local_retained_store_rep_or_pin[local]:
  MEM st xs /\ st.inst_opcode = MSTORE /\
  dfg_get_inst_by_id dfg st.inst_id = SOME st /\
  MEM cg groups /\ MEM st.inst_id cg.cg_inst_ids /\
  ~MEM st.inst_id (nop_ids_of_groups dfg mode xs groups) ==>
  ?rep. rep_of_group xs cg = SOME (rep,cg) /\
    (rep = st.inst_id \/ rep_pin_id dfg mode rep cg = SOME st.inst_id)
Proof
  strip_tac >>
  `MEM st.inst_id (sort_ids_by_block xs cg.cg_inst_ids)` by
    (simp[sort_ids_by_block_def, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  `~MEM st.inst_id (nop_ids_of_group dfg mode xs cg)` by
    (gvs[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  Cases_on `REVERSE (sort_ids_by_block xs cg.cg_inst_ids)`
  >- metis_tac[MEM_REVERSE, MEM] >>
  rename1 `REVERSE (sort_ids_by_block xs cg.cg_inst_ids) = rep::earlier` >>
  qexists `rep` >> simp[rep_of_group_def] >>
  Cases_on `rep = st.inst_id` >- simp[] >>
  `MEM st.inst_id earlier` by metis_tac[MEM_REVERSE, MEM] >>
  qpat_x_assum `~MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
  simp[nop_ids_of_group_def, MEM_FILTER, MEM_REVERSE] >>
  gvs[]
QED

Theorem mm_local_retained_store_rep[local]:
  MEM st xs /\ st.inst_opcode = MSTORE /\
  dfg_get_inst_by_id dfg st.inst_id = SOME st /\
  MEM cg groups /\ MEM st.inst_id cg.cg_inst_ids /\
  ~MEM st.inst_id (nop_ids_of_groups dfg mode xs groups) /\
  (!rep. rep_pin_id dfg mode rep cg <> SOME st.inst_id) ==>
  rep_of_group xs cg = SOME (st.inst_id,cg)
Proof
  metis_tac[mm_local_retained_store_rep_or_pin]
QED

Theorem mm_local_deleted_unpinned[local]:
  MEM id (nop_ids_of_group dfg mode insts cg) ==>
  ?rep. rep_of_group insts cg = SOME (rep,cg) /\
        rep_pin_id dfg mode rep cg <> SOME id
Proof
  simp[nop_ids_of_group_def, rep_of_group_def] >>
  Cases_on `REVERSE (sort_ids_by_block insts cg.cg_inst_ids)` >>
  simp[MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_deleted_load_users[local]:
  dfg_get_inst_by_id dfg id = SOME load /\
  load.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} /\
  load.inst_outputs = [v] /\
  MEM id (nop_ids_of_group dfg mode insts cg) ==>
  EVERY (\u. MEM u.inst_id cg.cg_inst_ids) (dfg_get_uses dfg v)
Proof
  simp[nop_ids_of_group_def] >>
  Cases_on `REVERSE (sort_ids_by_block insts cg.cg_inst_ids)` >>
  simp[MEM_FILTER, load_safe_to_nop_def] >> strip_tac >> gvs[]
QED

Theorem mm_local_deleted_load_certificate[local]:
  dfg_get_inst_by_id dfg id = SOME load /\
  load.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} /\
  load.inst_outputs = [v] /\
  MEM id (nop_ids_of_groups dfg mode insts groups) ==>
  ?cg rep. MEM cg groups /\
    rep_of_group insts cg = SOME (rep,cg) /\
    rep_pin_id dfg mode rep cg <> SOME id /\
    EVERY (\u. MEM u.inst_id cg.cg_inst_ids) (dfg_get_uses dfg v)
Proof
  strip_tac >>
  qpat_x_assum `MEM id (nop_ids_of_groups _ _ _ _)` mp_tac >>
  simp[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >> strip_tac >> gvs[] >>
  drule mm_local_deleted_load_users >> simp[] >> strip_tac >>
  drule mm_local_deleted_unpinned >> strip_tac >>
  metis_tac[]
QED

Theorem mm_local_load_protected[local]:
  dfg_get_inst_by_id dfg id = SOME load /\
  load.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} /\
  load.inst_outputs = [v] /\
  (!cg. MEM cg groups ==>
    (?rep. rep_of_group insts cg = SOME (rep,cg) /\
           rep_pin_id dfg mode rep cg = SOME id) \/
    (?u. MEM u (dfg_get_uses dfg v) /\ ~MEM u.inst_id cg.cg_inst_ids)) ==>
  ~MEM id (nop_ids_of_groups dfg mode insts groups)
Proof
  strip_tac >> strip_tac >>
  drule_all mm_local_deleted_load_certificate >> strip_tac >>
  qpat_x_assum `!cg. MEM cg groups ==> _` drule >>
  strip_tac >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem mm_local_phase_other_load_origin[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) /\ phase <> SOME other /\
  MEM i cc.bb_instructions /\ i.inst_opcode = mode_load_opcode other ==>
  MEM i bb.bb_instructions
Proof
  Cases_on `phase` >> simp[mm_local_phase_def] >>
  metis_tac[transform_block_memzero_supply_load_origin,
    transform_block_mode_supply_other_load_origin]
QED

Theorem mm_local_memzero_list_use_origin[local]:
  !xs s ys t j v.
  mm_flat_map_supply (apply_memzero_inst_supply ns rm) s xs = (ys,t) /\
  j < LENGTH ys /\ MEM v (venomInst$inst_uses (EL j ys)) ==>
  MEM (EL j ys) xs \/
  (0 < j /\ (EL (j - 1) ys).inst_outputs = [v] /\
   venomInst$inst_uses (EL (j - 1) ys) = [] /\
   venomInst$inst_uses (EL j ys) = [v])
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >>
  simp[Once mm_flat_map_supply_def, AllCaseEqs()] >> strip_tac >>
  rename1 `apply_memzero_inst_supply ns rm s h = (out,s1)` >>
  Cases_on `j < LENGTH out`
  >- (
    qpat_x_assum `apply_memzero_inst_supply _ _ _ _ = _` mp_tac >>
    simp[apply_memzero_inst_supply_def, AllCaseEqs()] >> strip_tac >>
    gvs[EL_APPEND_EQN, mk_nop_from_def, mk_zero_store_inst_def,
        mk_memzero_calldatacopy_def, venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
        venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def, venomInstTheory.operand_var_def] >>
    `j = 0 \/ j = 1` by decide_tac >>
    gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def, venomInstTheory.operand_var_def]) >>
  `j - LENGTH out < LENGTH outs` by (gvs[] >> decide_tac) >>
  `MEM v (venomInst$inst_uses (EL (j - LENGTH out) outs))` by
    gvs[EL_APPEND_EQN] >>
  first_x_assum drule >> disch_then drule >> disch_then drule >>
  strip_tac >- gvs[EL_APPEND_EQN] >>
  `0 < j /\ ~(j - 1 < LENGTH out) /\
   j - 1 - LENGTH out = j - LENGTH out - 1` by decide_tac >>
  gvs[EL_APPEND_EQN]
QED

Theorem mm_local_mode_list_use_origin[local]:
  !xs s ys t j v.
  mm_flat_map_supply (apply_groups_inst_supply mode ns rm) s xs = (ys,t) /\
  j < LENGTH ys /\ MEM v (venomInst$inst_uses (EL j ys)) ==>
  MEM (EL j ys) xs \/
  (0 < j /\ (EL (j - 1) ys).inst_outputs = [v] /\
   venomInst$inst_uses (EL (j - 1) ys) = [] /\
   venomInst$inst_uses (EL j ys) = [v])
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >>
  simp[Once mm_flat_map_supply_def, AllCaseEqs()] >> strip_tac >>
  rename1 `apply_groups_inst_supply mode ns rm s h = (out,s1)` >>
  Cases_on `j < LENGTH out`
  >- (
    qpat_x_assum `apply_groups_inst_supply _ _ _ _ _ = _` mp_tac >>
    simp[apply_groups_inst_supply_def, AllCaseEqs()] >> strip_tac >>
    gvs[EL_APPEND_EQN, mk_nop_from_def, mk_bulk_copy_inst_def,
        mk_load_inst_def, mk_mstore_from_load_def,
        venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def, venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
        venomInstTheory.operand_var_def] >>
    `j = 0 \/ j = 1` by decide_tac >>
    gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def, venomInstTheory.operand_var_def]) >>
  `j - LENGTH out < LENGTH outs` by (gvs[] >> decide_tac) >>
  `MEM v (venomInst$inst_uses (EL (j - LENGTH out) outs))` by
    gvs[EL_APPEND_EQN] >>
  first_x_assum drule >> disch_then drule >> disch_then drule >>
  strip_tac >- gvs[EL_APPEND_EQN] >>
  `0 < j /\ ~(j - 1 < LENGTH out) /\
   j - 1 - LENGTH out = j - LENGTH out - 1` by decide_tac >>
  gvs[EL_APPEND_EQN]
QED

Theorem mm_local_phase_use_origin[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) /\
  j < LENGTH cc.bb_instructions /\
  MEM v (venomInst$inst_uses (EL j cc.bb_instructions)) ==>
  MEM (EL j cc.bb_instructions) bb.bb_instructions \/
  (0 < j /\ (EL (j - 1) cc.bb_instructions).inst_outputs = [v] /\
   venomInst$inst_uses (EL (j - 1) cc.bb_instructions) = [] /\
   venomInst$inst_uses (EL j cc.bb_instructions) = [v])
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[mm_local_memzero_list_use_origin, mm_local_mode_list_use_origin]
QED

Theorem mm_local_pending_load_origin[local]:
  !fn0 supply index k bb sk mode i.
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  MEM i bb.bb_instructions /\ i.inst_opcode = mode_load_opcode mode ==>
  MEM i (EL index fn0.fn_blocks).bb_instructions
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >>
  gvs[] >>
  drule mm_local_phase_other_load_origin >>
  simp[] >> strip_tac >> metis_tac[merge_mode_distinct]
QED

Theorem mm_local_phase_ids[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
  mm_local_phase dfg phase (bb,s) = (cc,t) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) cc.bb_instructions) /\
  s.irs_next_inst <= t.irs_next_inst /\
  EVERY (\i. i.inst_id < t.irs_next_inst) cc.bb_instructions /\
  (!i. MEM i cc.bb_instructions ==>
    MEM i.inst_id (MAP (\j. j.inst_id) bb.bb_instructions) \/
    (s.irs_next_inst <= i.inst_id /\ i.inst_id < t.irs_next_inst))
Proof
  Cases_on `phase` >> simp[mm_local_phase_def] >>
  metis_tac[transform_block_memzero_supply_ids, transform_block_mode_supply_ids]
QED

Theorem mm_local_prefix_ids[local]:
  !fn0 supply index k bb sk.
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions) /\
  EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  supply.irs_next_inst <= sk.irs_next_inst /\
  EVERY (\i. i.inst_id < sk.irs_next_inst) bb.bb_instructions /\
  (!i. MEM i bb.bb_instructions ==>
    MEM i.inst_id (MAP (\j. j.inst_id) (EL index fn0.fn_blocks).bb_instructions) \/
    (supply.irs_next_inst <= i.inst_id /\ i.inst_id < sk.irs_next_inst))
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- (simp[mm_local_prefix_zero] >> metis_tac[MEM_MAP]) >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) prev.bb_instructions) /\
   supply.irs_next_inst <= sp.irs_next_inst /\
   EVERY (\i. i.inst_id < sp.irs_next_inst) prev.bb_instructions /\
   (!i. MEM i prev.bb_instructions ==>
     MEM i.inst_id (MAP (\j. j.inst_id) (EL index fn0.fn_blocks).bb_instructions) \/
     (supply.irs_next_inst <= i.inst_id /\ i.inst_id < sp.irs_next_inst))`
    by (first_x_assum irule >> simp[]) >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  drule_all mm_local_phase_ids >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  conj_tac >- simp[] >>
  rpt strip_tac >> irule inst_id_interval_compose >>
  qexistsl [`sp.irs_next_inst`, `prev.bb_instructions`, `bb.bb_instructions`] >> simp[]
QED

Theorem mm_local_mode_old_output[local]:
  apply_groups_inst_supply mode ns rm s i = (out,t) ==>
  s.irs_next_inst <= t.irs_next_inst /\
  (!j. MEM j out /\ j.inst_outputs <> [] /\ j.inst_id < s.irs_next_inst ==> j = i)
Proof
  simp[apply_groups_inst_supply_def] >>
  Cases_on `MEM i.inst_id ns` >> simp[] >>
  Cases_on `ALOOKUP rm i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[irSupplyTheory.fresh_inst_id_def, irSupplyTheory.fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def] >> rpt strip_tac >> gvs[]
QED

Theorem mm_local_memzero_old_output[local]:
  apply_memzero_inst_supply ns rm s i = (out,t) ==>
  s.irs_next_inst <= t.irs_next_inst /\
  (!j. MEM j out /\ j.inst_outputs <> [] /\ j.inst_id < s.irs_next_inst ==> j = i)
Proof
  simp[apply_memzero_inst_supply_def] >>
  Cases_on `MEM i.inst_id ns` >> simp[] >>
  Cases_on `ALOOKUP rm i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[irSupplyTheory.fresh_inst_id_def, irSupplyTheory.fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem mm_local_list_old_output[local]:
  !f xs s ys t.
  (!u i out v. f u i = (out,v) ==>
    u.irs_next_inst <= v.irs_next_inst /\
    (!j. MEM j out /\ j.inst_outputs <> [] /\ j.inst_id < u.irs_next_inst ==> j = i)) /\
  mm_flat_map_supply f s xs = (ys,t) ==>
  s.irs_next_inst <= t.irs_next_inst /\
  (!j. MEM j ys /\ j.inst_outputs <> [] /\ j.inst_id < s.irs_next_inst ==> MEM j xs)
Proof
  gen_tac >> Induct >> simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `!u i out v. _` drule >> strip_tac >>
  qpat_x_assum `!s ys t. _` (qspecl_then [`s1`, `outs`, `t`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[])) >> strip_tac >>
  simp[MEM_APPEND] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem mm_local_phase_old_output[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) ==>
  s.irs_next_inst <= t.irs_next_inst /\
  (!j. MEM j cc.bb_instructions /\ j.inst_outputs <> [] /\
       j.inst_id < s.irs_next_inst ==> MEM j bb.bb_instructions)
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_local_list_old_output >>
  (impl_tac >- metis_tac[mm_local_memzero_old_output, mm_local_mode_old_output]) >>
  simp[]
QED

Theorem mm_local_prefix_old_output[local]:
  !fn0 supply index k bb sk.
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) ==>
  supply.irs_next_inst <= sk.irs_next_inst /\
  (!i. MEM i bb.bb_instructions /\ i.inst_outputs <> [] /\
    i.inst_id < supply.irs_next_inst ==>
    MEM i (EL index fn0.fn_blocks).bb_instructions)
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `supply.irs_next_inst <= sp.irs_next_inst /\
   (!i. MEM i prev.bb_instructions /\ i.inst_outputs <> [] /\
     i.inst_id < supply.irs_next_inst ==>
     MEM i (EL index fn0.fn_blocks).bb_instructions)`
    by (first_x_assum irule >> simp[]) >>
  drule mm_local_phase_old_output >> strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem mm_local_prefix_id_distinct[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions) /\
  EVERY (\i. i.inst_id < supply.irs_next_inst) (EL index fn0.fn_blocks).bb_instructions ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  metis_tac[mm_local_prefix_ids]
QED

Theorem mm_local_prefix_id_mono[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) ==>
  supply.irs_next_inst <= sk.irs_next_inst
Proof
  metis_tac[mm_local_prefix_old_output]
QED

Theorem mm_local_prefix_id_bound[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions) /\
  EVERY (\i. i.inst_id < supply.irs_next_inst) (EL index fn0.fn_blocks).bb_instructions ==>
  EVERY (\i. i.inst_id < sk.irs_next_inst) bb.bb_instructions
Proof
  metis_tac[mm_local_prefix_ids]
QED

Theorem mm_local_prefix_id_origin[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions) /\
  EVERY (\i. i.inst_id < supply.irs_next_inst) (EL index fn0.fn_blocks).bb_instructions /\
  MEM i bb.bb_instructions ==>
  MEM i.inst_id (MAP (\j. j.inst_id) (EL index fn0.fn_blocks).bb_instructions) \/
  (supply.irs_next_inst <= i.inst_id /\ i.inst_id < sk.irs_next_inst)
Proof
  metis_tac[mm_local_prefix_ids]
QED

Theorem mm_local_prefix_output_origin[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM i bb.bb_instructions /\ i.inst_outputs <> [] /\
  i.inst_id < supply.irs_next_inst ==>
  MEM i (EL index fn0.fn_blocks).bb_instructions
Proof
  metis_tac[mm_local_prefix_old_output]
QED

Theorem mm_local_prefix_phi_origin[local]:
  !fn0 supply index k bb sk i.
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
  MEM i (EL index fn0.fn_blocks).bb_instructions
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `MEM i prev.bb_instructions` by
    (Cases_on `EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]` >>
     gvs[mm_local_phase_def] >>
     metis_tac[transform_block_memzero_supply_phi_origin,
       transform_block_mode_supply_phi_origin]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem mm_local_prefix_wf_last[local]:
  !fn0 supply index k bb sk.
  fn_inst_wf fn0 /\ wf_function fn0 /\ ssa_form fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions /\
  mm_local_prefix fn0 supply index k = (bb,sk) ==>
  bb_well_formed bb /\
  LAST bb.bb_instructions = LAST (EL index fn0.fn_blocks).bb_instructions /\
  bb.bb_label = (EL index fn0.fn_blocks).bb_label
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- (simp[mm_local_prefix_zero] >> rpt strip_tac >>
      gvs[wf_function_def] >> metis_tac[MEM_EL]) >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `bb_well_formed prev /\
   LAST prev.bb_instructions = LAST (EL index fn0.fn_blocks).bb_instructions /\
   prev.bb_label = (EL index fn0.fn_blocks).bb_label` by
    (first_x_assum irule >> simp[]) >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `fn_inst_ids_distinct fn0 /\ MEM (EL index fn0.fn_blocks) fn0.fn_blocks` by
    (gvs[wf_function_def] >> metis_tac[MEM_EL]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) prev.bb_instructions)` by
    (irule mm_local_prefix_id_distinct >>
     qexistsl [`fn0`, `index`, `k`, `sp`, `supply`] >>
     simp[] >> metis_tac[mmWfProofsTheory.fn_inst_ids_distinct_block]) >>
  `!i. MEM i prev.bb_instructions /\
       i.inst_id = (LAST prev.bb_instructions).inst_id ==>
       i = LAST prev.bb_instructions` by
    (gvs[bb_well_formed_def] >>
     metis_tac[mmWfProofsTheory.all_distinct_map_inv, MEM_LAST_NOT_NIL]) >>
  `MEM (LAST prev.bb_instructions) (fn_insts fn0)` by
    (irule mmWfProofsTheory.fn_insts_mem_block >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[] >>
     `bb_well_formed (EL index fn0.fn_blocks)` by
       metis_tac[wf_function_def] >>
     qpat_x_assum `bb_well_formed (EL index _)` mp_tac >>
     simp[bb_well_formed_def] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  `k <= 4` by decide_tac >>
  `!i. MEM i prev.bb_instructions /\ i.inst_opcode = PHI ==>
       MEM i (fn_insts fn0)` by
    (rpt strip_tac >> irule mmWfProofsTheory.fn_insts_mem_block >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[] >>
     metis_tac[mm_local_prefix_phi_origin]) >>
  `bb.bb_label = prev.bb_label` by metis_tac[mm_local_phase_label] >>
  Cases_on `EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]`
  >- (gvs[mm_local_phase_def] >>
      metis_tac[transform_block_memzero_supply_wf,
        transform_block_memzero_supply_last]) >>
  rename1 `EL k _ = SOME mode` >>
  `MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])` by
    (`k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >> gvs[]) >>
  `!i. MEM i prev.bb_instructions /\ i.inst_opcode = mode_load_opcode mode /\
       i.inst_outputs <> [] ==> MEM i (fn_insts fn0)` by
    (rpt strip_tac >> irule mmWfProofsTheory.fn_insts_mem_block >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[] >>
     metis_tac[mm_local_pending_load_origin]) >>
  gvs[mm_local_phase_def] >>
  `!p i. MEM p prev.bb_instructions /\ p.inst_opcode = PHI /\
    MEM i prev.bb_instructions /\ i.inst_id = p.inst_id ==> i = p` by
    metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  conj_tac
  >- (irule transform_block_mode_supply_wf >>
      qexistsl [`prev`, `dfg_build_function fn0`, `fn0`, `mode`, `sp`, `sk`] >>
      simp[]) >>
  `LAST bb.bb_instructions = LAST prev.bb_instructions` suffices_by simp[] >>
  drule_at (Pat `transform_block_mode_supply _ _ _ _ = _`)
    transform_block_mode_supply_last >>
  disch_then (qspec_then `fn0` mp_tac) >> simp[]
QED

Theorem mm_local_prefix_cfg_shape[local]:
  fn_inst_wf fn0 /\ wf_function fn0 /\ ssa_form fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions /\
  mm_local_prefix fn0 supply index k = (bb,sk) ==>
  MAP (\b. (b.bb_label, bb_succs b)) (LUPDATE bb index fn0.fn_blocks) =
  MAP (\b. (b.bb_label, bb_succs b)) fn0.fn_blocks
Proof
  strip_tac >> drule_all mm_local_prefix_wf_last >> strip_tac >>
  `bb_succs bb = bb_succs (EL index fn0.fn_blocks)` by
    (`bb.bb_instructions <> [] /\
      (EL index fn0.fn_blocks).bb_instructions <> []` by
       (metis_tac[wf_function_def, MEM_EL, bb_well_formed_def]) >>
     simp[venomInstTheory.bb_succs_def] >>
     Cases_on `bb.bb_instructions` >>
     Cases_on `(EL index fn0.fn_blocks).bb_instructions` >> gvs[]) >>
  simp[LUPDATE_MAP] >>
  `((\b. (b.bb_label, bb_succs b)) bb) =
   EL index (MAP (\b. (b.bb_label, bb_succs b)) fn0.fn_blocks)` by
    simp[EL_MAP] >>
  gvs[LUPDATE_SAME]
QED

Theorem mm_local_prefix_cfg_transport[local]:
  fn_inst_wf fn0 /\ wf_function fn0 /\ ssa_form fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks ==>
  fn_labels fn = fn_labels fn0 /\
  fn_entry_label fn = fn_entry_label fn0 /\
  fn_cfg_edge fn = fn_cfg_edge fn0 /\
  (!l. fn_reachable fn l <=> fn_reachable fn0 l) /\
  (!d n. fn_dominates fn d n <=> fn_dominates fn0 d n) /\
  (all_reachable fn <=> all_reachable fn0)
Proof
  strip_tac >>
  `MAP (\b. (b.bb_label, bb_succs b)) fn.fn_blocks =
   MAP (\b. (b.bb_label, bb_succs b)) fn0.fn_blocks` by
    (gvs[] >> irule mm_local_prefix_cfg_shape >> metis_tac[]) >>
  `fn_cfg_edge fn = fn_cfg_edge fn0` by
    (irule cfg_blocks_edges >> simp[]) >>
  `fn_labels fn = fn_labels fn0` by
    (pure_rewrite_tac[venomInstTheory.fn_labels_def] >>
     metis_tac[makeSsaCurrentCfgTheory.block_succs_map_labels]) >>
  `fn_entry_label fn = fn_entry_label fn0` by
    simp[makeSsaCurrentCfgTheory.succs_map_cfg_edge] >>
  `!l d n. (fn_reachable fn l <=> fn_reachable fn0 l) /\
    (fn_dominates fn d n <=> fn_dominates fn0 d n)` by
    (rpt gen_tac >> irule current_wf_cfg_dominance >> simp[]) >>
  `all_reachable fn <=> all_reachable fn0` by
    (qpat_x_assum `fn = _` kall_tac >>
     pure_rewrite_tac[all_reachable_def] >>
     `!l. MEM l (fn_labels fn) <=> MEM l (fn_labels fn0)` by simp[] >>
     fs[venomInstTheory.fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

Theorem mm_local_flat_map_supply_member[local]:
  !xs s ys t q.
  mm_flat_map_supply f s xs = (ys,t) /\ MEM q xs /\
  (!r out z. f r q = (out,z) ==> MEM q out) ==> MEM q ys
Proof
  Induct_on `xs` >> simp[mm_flat_map_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_APPEND]
QED

Theorem mm_local_flat_map_supply_order[local]:
  !xs s ys t a b q u.
  mm_flat_map_supply f s xs = (ys,t) /\
  a < b /\ b < LENGTH xs /\ EL a xs = q /\ EL b xs = u /\
  (!r out z. f r q = (out,z) ==> MEM q out) /\
  (!r out z. f r u = (out,z) ==> MEM u out) ==>
  ?c d. c < d /\ d < LENGTH ys /\ EL c ys = q /\ EL d ys = u
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> simp[Once mm_flat_map_supply_def, AllCaseEqs()] >> strip_tac >>
  rename1 `f s h = (out,s1)` >>
  Cases_on `a`
  >- (Cases_on `b` >- gvs[] >> gvs[] >>
      `MEM h out` by metis_tac[] >>
      `MEM (EL n xs) outs` by
        (irule mm_local_flat_map_supply_member >>
         metis_tac[MEM_EL]) >>
      gvs[MEM_EL] >>
      rename1 `c < LENGTH out` >> rename1 `d < LENGTH outs` >>
      qexistsl [`c`, `LENGTH out + d`] >> simp[EL_APPEND_EQN] >> decide_tac) >>
  Cases_on `b` >- gvs[] >>
  gvs[] >>
  qpat_x_assum `!s ys t a b. _` (qspecl_then [`s1`, `outs`, `t`, `n`, `n'`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl [`LENGTH out + c`, `LENGTH out + d`] >>
  simp[EL_APPEND_EQN]
QED

Theorem mm_local_memzero_chunk_use[local]:
  apply_memzero_inst_supply ns rm s i = (out,t) /\
  j < LENGTH out /\ MEM v (venomInst$inst_uses (EL j out)) ==>
  (EL j out = i /\ MEM v (venomInst$inst_uses i)) \/
  (?a. a < j /\ MEM v (EL a out).inst_outputs)
Proof
  simp[apply_memzero_inst_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def,
      mk_memzero_calldatacopy_def, venomInstTheory.inst_uses_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
  `j = 0 \/ j = 1` by decide_tac >>
  gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
  qexists_tac `0` >> simp[]
QED

Theorem mm_local_mode_chunk_use[local]:
  apply_groups_inst_supply mode ns rm s i = (out,t) /\
  j < LENGTH out /\ MEM v (venomInst$inst_uses (EL j out)) ==>
  (EL j out = i /\ MEM v (venomInst$inst_uses i)) \/
  (?a. a < j /\ MEM v (EL a out).inst_outputs)
Proof
  simp[apply_groups_inst_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def, venomInstTheory.inst_uses_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
  `j = 0 \/ j = 1` by decide_tac >>
  gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
  qexists_tac `0` >> simp[]
QED


Theorem mm_local_flat_map_supply_use_order[local]:
  (!s i out t j v.
    f s i = (out,t) /\ j < LENGTH out /\
    MEM v (venomInst$inst_uses (EL j out)) ==>
    (EL j out = i /\ MEM v (venomInst$inst_uses i)) \/
    (?a. a < j /\ MEM v (EL a out).inst_outputs)) ==>
  !xs s ys t j v.
  mm_flat_map_supply f s xs = (ys,t) /\ j < LENGTH ys /\
  MEM v (venomInst$inst_uses (EL j ys)) ==>
  (?b r chunk z. b < LENGTH xs /\ f r (EL b xs) = (chunk,z) /\
    MEM (EL j ys) chunk /\ EL j ys = EL b xs /\
    MEM v (venomInst$inst_uses (EL b xs)) /\
    (!q. MEM q (TAKE b xs) /\
      (!r out z. f r q = (out,z) ==> MEM q out) ==>
      ?c. c < j /\ EL c ys = q)) \/
  (?a. a < j /\ MEM v (EL a ys).inst_outputs)
Proof
  strip_tac >> Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >>
  simp[Once mm_flat_map_supply_def, AllCaseEqs()] >> strip_tac >>
  rename1 `f s h = (out,s1)` >>
  Cases_on `j < LENGTH out`
  >- (gvs[EL_APPEND_EQN] >>
      qpat_x_assum `!s i out t j v. _` drule >>
      disch_then drule >> disch_then drule >> strip_tac
      >- (disj1_tac >> qexistsl [`0`, `s`, `out`, `s1`] >> simp[] >>
          metis_tac[MEM_EL]) >>
      disj2_tac >> qexists_tac `a` >> simp[EL_APPEND_EQN]) >>
  `j - LENGTH out < LENGTH outs` by (gvs[] >> decide_tac) >>
  `MEM v (venomInst$inst_uses (EL (j - LENGTH out) outs))` by
    gvs[EL_APPEND_EQN] >>
  first_x_assum drule >> disch_then drule >> disch_then drule >> strip_tac
  >- (disj1_tac >> qexistsl [`SUC b`, `r`, `chunk`, `z`] >>
      gvs[EL_APPEND_EQN] >> rpt strip_tac >>
      gvs[TAKE_def]
      >- (`MEM h out` by metis_tac[] >>
          qpat_x_assum `MEM h out` (mp_tac o REWRITE_RULE [MEM_EL]) >>
          disch_then (qx_choose_then `pos` strip_assume_tac) >>
          qexists_tac `pos` >> simp[EL_APPEND_EQN] >> decide_tac) >>
      first_x_assum drule >> disch_then drule >> strip_tac >>
      qexists_tac `LENGTH out + c` >> simp[EL_APPEND_EQN] >> decide_tac) >>
  disj2_tac >> qexists_tac `LENGTH out + a` >>
  gvs[EL_APPEND_EQN] >> decide_tac
QED

Theorem mm_local_flat_map_supply_use[local]:
  (!s i out t j v.
    f s i = (out,t) /\ j < LENGTH out /\
    MEM v (venomInst$inst_uses (EL j out)) ==>
    (EL j out = i /\ MEM v (venomInst$inst_uses i)) \/
    (?a. a < j /\ MEM v (EL a out).inst_outputs)) ==>
  !xs s ys t j v.
  mm_flat_map_supply f s xs = (ys,t) /\ j < LENGTH ys /\
  MEM v (venomInst$inst_uses (EL j ys)) ==>
  (?i r chunk z. MEM i xs /\ f r i = (chunk,z) /\
    MEM (EL j ys) chunk /\ EL j ys = i /\
    MEM v (venomInst$inst_uses i)) \/
  (?a. a < j /\ MEM v (EL a ys).inst_outputs)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all mm_local_flat_map_supply_use_order >>
  metis_tac[EL_MEM]
QED

Theorem mm_local_mode_old_use[local]:
  apply_groups_inst_supply mode ns rm s i = (out,t) ==>
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!j v. MEM j out /\ MEM v (venomInst$inst_uses j) /\
    MEM v s.irs_used_vars ==> j = i)
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def, venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
      irSupplyTheory.fresh_inst_id_def] >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >> gvs[]
QED

Theorem mm_local_memzero_old_use[local]:
  apply_memzero_inst_supply ns rm s i = (out,t) ==>
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!j v. MEM j out /\ MEM v (venomInst$inst_uses j) /\
    MEM v s.irs_used_vars ==> j = i)
Proof
  rw[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def,
      venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def, irSupplyTheory.fresh_inst_id_def] >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >> gvs[]
QED

Theorem mm_local_list_old_vars[local]:
  !vars f xs s ys t.
  (!u i out w. f u i = (out,w) ==>
    (!v. MEM v u.irs_used_vars ==> MEM v w.irs_used_vars) /\
    (!j v. MEM j out /\ MEM v (vars j) /\
      MEM v u.irs_used_vars ==> j = i)) /\
  mm_flat_map_supply f s xs = (ys,t) ==>
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!j v. MEM j ys /\ MEM v (vars j) /\
    MEM v s.irs_used_vars ==> MEM j xs)
Proof
  ntac 2 gen_tac >> Induct >> simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `!u i out w. _` drule >> strip_tac >>
  qpat_x_assum `!s ys t. _` (qspecl_then [`s1`, `outs`, `t`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[])) >> strip_tac >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_phase_old_use[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) ==>
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!i v. MEM i cc.bb_instructions /\ MEM v (venomInst$inst_uses i) /\
    MEM v s.irs_used_vars ==> MEM i bb.bb_instructions)
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`)
    (Q.ISPEC `venomInst$inst_uses` mm_local_list_old_vars) >>
  (impl_tac >- metis_tac[mm_local_memzero_old_use, mm_local_mode_old_use]) >>
  simp[]
QED

Theorem mm_local_prefix_old_use[local]:
  !fn0 supply index k bb sk.
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) ==>
  (!v. MEM v supply.irs_used_vars ==> MEM v sk.irs_used_vars) /\
  (!i v. MEM i bb.bb_instructions /\ MEM v (venomInst$inst_uses i) /\
    MEM v supply.irs_used_vars ==> MEM i (EL index fn0.fn_blocks).bb_instructions)
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `(!v. MEM v supply.irs_used_vars ==> MEM v sp.irs_used_vars) /\
   (!i v. MEM i prev.bb_instructions /\ MEM v (venomInst$inst_uses i) /\
     MEM v supply.irs_used_vars ==> MEM i (EL index fn0.fn_blocks).bb_instructions)`
    by (first_x_assum irule >> simp[]) >>
  drule mm_local_phase_old_use >> strip_tac >> metis_tac[]
QED

Theorem mm_local_phase_used_vars_mono[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) /\ MEM v s.irs_used_vars ==>
  MEM v t.irs_used_vars
Proof
  metis_tac[mm_local_phase_old_use]
QED

Theorem mm_local_phase_old_use_origin[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) /\
  MEM i cc.bb_instructions /\ MEM v (venomInst$inst_uses i) /\
  MEM v s.irs_used_vars ==> MEM i bb.bb_instructions
Proof
  metis_tac[mm_local_phase_old_use]
QED

Theorem mm_local_prefix_used_vars_mono[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM v supply.irs_used_vars ==> MEM v sk.irs_used_vars
Proof
  metis_tac[mm_local_prefix_old_use]
QED

Theorem mm_local_prefix_old_use_origin[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM i bb.bb_instructions /\ MEM v (venomInst$inst_uses i) /\
  MEM v supply.irs_used_vars ==> MEM i (EL index fn0.fn_blocks).bb_instructions
Proof
  metis_tac[mm_local_prefix_old_use]
QED

Theorem mm_local_prefix_original_use_origin[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ir_supply_covers_fn supply fn0 /\ MEM v (irSupply$fn_ir_vars fn0) /\
  MEM i bb.bb_instructions /\ MEM v (venomInst$inst_uses i) ==>
  MEM i (EL index fn0.fn_blocks).bb_instructions
Proof
  rpt strip_tac >> irule mm_local_prefix_old_use_origin >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Theorem mm_local_prefix_original_consumer[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ir_supply_covers_fn supply fn0 /\ MEM v (irSupply$fn_ir_vars fn0) /\
  index < LENGTH fn0.fn_blocks /\
  MEM i bb.bb_instructions /\ MEM v (venomInst$inst_uses i) ==>
  MEM i (fn_insts fn0)
Proof
  rpt strip_tac >>
  drule_all mm_local_prefix_original_use_origin >> strip_tac >>
  irule mmWfProofsTheory.fn_insts_mem_block >>
  qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM]
QED

Theorem mm_local_operand_vars_eq[local]:
  !ops. dfgDefs$operand_vars ops = venomInst$operand_vars ops
Proof
  Induct >> simp[dfgDefsTheory.operand_vars_def,
                 venomInstTheory.operand_vars_def] >>
  Cases_on `h` >>
  simp[dfgDefsTheory.operand_vars_def, venomInstTheory.operand_vars_def,
       dfgDefsTheory.operand_var_def, venomInstTheory.operand_var_def]
QED

Theorem mm_local_prefix_original_uses[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ir_supply_covers_fn supply fn0 /\ MEM v (irSupply$fn_ir_vars fn0) /\
  index < LENGTH fn0.fn_blocks /\
  MEM i bb.bb_instructions /\ MEM v (venomInst$inst_uses i) ==>
  MEM i (dfg_get_uses (dfg_build_function fn0) v)
Proof
  rpt strip_tac >>
  irule dfgAnalysisPropsTheory.dfg_build_function_uses_complete >>
  conj_tac
  >- (drule_all mm_local_prefix_original_consumer >> simp[]) >>
  gvs[mm_local_operand_vars_eq, venomInstTheory.inst_uses_def]
QED

Theorem mm_local_build_ids_key[local]:
  !xs dfg.
  (!id i. dfg_get_inst_by_id dfg id = SOME i ==> i.inst_id = id) ==>
  !id i. dfg_get_inst_by_id (dfg_build_insts_rev dfg xs) id = SOME i ==>
    i.inst_id = id
Proof
  Induct >> simp[dfgDefsTheory.dfg_build_insts_rev_def] >> rpt strip_tac >>
  qpat_x_assum `!dfg. _` (qspec_then `dfg_add_inst dfg h` mp_tac) >>
  impl_tac
  >- metis_tac[dfgCorrectnessProofTheory.dfg_add_inst_ids_sound] >>
  disch_then drule >> simp[]
QED

Theorem mm_local_function_ids_key[local]:
  dfg_get_inst_by_id (dfg_build_function fn0) id = SOME i ==> i.inst_id = id
Proof
  simp[dfgDefsTheory.dfg_build_function_def, dfgDefsTheory.dfg_build_insts_def] >>
  strip_tac >> irule mm_local_build_ids_key >>
  qexistsl_tac [`dfg_empty`, `REVERSE (fn_insts fn0)`] >>
  simp[dfgDefsTheory.dfg_get_inst_by_id_def, dfgDefsTheory.dfg_empty_def]
QED

Theorem mm_local_function_ids_exact[local]:
  wf_function fn0 /\ MEM i (fn_insts fn0) ==>
  dfg_get_inst_by_id (dfg_build_function fn0) i.inst_id = SOME i
Proof
  rpt strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_ids_complete_proof >>
  strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_ids_sound_proof >>
  strip_tac >>
  drule mm_local_function_ids_key >> strip_tac >>
  `inst' = i` by
    (irule mmWfProofsTheory.fn_inst_ids_distinct_inj >>
     conj_tac >- simp[] >>
     qexists_tac `fn0` >> gvs[venomWfTheory.wf_function_def]) >>
  gvs[]
QED

Theorem mm_local_prefix_original_lookup[local]:
  wf_function fn0 /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ir_supply_covers_fn supply fn0 /\ MEM v (irSupply$fn_ir_vars fn0) /\
  index < LENGTH fn0.fn_blocks /\
  MEM i bb.bb_instructions /\ MEM v (venomInst$inst_uses i) ==>
  dfg_get_inst_by_id (dfg_build_function fn0) i.inst_id = SOME i
Proof
  rpt strip_tac >> irule mm_local_function_ids_exact >> simp[] >>
  drule_all mm_local_prefix_original_consumer >> simp[]
QED

Theorem mm_local_scan_lookup_step[local]:
  FLOOKUP (scan_inst dfg mode ss inst).ss_loads v = SOME a ==>
  FLOOKUP ss.ss_loads v = SOME a \/
  (inst.inst_opcode = mode_load_opcode mode /\
   ?w. inst.inst_operands = [Lit w] /\ inst.inst_outputs = [v] /\ a = w2n w)
Proof
  simp[scan_inst_def] >> IF_CASES_TAC
  >- (simp[scan_load_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >>
        gvs[hard_barrier_def, operand_lit_val_def]) >>
      rpt IF_CASES_TAC >>
      gvs[flush_copies_def, finite_mapTheory.FLOOKUP_UPDATE,
          AllCaseEqs()] >> Cases_on `h` >>
      gvs[operand_lit_val_def] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (simp[scan_store_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[hard_barrier_def]) >>
      simp[flush_hazards_def] >> rpt IF_CASES_TAC >>
      gvs[flush_copies_def, invalidate_loads_def,
          finite_mapTheory.FLOOKUP_DRESTRICT, AllCaseEqs()]) >>
  IF_CASES_TAC
  >- (simp[scan_bulk_copy_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[hard_barrier_def]) >>
      simp[flush_hazards_def] >> rpt IF_CASES_TAC >>
      gvs[flush_copies_def, invalidate_loads_def,
          finite_mapTheory.FLOOKUP_DRESTRICT, AllCaseEqs()]) >>
  IF_CASES_TAC >> simp[hard_barrier_def]
QED

Theorem mm_local_scan_lookup_fold[local]:
  !xs ss v a.
  FLOOKUP (FOLDL (scan_inst dfg mode) ss xs).ss_loads v = SOME a ==>
  FLOOKUP ss.ss_loads v = SOME a \/
  ?q w. MEM q xs /\ q.inst_opcode = mode_load_opcode mode /\
    q.inst_operands = [Lit w] /\ q.inst_outputs = [v] /\ a = w2n w
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- (drule mm_local_scan_lookup_step >> strip_tac >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem mm_local_scan_lookup_prefix[local]:
  (!v a. FLOOKUP ss.ss_loads v = SOME a ==>
    ?q w. MEM q pre /\ q.inst_opcode = mode_load_opcode mode /\
      q.inst_operands = [Lit w] /\ q.inst_outputs = [v] /\ a = w2n w) ==>
  !v a. FLOOKUP (FOLDL (scan_inst dfg mode) ss xs).ss_loads v = SOME a ==>
    ?q w. MEM q (pre ++ xs) /\ q.inst_opcode = mode_load_opcode mode /\
      q.inst_operands = [Lit w] /\ q.inst_outputs = [v] /\ a = w2n w
Proof
  rpt strip_tac >> drule mm_local_scan_lookup_fold >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_scan_lookup_origin[local]:
  FLOOKUP (FOLDL (scan_inst dfg mode) empty_scan_state xs).ss_loads v = SOME a ==>
  ?q w. MEM q xs /\ q.inst_opcode = mode_load_opcode mode /\
    q.inst_operands = [Lit w] /\ q.inst_outputs = [v] /\ a = w2n w
Proof
  strip_tac >> drule mm_local_scan_lookup_fold >>
  simp[empty_scan_state_def]
QED

Theorem mm_local_fold_roles[local]:
  !is pre post xs. xs = pre ++ is ++ post /\
  mm_local_scan_every (mm_local_group_roles dfg mode xs)
    (FOLDL (scan_inst dfg mode) empty_scan_state pre) ==>
  mm_local_scan_every (mm_local_group_roles dfg mode xs)
    (FOLDL (scan_inst dfg mode) empty_scan_state (pre ++ is))
Proof
  Induct_on `is` >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`pre ++ [h]`, `post`, `xs`] mp_tac) >>
  simp[APPEND_ASSOC, FOLDL_APPEND] >> disch_then irule >>
  irule mm_local_inst_roles >> simp[MEM_APPEND] >>
  reverse conj_tac >- metis_tac[GSYM APPEND_ASSOC] >>
  rpt strip_tac >> drule mm_local_scan_lookup_origin >> strip_tac >>
  gvs[MEM_SPLIT] >> metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem mm_local_scan_group_roles[local]:
  MEM cg (scan_block dfg mode bb).ss_flushed ==>
  mm_local_group_roles dfg mode bb.bb_instructions cg
Proof
  `mm_local_scan_every (mm_local_group_roles dfg mode bb.bb_instructions)
    (scan_block dfg mode bb)` by
    (simp[scan_block_def] >> irule mm_local_barrier_every >>
     mp_tac (Q.SPECL [`bb.bb_instructions`, `[]`, `[]`, `bb.bb_instructions`]
       mm_local_fold_roles) >>
     simp[mm_local_scan_every_def, empty_scan_state_def]) >>
  gvs[mm_local_scan_every_def, EVERY_MEM]
QED

Theorem mm_local_scan_group_roles_elim[local]:
  MEM cg (scan_block dfg mode bb).ss_flushed /\ MEM id cg.cg_inst_ids ==>
  (?st dst v. MEM st bb.bb_instructions /\ st.inst_id = id /\
    st.inst_opcode = MSTORE /\ st.inst_operands = [Lit dst; Var v]) \/
  (?cp dst src len. MEM cp bb.bb_instructions /\ cp.inst_id = id /\
    cp.inst_opcode = mode_copy_opcode mode /\
    cp.inst_operands = [Lit dst; Lit src; Lit len]) \/
  (?pre q mid st post v addr dst li.
    bb.bb_instructions = pre ++ [q] ++ mid ++ [st] ++ post /\
    q.inst_opcode = mode_load_opcode mode /\
    q.inst_operands = [Lit addr] /\ q.inst_outputs = [v] /\
    st.inst_opcode = MSTORE /\ st.inst_operands = [Lit dst; Var v] /\
    dfg_get_def dfg v = SOME li /\ li.inst_id = id /\
    MEM st.inst_id cg.cg_inst_ids)
Proof
  strip_tac >> drule mm_local_scan_group_roles >>
  simp[mm_local_group_roles_def]
QED

Theorem mm_local_mode_old_output_var[local]:
  apply_groups_inst_supply mode ns rm s i = (out,t) ==>
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!j v. MEM j out /\ MEM v j.inst_outputs /\
    MEM v s.irs_used_vars ==> j = i)
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def, irSupplyTheory.fresh_inst_id_def] >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >> gvs[]
QED

Theorem mm_local_memzero_old_output_var[local]:
  apply_memzero_inst_supply ns rm s i = (out,t) ==>
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!j v. MEM j out /\ MEM v j.inst_outputs /\
    MEM v s.irs_used_vars ==> j = i)
Proof
  rw[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def,
      irSupplyTheory.fresh_inst_id_def] >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >> gvs[]
QED

Theorem mm_local_phase_old_output_var[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) ==>
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!i v. MEM i cc.bb_instructions /\ MEM v i.inst_outputs /\
    MEM v s.irs_used_vars ==> MEM i bb.bb_instructions)
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`)
    (Q.ISPEC `\i:instruction. i.inst_outputs` mm_local_list_old_vars) >>
  (impl_tac >- metis_tac[mm_local_memzero_old_output_var,
                       mm_local_mode_old_output_var]) >>
  metis_tac[]
QED

Theorem mm_local_prefix_old_output_var[local]:
  !fn0 supply index k bb sk.
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) ==>
  (!v. MEM v supply.irs_used_vars ==> MEM v sk.irs_used_vars) /\
  (!i v. MEM i bb.bb_instructions /\ MEM v i.inst_outputs /\
    MEM v supply.irs_used_vars ==> MEM i (EL index fn0.fn_blocks).bb_instructions)
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `(!v. MEM v supply.irs_used_vars ==> MEM v sp.irs_used_vars) /\
   (!i v. MEM i prev.bb_instructions /\ MEM v i.inst_outputs /\
     MEM v supply.irs_used_vars ==> MEM i (EL index fn0.fn_blocks).bb_instructions)`
    by (first_x_assum irule >> simp[]) >>
  drule mm_local_phase_old_output_var >> strip_tac >> metis_tac[]
QED

Theorem mm_local_prefix_producer_identify[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM q bb.bb_instructions /\ MEM v q.inst_outputs /\
  dfg_get_def (dfg_build_function fn0) v = SOME li ==> q = li
Proof
  rpt strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_correct_proof >> strip_tac >>
  `MEM v supply.irs_used_vars` by
    (mp_tac (Q.SPECL [`fn0.fn_blocks`, `supply.irs_used_vars`]
      mmSupplyWfProofsTheory.mm_supply_outputs_covered) >>
     gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_vars_def,
         list_subset_def, EVERY_MEM, venomInstTheory.fn_insts_def, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  `MEM q (EL index fn0.fn_blocks).bb_instructions` by
    metis_tac[mm_local_prefix_old_output_var] >>
  `MEM q (fn_insts fn0)` by
    (irule mmWfProofsTheory.fn_insts_mem_block >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
  irule allocaRemapSSATheory.ssa_unique_output >>
  conj_tac
  >- (qexists_tac `fn0` >> gvs[wf_ssa_def]) >>
  qexists_tac `v` >> simp[]
QED

Theorem mm_local_nonoriginal_def_absent[local]:
  ~MEM v (irSupply$fn_ir_vars fn0) ==>
  dfg_get_def (dfg_build_function fn0) v = NONE
Proof
  strip_tac >> Cases_on `dfg_get_def (dfg_build_function fn0) v` >> simp[] >>
  drule dfgCorrectnessProofTheory.dfg_build_function_correct_proof >> strip_tac >>
  mp_tac (Q.SPECL [`fn0.fn_blocks`, `irSupply$fn_ir_vars fn0`]
    mmSupplyWfProofsTheory.mm_supply_outputs_covered) >>
  gvs[irSupplyTheory.fn_ir_vars_def, list_subset_def, EVERY_MEM,
      venomInstTheory.fn_insts_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem mm_local_prefix_group_roles_elim[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM id cg.cg_inst_ids ==>
  (?st dst v. MEM st bb.bb_instructions /\ st.inst_id = id /\
    st.inst_opcode = MSTORE /\ st.inst_operands = [Lit dst; Var v]) \/
  (?cp dst src len. MEM cp bb.bb_instructions /\ cp.inst_id = id /\
    cp.inst_opcode = mode_copy_opcode mode /\
    cp.inst_operands = [Lit dst; Lit src; Lit len]) \/
  (?pre q mid st post v addr dst.
    bb.bb_instructions = pre ++ [q] ++ mid ++ [st] ++ post /\
    q.inst_opcode = mode_load_opcode mode /\
    q.inst_operands = [Lit addr] /\ q.inst_outputs = [v] /\
    st.inst_opcode = MSTORE /\ st.inst_operands = [Lit dst; Var v] /\
    dfg_get_def (dfg_build_function fn0) v = SOME q /\ q.inst_id = id /\
    MEM st.inst_id cg.cg_inst_ids)
Proof
  rpt strip_tac >> drule_all mm_local_scan_group_roles_elim >> strip_tac
  >- metis_tac[]
  >- metis_tac[] >>
  `MEM q bb.bb_instructions /\ MEM v q.inst_outputs` by simp[MEM_APPEND] >>
  drule_all mm_local_prefix_producer_identify >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_rep_not_before_store[local]:
  xs = pre ++ [q] ++ mid ++ [st] ++ post /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  MEM st.inst_id cg.cg_inst_ids ==>
  rep_of_group xs cg <> SOME (q.inst_id,cg)
Proof
  strip_tac >> gvs[] >>
  simp[rep_of_group_def, sort_ids_by_block_def, FILTER_APPEND_DISTRIB] >>
  Cases_on `REVERSE (FILTER (\id. MEM id cg.cg_inst_ids)
    (MAP (\i. i.inst_id) post))` >> simp[] >>
  gvs[REVERSE_APPEND, ALL_DISTINCT_APPEND] >>
  `MEM h (REVERSE (FILTER (\id. MEM id cg.cg_inst_ids)
    (MAP (\i. i.inst_id) post)))` by metis_tac[MEM] >>
  gvs[MEM_REVERSE, MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_prefix_load_not_rep[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ q.inst_opcode = mode_load_opcode mode /\
  MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed ==>
  rep_of_group bb.bb_instructions cg <> SOME (q.inst_id,cg)
Proof
  strip_tac >> strip_tac >>
  drule mm_local_rep_member >> strip_tac >>
  drule_all mm_local_prefix_group_roles_elim >> strip_tac
  >- (`st = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      Cases_on `mode` >> gvs[mode_load_opcode_def])
  >- (rename1 `MEM copy_inst bb.bb_instructions` >>
      `copy_inst = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      Cases_on `mode` >> gvs[mode_load_opcode_def, mode_copy_opcode_def]) >>
  `MEM q' bb.bb_instructions` by simp[MEM_APPEND] >>
  `q' = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  metis_tac[mm_local_rep_not_before_store]
QED

Theorem mm_local_prefix_load_rep_absent[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ q.inst_opcode = mode_load_opcode mode ==>
  ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed) q.inst_id = NONE
Proof
  strip_tac >> simp[alistTheory.ALOOKUP_NONE, rep_map_of_groups_def,
    MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  rename1 `MEM group (scan_block (dfg_build_function fn0) mode bb).ss_flushed` >>
  Cases_on `rep_of_group bb.bb_instructions group` >> gvs[] >>
  rename1 `rep_of_group bb.bb_instructions group = SOME result` >>
  PairCases_on `result` >> gvs[] >>
  drule mm_local_rep_member >> strip_tac >> gvs[] >>
  metis_tac[mm_local_prefix_load_not_rep]
QED

Theorem mm_local_surviving_store_supply[local]:
  u.inst_opcode = MSTORE /\ MEM v (venomInst$inst_uses u) /\
  apply_groups_inst_supply mode ns rm s u = (out,t) /\ MEM u out ==>
  ~MEM u.inst_id ns /\
  (!cg. ALOOKUP rm u.inst_id = SOME cg ==> cg.cg_length = 32 /\ mode <> DloadMerge)
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def,
    venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def,
    venomInstTheory.operand_var_def] >>
  gvs[venomInstTheory.instruction_component_equality,
    venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]
QED

Theorem mm_local_store_not_definition[local]:
  fn_inst_wf fn0 /\ wf_function fn0 /\ MEM u (fn_insts fn0) /\
  u.inst_opcode = MSTORE /\
  dfg_get_def (dfg_build_function fn0) v = SOME li ==> li.inst_id <> u.inst_id
Proof
  strip_tac >> strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_correct_proof >> strip_tac >>
  `li = u` by
    (irule mmWfProofsTheory.fn_inst_ids_distinct_inj >> simp[] >>
     qexists_tac `fn0` >> gvs[wf_function_def]) >>
  gvs[fn_inst_wf_def, venomInstTheory.fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
  `inst_wf li` by metis_tac[] >> gvs[inst_wf_def]
QED

Theorem mm_local_surviving_original_store_pin[local]:
  fn_inst_wf fn0 /\ wf_function fn0 /\ MEM u (fn_insts fn0) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM u bb.bb_instructions /\ u.inst_opcode = MSTORE /\
  u.inst_operands = [Lit dst; Var v] /\
  dfg_get_inst_by_id (dfg_build_function fn0) u.inst_id = SOME u /\
  dfg_get_def (dfg_build_function fn0) v = SOME q /\
  MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM u.inst_id cg.cg_inst_ids /\
  apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) s u = (out,t) /\
  MEM u out ==>
  rep_of_group bb.bb_instructions cg = SOME (u.inst_id,cg) /\
  rep_pin_id (dfg_build_function fn0) mode u.inst_id cg = SOME q.inst_id
Proof
  strip_tac >>
  `MEM v (venomInst$inst_uses u)` by
    simp[venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def] >>
  drule_all mm_local_surviving_store_supply >> strip_tac >>
  `!x li. dfg_get_def (dfg_build_function fn0) x = SOME li ==> li.inst_id <> u.inst_id`
    by metis_tac[mm_local_store_not_definition] >>
  `!rep. rep_pin_id (dfg_build_function fn0) mode rep cg <> SOME u.inst_id` by
    (simp[rep_pin_id_def, AllCaseEqs()] >> metis_tac[]) >>
  `rep_of_group bb.bb_instructions cg = SOME (u.inst_id,cg)` by
    (irule mm_local_retained_store_rep >> simp[] >> metis_tac[]) >>
  `ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed) u.inst_id = SOME cg` by
    (irule mm_local_scan_rep_lookup >> simp[] >> qexists_tac `\id. id = u.inst_id` >> simp[] >>
     metis_tac[]) >>
  `cg.cg_length = 32 /\ mode <> DloadMerge` by metis_tac[] >>
  simp[rep_pin_id_def]
QED

Theorem mm_local_prefix_used_load_not_nop[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ q.inst_opcode = mode_load_opcode mode /\
  q.inst_operands = [Lit addr] /\ q.inst_outputs = [v] /\
  dfg_get_def (dfg_build_function fn0) v = SOME q /\
  MEM u bb.bb_instructions /\ MEM u (dfg_get_uses (dfg_build_function fn0) v) /\
  MEM v (venomInst$inst_uses u) /\
  apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) s u = (out,t) /\
  MEM u out ==>
  ~MEM q.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
Proof
  strip_tac >> strip_tac >>
  `MEM q (fn_insts fn0)` by
    metis_tac[dfgCorrectnessProofTheory.dfg_build_function_correct_proof] >>
  `MEM u (fn_insts fn0)` by
    metis_tac[dfgCorrectnessProofTheory.dfg_build_function_uses_sound_proof] >>
  `dfg_get_inst_by_id (dfg_build_function fn0) q.inst_id = SOME q /\
   dfg_get_inst_by_id (dfg_build_function fn0) u.inst_id = SOME u` by
    metis_tac[mm_local_function_ids_exact] >>
  `q.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD}` by
    (Cases_on `mode` >> gvs[mode_load_opcode_def]) >>
  drule_all mm_local_deleted_load_certificate >> strip_tac >>
  `MEM u.inst_id cg.cg_inst_ids` by gvs[EVERY_MEM] >>
  drule_all mm_local_prefix_group_roles_elim >> strip_tac
  >- (`st = u` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      gvs[venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def,
        venomInstTheory.operand_var_def] >>
      drule_all mm_local_surviving_original_store_pin >> strip_tac >> gvs[]) 
  >- (`cp' = u` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      gvs[venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def,
        venomInstTheory.operand_var_def]) >>
  `MEM q' bb.bb_instructions` by simp[MEM_APPEND] >>
  `q' = u` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  gvs[venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def,
    venomInstTheory.operand_var_def]
QED

Theorem mm_local_prefix_used_load_unchanged[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ q.inst_opcode = mode_load_opcode mode /\
  q.inst_operands = [Lit addr] /\ q.inst_outputs = [v] /\
  dfg_get_def (dfg_build_function fn0) v = SOME q /\
  MEM u bb.bb_instructions /\ MEM u (dfg_get_uses (dfg_build_function fn0) v) /\
  MEM v (venomInst$inst_uses u) /\
  apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) s u = (out,t) /\
  MEM u out ==>
  !r. apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) r q = ([q],r)
Proof
  strip_tac >>
  drule_all mm_local_prefix_used_load_not_nop >> strip_tac >>
  drule_all mm_local_prefix_load_rep_absent >> strip_tac >>
  simp[apply_groups_inst_supply_def]
QED

Theorem mm_local_mode_output_opcode[local]:
  apply_groups_inst_supply mode ns rm s i = (out,t) /\
  MEM j out /\ j.inst_outputs <> [] ==>
  j = i \/ (mode <> DloadMerge /\ j.inst_opcode = mode_load_opcode mode)
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def]
QED

Theorem mm_local_memzero_output_opcode[local]:
  apply_memzero_inst_supply ns rm s i = (out,t) /\
  MEM j out /\ j.inst_outputs <> [] ==>
  j = i \/ j.inst_opcode = CALLDATASIZE
Proof
  rw[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def]
QED

Theorem mm_local_phase_output_opcode[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) /\
  MEM j cc.bb_instructions /\ j.inst_outputs <> [] ==>
  MEM j bb.bb_instructions \/
  (case phase of NONE => j.inst_opcode = CALLDATASIZE
   | SOME mode => mode <> DloadMerge /\ j.inst_opcode = mode_load_opcode mode)
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  spose_not_then strip_assume_tac >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`)
    mmSupplyWfProofsTheory.mm_flat_map_supply_origin
  >- (disch_then (qspec_then `\i. i.inst_outputs <> [] /\
        i.inst_opcode <> CALLDATASIZE` (qspec_then `j` mp_tac)) >>
      simp[] >> rpt strip_tac >>
      drule_all mm_local_memzero_output_opcode >> simp[]) >>
  disch_then (qspec_then `\i. i.inst_outputs <> [] /\
    ~(x <> DloadMerge /\ i.inst_opcode = mode_load_opcode x)`
    (qspec_then `j` mp_tac)) >> simp[] >>
  metis_tac[mm_local_mode_output_opcode]
QED

Theorem mm_local_prefix_output_opcode[local]:
  !fn0 supply index k bb sk q.
  k < 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM q bb.bb_instructions /\ q.inst_outputs <> [] ==>
  MEM q (EL index fn0.fn_blocks).bb_instructions \/
  q.inst_opcode = CALLDATASIZE \/
  (2 <= k /\ q.inst_opcode = CALLDATALOAD)
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  drule_all mm_local_phase_output_opcode >> strip_tac
  >- (first_x_assum (qspecl_then [`prev`, `sp`, `q`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >> decide_tac) >>
  `k = 0 \/ k = 1 \/ k = 2` by decide_tac >>
  gvs[mode_load_opcode_def]
QED

Theorem mm_local_prefix_fresh_output_opcode[local]:
  index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM q bb.bb_instructions /\ MEM v q.inst_outputs /\
  ~MEM v (irSupply$fn_ir_vars fn0) ==>
  q.inst_opcode = CALLDATASIZE \/ (2 <= k /\ q.inst_opcode = CALLDATALOAD)
Proof
  strip_tac >>
  `q.inst_outputs <> []` by (strip_tac >> gvs[]) >>
  drule_all mm_local_prefix_output_opcode >> strip_tac >> simp[] >>
  `MEM q (fn_insts fn0)` by
    (irule mmWfProofsTheory.fn_insts_mem_block >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
  mp_tac (Q.SPECL [`fn0.fn_blocks`, `irSupply$fn_ir_vars fn0`]
    mmSupplyWfProofsTheory.mm_supply_outputs_covered) >>
  gvs[irSupplyTheory.fn_ir_vars_def, list_subset_def, EVERY_MEM,
      venomInstTheory.fn_insts_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem mm_local_prefix_nonselected_group_absent[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ q.inst_opcode <> MSTORE /\
  q.inst_opcode <> mode_copy_opcode mode /\
  q.inst_opcode <> mode_load_opcode mode ==>
  !cg. MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed ==>
    ~MEM q.inst_id cg.cg_inst_ids
Proof
  rpt strip_tac >> drule_all mm_local_prefix_group_roles_elim >> strip_tac
  >- (`st = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >> gvs[])
  >- (rename1 `MEM copy_inst bb.bb_instructions` >>
      `copy_inst = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >> gvs[]) >>
  `MEM q' bb.bb_instructions` by simp[MEM_APPEND] >>
  `q' = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >> gvs[]
QED

Theorem mm_local_groups_absent_unchanged[local]:
  (!cg. MEM cg groups ==> ~MEM q.inst_id cg.cg_inst_ids) ==>
  !r. apply_groups_inst_supply mode
    (nop_ids_of_groups dfg mode insts groups)
    (rep_map_of_groups insts groups) r q = ([q],r)
Proof
  strip_tac >>
  `~MEM q.inst_id (nop_ids_of_groups dfg mode insts groups)` by
    (strip_tac >> gvs[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >>
     rename1 `MEM cg groups` >>
     qpat_x_assum `MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
     simp[nop_ids_of_group_def] >>
     Cases_on `REVERSE (sort_ids_by_block insts cg.cg_inst_ids)` >>
     simp[MEM_FILTER] >> disj2_tac >> strip_tac >>
     `MEM q.inst_id (REVERSE (sort_ids_by_block insts cg.cg_inst_ids))`
       by (pure_asm_rewrite_tac[MEM] >> simp[]) >>
     gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER] >> metis_tac[]) >>
  `ALOOKUP (rep_map_of_groups insts groups) q.inst_id = NONE` by
    (simp[alistTheory.ALOOKUP_NONE, rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
     rpt strip_tac >> spose_not_then strip_assume_tac >>
     rename1 `MEM group groups` >>
     Cases_on `rep_of_group insts group` >> gvs[] >>
     rename1 `rep_of_group insts group = SOME result` >>
     PairCases_on `result` >> gvs[] >> drule mm_local_rep_member >> strip_tac >>
     metis_tac[]) >>
  simp[apply_groups_inst_supply_def]
QED

Theorem mm_local_prefix_nonselected_unchanged[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ q.inst_opcode <> MSTORE /\
  q.inst_opcode <> mode_copy_opcode mode /\
  q.inst_opcode <> mode_load_opcode mode ==>
  !r. apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) r q = ([q],r)
Proof
  strip_tac >> irule mm_local_groups_absent_unchanged >>
  metis_tac[mm_local_prefix_nonselected_group_absent]
QED

Theorem mm_local_prefix_fresh_mode_unchanged[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ 0 < k /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ MEM v q.inst_outputs /\
  ~MEM v (irSupply$fn_ir_vars fn0) /\
  EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] = SOME mode ==>
  !r. apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) r q = ([q],r)
Proof
  strip_tac >> drule_all mm_local_prefix_fresh_output_opcode >> strip_tac >>
  `q.inst_opcode <> MSTORE /\ q.inst_opcode <> mode_copy_opcode mode /\
   q.inst_opcode <> mode_load_opcode mode` by
    (`k = 1 \/ k = 2 \/ k = 3` by decide_tac >>
     gvs[mode_copy_opcode_def, mode_load_opcode_def]) >>
  irule mm_local_prefix_nonselected_unchanged >> simp[] >>
  qexistsl_tac [`index`, `k`, `sk`, `supply`] >> simp[]
QED

Theorem mm_local_prefix_fresh_unchanged[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ MEM v q.inst_outputs /\
  ~MEM v (irSupply$fn_ir_vars fn0) ==>
  !r. (case EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] of
    NONE => apply_memzero_inst_supply
      (nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed) r q
  | SOME mode => apply_groups_inst_supply mode
      (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed) r q) = ([q],r)
Proof
  strip_tac >> Cases_on `k = 0`
  >- (gvs[mm_local_prefix_zero] >>
      `MEM q (fn_insts fn0)` by
        (irule mmWfProofsTheory.fn_insts_mem_block >>
         qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
      mp_tac (Q.SPECL [`fn0.fn_blocks`, `irSupply$fn_ir_vars fn0`]
        mmSupplyWfProofsTheory.mm_supply_outputs_covered) >>
      gvs[irSupplyTheory.fn_ir_vars_def, list_subset_def, EVERY_MEM,
          venomInstTheory.fn_insts_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `0 < k` by decide_tac >>
  `?mode. EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] = SOME mode` by
    (`k = 1 \/ k = 2 \/ k = 3` by decide_tac >> gvs[]) >>
  simp[] >> drule_all mm_local_prefix_fresh_mode_unchanged >> simp[]
QED

Theorem mm_local_prefix_group_producer_shape[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ inst_wf q /\ MEM v q.inst_outputs /\
  MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM q.inst_id cg.cg_inst_ids ==>
  q.inst_opcode = mode_load_opcode mode /\
  (?addr. q.inst_operands = [Lit addr]) /\ q.inst_outputs = [v] /\
  dfg_get_def (dfg_build_function fn0) v = SOME q
Proof
  strip_tac >> drule_all mm_local_prefix_group_roles_elim >> strip_tac
  >- (`st = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      gvs[inst_wf_def])
  >- (rename1 `MEM copy_inst bb.bb_instructions` >>
      `copy_inst = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      Cases_on `mode` >> gvs[mode_copy_opcode_def, inst_wf_def]) >>
  `MEM q' bb.bb_instructions` by simp[MEM_APPEND] >>
  `q' = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >> gvs[]
QED

Theorem mm_local_prefix_external_id_absent[local]:
  wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM u (fn_insts fn0) /\
  ~MEM u (EL index fn0.fn_blocks).bb_instructions ==>
  ~MEM u.inst_id (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  strip_tac >>
  `MEM (EL index fn0.fn_blocks) fn0.fn_blocks` by simp[EL_MEM] >>
  `fn_inst_ids_distinct fn0` by gvs[wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions)` by
    metis_tac[mmWfProofsTheory.fn_inst_ids_distinct_block] >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
      (EL index fn0.fn_blocks).bb_instructions /\
    u.inst_id < supply.irs_next_inst` by
    (gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP,
      venomInstTheory.fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[MEM_MAP]) >>
  strip_tac >> gvs[MEM_MAP] >>
  drule_all mm_local_prefix_id_origin >> strip_tac
  >- (gvs[MEM_MAP] >>
      `MEM j (fn_insts fn0)` by
        (irule mmWfProofsTheory.fn_insts_mem_block >> metis_tac[]) >>
      `j = u` by metis_tac[mmWfProofsTheory.fn_inst_ids_distinct_inj] >> metis_tac[]) >>
  decide_tac
QED

Theorem mm_local_prefix_external_load_unchanged[local]:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ q.inst_opcode = mode_load_opcode mode /\
  q.inst_outputs = [v] /\
  dfg_get_inst_by_id (dfg_build_function fn0) q.inst_id = SOME q /\
  MEM u (dfg_get_uses (dfg_build_function fn0) v) /\
  MEM u (fn_insts fn0) /\
  ~MEM u (EL index fn0.fn_blocks).bb_instructions ==>
  !r. apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) r q = ([q],r)
Proof
  strip_tac >>
  `~MEM u.inst_id (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_external_id_absent] >>
  `~MEM q.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)` by
    (strip_tac >>
     `q.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD}` by
       (Cases_on `mode` >> gvs[mode_load_opcode_def]) >>
     drule_all mm_local_deleted_load_certificate >> strip_tac >>
     `MEM u.inst_id cg.cg_inst_ids` by gvs[EVERY_MEM] >>
     drule_all mm_local_prefix_group_roles_elim >> strip_tac >>
     gvs[MEM_MAP, MEM_APPEND] >> metis_tac[]) >>
  drule_all mm_local_prefix_load_rep_absent >> simp[apply_groups_inst_supply_def]
QED

Theorem mm_local_prefix_used_producer_unchanged[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ inst_wf q /\ MEM v q.inst_outputs /\
  MEM v (venomInst$inst_uses u) /\
  ((MEM u bb.bb_instructions /\
    apply_groups_inst_supply mode
      (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed) s u = (out,t) /\
    MEM u out) \/
   (MEM u (fn_insts fn0) /\ ~MEM u (EL index fn0.fn_blocks).bb_instructions)) ==>
  !r. apply_groups_inst_supply mode
    (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) r q = ([q],r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `?cg. MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
    MEM q.inst_id cg.cg_inst_ids`
  >- (pop_assum strip_assume_tac >>
      drule_all mm_local_prefix_group_producer_shape >> strip_tac >>
      `MEM v (irSupply$fn_ir_vars fn0)` by
        (spose_not_then assume_tac >> drule mm_local_nonoriginal_def_absent >> simp[]) >>
      qpat_x_assum `_ \/ _` strip_assume_tac
      >- (`MEM u (dfg_get_uses (dfg_build_function fn0) v)` by
            metis_tac[mm_local_prefix_original_uses] >>
          drule_all mm_local_prefix_used_load_unchanged >> simp[]) >>
      `MEM u (dfg_get_uses (dfg_build_function fn0) v)` by
        (irule dfgAnalysisPropsTheory.dfg_build_function_uses_complete >>
         gvs[mm_local_operand_vars_eq, venomInstTheory.inst_uses_def]) >>
      `dfg_get_inst_by_id (dfg_build_function fn0) q.inst_id = SOME q` by
        (drule dfgCorrectnessProofTheory.dfg_build_function_correct_proof >>
         strip_tac >> metis_tac[mm_local_function_ids_exact]) >>
      drule_all mm_local_prefix_external_load_unchanged >> simp[]) >>
  irule mm_local_groups_absent_unchanged >> metis_tac[]
QED

Theorem mm_local_memzero_producer_unchanged[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ inst_wf q /\ q.inst_outputs <> [] ==>
  !r. apply_memzero_inst_supply
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) r q = ([q],r)
Proof
  strip_tac >>
  `!cg. MEM cg (scan_block_memzero dfg bb).mz_flushed ==>
    ~MEM q.inst_id cg.cg_inst_ids` by
    (rpt strip_tac >> drule_all mm_local_memzero_group_roles >> strip_tac >>
     `i = q` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
     gvs[is_zero_store_def, is_calldatasize_copy_def, inst_wf_def]) >>
  `~MEM q.inst_id (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)` by
    (strip_tac >> gvs[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >>
     rename1 `MEM cg (scan_block_memzero dfg bb).mz_flushed` >>
     qpat_x_assum `MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
     simp[nop_ids_of_group_def] >>
     Cases_on `REVERSE (sort_ids_by_block bb.bb_instructions cg.cg_inst_ids)` >>
     simp[MEM_FILTER] >> disj2_tac >> strip_tac >>
     `MEM q.inst_id (REVERSE (sort_ids_by_block bb.bb_instructions cg.cg_inst_ids))`
       by (pure_asm_rewrite_tac[MEM] >> simp[]) >>
     gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER] >> metis_tac[]) >>
  `ALOOKUP (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) q.inst_id = NONE` by
    (simp[alistTheory.ALOOKUP_NONE, rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
     rpt strip_tac >> spose_not_then strip_assume_tac >>
     rename1 `MEM cg (scan_block_memzero dfg bb).mz_flushed` >>
     Cases_on `rep_of_group bb.bb_instructions cg` >> gvs[] >>
     rename1 `rep_of_group bb.bb_instructions cg = SOME result` >>
     PairCases_on `result` >> gvs[] >> drule mm_local_rep_member >>
     metis_tac[]) >>
  simp[apply_memzero_inst_supply_def]
QED

Theorem mm_local_prefix_phase_producer_unchanged[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ inst_wf q /\ MEM v q.inst_outputs /\
  MEM v (venomInst$inst_uses u) /\
  f = (case EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] of
    NONE => apply_memzero_inst_supply
      (nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
  | SOME mode => apply_groups_inst_supply mode
      (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)) /\
  ((MEM u bb.bb_instructions /\ f s u = (out,t) /\ MEM u out) \/
   (MEM u (fn_insts fn0) /\ ~MEM u (EL index fn0.fn_blocks).bb_instructions)) ==>
  !r. f r q = ([q],r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `k <= 4` by decide_tac >>
  Cases_on `EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]`
  >- (gvs[] >> irule mm_local_memzero_producer_unchanged >>
      simp[] >> metis_tac[MEM]) >>
  gvs[] >> `k <= 4` by decide_tac >>
  irule mm_local_prefix_used_producer_unchanged >> metis_tac[]
QED

Theorem mm_local_phase_expansion[local]:
  f = (case phase of
    NONE => apply_memzero_inst_supply
      (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
        (scan_block_memzero dfg bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed)
  | SOME mode => apply_groups_inst_supply mode
      (nop_ids_of_groups dfg mode bb.bb_instructions
        (scan_block dfg mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions (scan_block dfg mode bb).ss_flushed)) /\
  mm_local_phase dfg phase (bb,sk) = (bb',sk') ==>
  mm_flat_map_supply f sk bb.bb_instructions = (bb'.bb_instructions,sk') /\
  (!s i out t j v. f s i = (out,t) /\ j < LENGTH out /\
    MEM v (venomInst$inst_uses (EL j out)) ==>
    (EL j out = i /\ MEM v (venomInst$inst_uses i)) \/
    (?a. a < j /\ MEM v (EL a out).inst_outputs))
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> metis_tac[mm_local_memzero_chunk_use, mm_local_mode_chunk_use]
QED

Theorem mm_local_available_endpoint_transport[local]:
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  target'.bb_label = target.bb_label /\
  (!db q. MEM db fn.fn_blocks /\ MEM q db.bb_instructions /\
    MEM v q.inst_outputs ==>
    ?db'. MEM db' fn'.fn_blocks /\ db'.bb_label = db.bb_label /\
      MEM q db'.bb_instructions) /\
  def_available_at fn target NONE v ==>
  def_available_at fn' target' NONE v
Proof
  simp[def_available_at_def] >> metis_tac[]
QED

Theorem mm_local_available_point_transport[local]:
  fn'.fn_blocks = MAP B fn.fn_blocks /\ MEM target fn.fn_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  (!b. MEM b fn.fn_blocks ==> (B b).bb_label = b.bb_label) /\
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  (!db q. MEM db fn.fn_blocks /\ MEM q db.bb_instructions /\
    MEM v q.inst_outputs ==> MEM q (B db).bb_instructions) /\
  (!q a b. a < b /\ b < LENGTH target.bb_instructions /\
    EL a target.bb_instructions = q /\ EL b target.bb_instructions = u /\
    MEM v q.inst_outputs ==>
    ?c d. c < d /\ d < LENGTH (B target).bb_instructions /\
      EL c (B target).bb_instructions = q /\ EL d (B target).bb_instructions = u) /\
  def_available_at fn target (SOME u) v ==>
  def_available_at fn' (B target) (SOME u) v
Proof
  strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  qexistsl [`B def_bb`, `def_inst`] >>
  conj_tac >- metis_tac[MEM_MAP] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  strip_tac >>
  `def_bb.bb_label = target.bb_label` by metis_tac[] >>
  `def_bb = target` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_prefix_phase_ordinary_available[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  fn_dominates fn' bb'.bb_label bb'.bb_label /\
  f = (case EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] of
    NONE => apply_memzero_inst_supply
      (nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
  | SOME mode => apply_groups_inst_supply mode
      (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)) /\
  j < LENGTH bb'.bb_instructions /\ (EL j bb'.bb_instructions).inst_opcode <> PHI /\
  MEM v (venomInst$inst_uses (EL j bb'.bb_instructions)) ==>
  def_available_at fn' bb' (SOME (EL j bb'.bb_instructions)) v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks` by
    (simp[] >> metis_tac[MEM_LUPDATE, EL_MEM, EL_LUPDATE, LENGTH_LUPDATE]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_function_def, mmWfProofsTheory.fn_inst_ids_distinct_block] >>
  drule_all mm_local_phase_expansion >> strip_tac >>
  drule_all mm_local_flat_map_supply_use_order >> strip_tac
  >- (`def_available_at fn bb (SOME (EL b bb.bb_instructions)) v` by
        (qpat_x_assum `wf_ssa fn` mp_tac >>
         pure_rewrite_tac[wf_ssa_def, def_dominates_uses_def] >> strip_tac >>
         qpat_x_assum `!bb inst. _` (qspecl_then [`bb`, `EL b bb.bb_instructions`] mp_tac) >>
         simp[] >>
         `MEM (EL b bb.bb_instructions) bb.bb_instructions` by metis_tac[EL_MEM] >>
         `MEM (Var v) (EL b bb.bb_instructions).inst_operands` by
           metis_tac[passSharedDefsTheory.MEM_operand_vars_eq_Var,
                     venomInstTheory.inst_uses_def] >>
         metis_tac[]) >>
      qpat_x_assum `def_available_at fn bb _ v` mp_tac >>
      pure_rewrite_tac[def_available_at_def] >> strip_tac >>
      `bb'.bb_label = bb.bb_label` by metis_tac[mm_local_phase_label] >>
      Cases_on `def_bb = bb`
      >- (qpat_x_assum `def_bb = bb` SUBST_ALL_TAC >>
          `inst_wf def_inst` by
            metis_tac[fn_inst_wf_def, EVERY_MEM] >>
          `MEM (EL b bb.bb_instructions) bb.bb_instructions /\
           MEM (EL b bb.bb_instructions) chunk` by metis_tac[EL_MEM] >>
          `!r. f r def_inst = ([def_inst],r)` by
            (irule mm_local_prefix_phase_producer_unchanged >>
             conj_tac >- simp[] >>
             goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
             goal_assum (drule_at (Pat `MEM _ (venomInst$inst_uses _)`)) >>
             simp[] >> metis_tac[]) >>
          qpat_x_assum `fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks` kall_tac >>
          qpat_x_assum `bb = bb ==> _` mp_tac >> simp[] >> strip_tac >>
          `j' = b` by
            metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
          `MEM def_inst (TAKE b bb.bb_instructions)` by
            (simp[MEM_EL] >> qexists_tac `i` >> simp[LENGTH_TAKE, EL_TAKE]) >>
          `?c. c < j /\ EL c bb'.bb_instructions = def_inst` by simp[] >>
          qexistsl [`bb'`, `def_inst`] >> simp[] >>
          conj_tac >- metis_tac[EL_MEM, arithmeticTheory.LESS_TRANS] >>
          qexistsl [`c`, `j`] >> simp[]) >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
        metis_tac[wf_function_def, venomInstTheory.fn_labels_def] >>
      `def_bb.bb_label <> bb.bb_label` by
        metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      `MEM def_bb fn'.fn_blocks` by
        (qpat_x_assum `MEM def_bb fn.fn_blocks` mp_tac >>
         simp[MEM_LUPDATE] >> metis_tac[]) >>
      `def_bb <> bb'` by metis_tac[] >>
      qpat_x_assum `fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks` kall_tac >>
      qexistsl [`def_bb`, `def_inst`] >> simp[]) >>
  qpat_x_assum `fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks` kall_tac >>
  simp[def_available_at_def] >>
  qexistsl [`bb'`, `EL a bb'.bb_instructions`] >> simp[] >>
  conj_tac >- (irule EL_MEM >> decide_tac) >>
  qexistsl [`a`, `j`] >> simp[]
QED

Theorem mm_local_prefix_phase_producer_retained[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ inst_wf q /\ MEM v q.inst_outputs /\
  MEM v (venomInst$inst_uses u) /\
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk') /\
  ((MEM u (fn_insts fn0) /\ ~MEM u (EL index fn0.fn_blocks).bb_instructions) \/
   (MEM u bb'.bb_instructions /\ u.inst_opcode = PHI)) ==>
  MEM q bb'.bb_instructions
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `f = (case EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] of
    NONE => apply_memzero_inst_supply
      (nop_ids_of_groups (dfg_build_function fn0) Mem2Mem bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block_memzero (dfg_build_function fn0) bb).mz_flushed)
  | SOME mode => apply_groups_inst_supply mode
      (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed))` >>
  `mm_flat_map_supply f sk bb.bb_instructions = (bb'.bb_instructions,sk')` by
    (irule (cj 1 mm_local_phase_expansion) >>
     goal_assum (drule_at (Pat `mm_local_phase _ _ _ = _`)) >> simp[Abbr `f`]) >>
  `(!xs s ys t. mm_flat_map_supply f s xs = (ys,t) /\ MEM u ys ==>
    ?i r out z. MEM i xs /\ f r i = (out,z) /\ MEM u out)` by
    (Induct >> simp[mm_flat_map_supply_def] >> rpt gen_tac >>
     Cases_on `f s h` >> rename1 `f s h = (chunk,r)` >>
     Cases_on `mm_flat_map_supply f r xs` >>
     simp[] >> strip_tac >> gvs[MEM_APPEND] >> metis_tac[]) >>
  `((?r out z. MEM u bb.bb_instructions /\ f r u = (out,z) /\ MEM u out) \/
    (MEM u (fn_insts fn0) /\ ~MEM u (EL index fn0.fn_blocks).bb_instructions))` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >- simp[] >>
     `?i r out z. MEM i bb.bb_instructions /\ f r i = (out,z) /\ MEM u out` by
       (first_x_assum irule >> metis_tac[]) >>
     `u = i` by
       (Cases_on `EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]` >>
        gvs[Abbr `f`] >>
        metis_tac[apply_memzero_inst_supply_phi_origin, apply_groups_inst_supply_phi_origin]) >>
     metis_tac[]) >>
  `!r. f r q = ([q],r)` by
    (irule mm_local_prefix_phase_producer_unchanged >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `MEM _ (venomInst$inst_uses _)`)) >>
     simp[Abbr `f`] >> metis_tac[]) >>
  drule mm_local_flat_map_supply_member >>
  disch_then irule >> simp[]
QED

Theorem mm_local_prefix_phase_external_available[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  MEM target fn0.fn_blocks /\
  target.bb_label <> (EL index fn0.fn_blocks).bb_label /\
  MEM u target.bb_instructions /\ MEM v (venomInst$inst_uses u) /\
  def_available_at fn target (SOME u) v ==>
  def_available_at fn' target (SOME u) v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
      (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM, MEM_MAP]) >>
  `bb.bb_label = (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mm_local_prefix_wf_last, wf_ssa_def, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `bb'.bb_label = bb.bb_label` by metis_tac[mm_local_phase_label] >>
  `MEM bb fn.fn_blocks` by
    (simp[] >> metis_tac[MEM_LUPDATE, EL_MEM, EL_LUPDATE, LENGTH_LUPDATE]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_function_def, mmWfProofsTheory.fn_inst_ids_distinct_block] >>
  `MEM u (fn_insts fn0) /\ ~MEM u (EL index fn0.fn_blocks).bb_instructions` by
    (conj_tac >- metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM] >>
     metis_tac[wf_function_def, scfg_instruction_block_unique, EL_MEM]) >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  pure_rewrite_tac[def_available_at_def] >> strip_tac >>
  Cases_on `def_bb = bb`
  >- (qpat_x_assum `def_bb = bb` SUBST_ALL_TAC >>
      `MEM def_inst bb'.bb_instructions` by
        (irule mm_local_prefix_phase_producer_retained >>
         (conj_tac >- metis_tac[fn_inst_wf_def, EVERY_MEM]) >>
         goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
         goal_assum (drule_at (Pat `MEM _ (venomInst$inst_uses _)`)) >>
         simp[] >> metis_tac[fn_inst_wf_def, EVERY_MEM]) >>
      `MEM bb' fn'.fn_blocks` by
        (simp[] >> metis_tac[MEM_LUPDATE, EL_MEM, EL_LUPDATE, LENGTH_LUPDATE]) >>
      qpat_x_assum `fn' = _` kall_tac >>
      simp[def_available_at_def] >> qexistsl [`bb'`, `def_inst`] >> simp[] >>
      metis_tac[]) >>
  `MEM def_bb fn'.fn_blocks` by
    (qpat_x_assum `MEM def_bb fn.fn_blocks` mp_tac >> simp[MEM_LUPDATE] >> metis_tac[]) >>
  qpat_x_assum `fn' = _` kall_tac >>
  simp[def_available_at_def] >> qexistsl [`def_bb`, `def_inst`] >> gvs[]
QED

Theorem mm_local_prefix_phase_endpoint_available[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  fn_inst_wf fn /\ wf_function fn /\
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  target'.bb_label = target.bb_label /\
  MEM v (venomInst$inst_uses u) /\
  ((MEM u (fn_insts fn0) /\
     ~MEM u (EL index fn0.fn_blocks).bb_instructions) \/
   (MEM u bb'.bb_instructions /\ u.inst_opcode = PHI)) /\
  def_available_at fn target NONE v ==>
  def_available_at fn' target' NONE v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
      (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM, MEM_MAP]) >>
  `bb.bb_label = (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mm_local_prefix_wf_last, wf_ssa_def, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `bb'.bb_label = bb.bb_label` by metis_tac[mm_local_phase_label] >>
  `MEM bb fn.fn_blocks` by
    (simp[] >> metis_tac[MEM_LUPDATE, EL_MEM, EL_LUPDATE, LENGTH_LUPDATE]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_function_def, mmWfProofsTheory.fn_inst_ids_distinct_block] >>
  irule mm_local_available_endpoint_transport >>
  goal_assum (drule_at (Pat `def_available_at _ _ _ _`)) >> simp[] >>
  rpt strip_tac >>
  Cases_on `db = bb`
  >- (qexists_tac `bb'` >> simp[] >>
      conj_tac >- (simp[] >> metis_tac[MEM_LUPDATE, EL_MEM, EL_LUPDATE, LENGTH_LUPDATE]) >>
      irule mm_local_prefix_phase_producer_retained >>
      (conj_tac >- metis_tac[fn_inst_wf_def, EVERY_MEM]) >>
      goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `MEM _ (venomInst$inst_uses _)`)) >>
      gvs[] >> metis_tac[]) >>
  qexists_tac `db` >> simp[] >>
  metis_tac[MEM_LUPDATE]
QED

Theorem mm_local_prefix_phase_phi_transport[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  fn_inst_wf fn /\ wf_function fn /\
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks /\
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  fn_cfg_edge fn' = fn_cfg_edge fn /\
  target'.bb_label = target.bb_label /\
  ((MEM u (fn_insts fn0) /\
     ~MEM u (EL index fn0.fn_blocks).bb_instructions) \/
   (MEM u bb'.bb_instructions /\ u.inst_opcode = PHI)) /\
  phi_edge_uses_wf fn target u ==>
  phi_edge_uses_wf fn' target' u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
      (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM, MEM_MAP]) >>
  `bb.bb_label = (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mm_local_prefix_wf_last, wf_ssa_def, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `bb'.bb_label = bb.bb_label` by metis_tac[mm_local_phase_label] >>
  qpat_x_assum `phi_edge_uses_wf _ _ _` mp_tac >>
  pure_rewrite_tac[phi_edge_uses_wf_def] >> strip_tac >>
  pure_rewrite_tac[phi_edge_uses_wf_def] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
  `MEM v (venomInst$inst_uses u)` by
    (simp[venomInstTheory.inst_uses_def] >>
     irule basePtrProofsTheory.phi_pairs_mem_operand_vars >>
     simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  first_x_assum (drule_at (Pat `MEM _ (phi_pairs _)`)) >> strip_tac >>
  Cases_on `pred_bb = bb`
  >- (qexists_tac `bb'` >>
      `MEM bb' fn'.fn_blocks` by
        (simp[] >> metis_tac[MEM_LUPDATE, EL_MEM, EL_LUPDATE, LENGTH_LUPDATE]) >>
      simp[] >>
      conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
      irule mm_local_prefix_phase_endpoint_available >>
      goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `MEM _ (venomInst$inst_uses _)`)) >>
      simp[] >> metis_tac[]) >>
  qexists_tac `pred_bb` >>
  `MEM pred_bb fn'.fn_blocks` by
    (qpat_x_assum `MEM pred_bb fn.fn_blocks` mp_tac >>
     simp[MEM_LUPDATE] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  irule mm_local_prefix_phase_endpoint_available >>
  goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `MEM _ (venomInst$inst_uses _)`)) >>
  simp[] >> metis_tac[]
QED

Theorem mm_local_prefix_phase_dominates_uses[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks ==>
  def_dominates_uses fn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ssa_form fn0 /\ k <= 4 /\ SUC k <= 4` by
    (gvs[wf_ssa_def] >> decide_tac) >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
      (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM, MEM_MAP]) >>
  `bb.bb_label = (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mm_local_prefix_wf_last] >>
  `bb'.bb_label = bb.bb_label` by metis_tac[mm_local_phase_label] >>
  `fn_cfg_edge fn = fn_cfg_edge fn0 /\
    (!d n. fn_dominates fn d n <=> fn_dominates fn0 d n)` by
    (drule_all mm_local_prefix_cfg_transport >> simp[]) >>
  `mm_local_prefix fn0 supply index (SUC k) = (bb',sk')` by
    metis_tac[mm_local_prefix_suc] >>
  `fn_cfg_edge fn' = fn_cfg_edge fn0 /\
    (!d n. fn_dominates fn' d n <=> fn_dominates fn0 d n) /\
    all_reachable fn' /\ fn_labels fn' = fn_labels fn0` by
    (qpat_x_assum `mm_local_prefix _ _ _ k = _` kall_tac >>
     qpat_x_assum `fn = _` kall_tac >>
     drule_all mm_local_prefix_cfg_transport >> simp[]) >>
  `!d n. fn_dominates fn d n ==> fn_dominates fn' d n` by metis_tac[] >>
  `MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks` by
    (simp[] >> metis_tac[MEM_LUPDATE, EL_MEM, EL_LUPDATE, LENGTH_LUPDATE]) >>
  `fn_dominates fn' bb'.bb_label bb'.bb_label` by
    (simp[fn_dominates_def] >> conj_tac
     >- (qpat_x_assum `all_reachable fn0` mp_tac >>
         simp[all_reachable_def] >> metis_tac[EL_MEM]) >>
     metis_tac[LAST_MEM]) >>
  qpat_x_assum `mm_local_prefix _ _ _ (SUC _) = _` kall_tac >>
  pure_rewrite_tac[def_dominates_uses_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `bb'' = bb'`
  >- (qpat_x_assum `bb'' = bb'` SUBST_ALL_TAC >>
      Cases_on `inst.inst_opcode = PHI` >> simp[]
      >- (`MEM inst bb.bb_instructions` by
            (qpat_x_assum `mm_local_phase _ _ _ = _` mp_tac >>
             Cases_on `EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]` >>
             simp[mm_local_phase_def] >>
             metis_tac[mmSupplyWfProofsTheory.transform_block_mode_supply_phi_origin,
               mmSupplyWfProofsTheory.transform_block_memzero_supply_phi_origin]) >>
          `phi_edge_uses_wf fn bb inst` by
            metis_tac[wf_ssa_def, def_dominates_uses_def] >>
          irule mm_local_prefix_phase_phi_transport >>
          goal_assum (drule_at (Pat `mm_local_prefix _ _ _ k = _`)) >>
          goal_assum (drule_at (Pat `phi_edge_uses_wf _ _ _`)) >>
          simp[] >> metis_tac[]) >>
      rpt strip_tac >>
      `MEM v (venomInst$inst_uses inst)` by
        simp[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
      qpat_x_assum `MEM inst bb'.bb_instructions` mp_tac >>
      simp[MEM_EL] >> strip_tac >>
      metis_tac[mm_local_prefix_phase_ordinary_available]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    metis_tac[wf_function_def, venomInstTheory.fn_labels_def] >>
  `bb''.bb_label <> (EL index fn0.fn_blocks).bb_label` by
    metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  `MEM bb'' fn0.fn_blocks /\ MEM bb'' fn.fn_blocks` by
    (qpat_x_assum `MEM bb'' fn'.fn_blocks` mp_tac >>
     simp[MEM_LUPDATE] >> metis_tac[MEM_EL]) >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (`phi_edge_uses_wf fn bb'' inst` by
        metis_tac[wf_ssa_def, def_dominates_uses_def] >>
      `MEM inst (fn_insts fn0) /\
       ~MEM inst (EL index fn0.fn_blocks).bb_instructions` by
        (conj_tac >- metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM] >>
         metis_tac[wf_function_def, scfg_instruction_block_unique, EL_MEM]) >>
      irule mm_local_prefix_phase_phi_transport >>
      goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `phi_edge_uses_wf _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM v (venomInst$inst_uses inst)` by
    simp[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  `def_available_at fn bb'' (SOME inst) v` by
    metis_tac[wf_ssa_def, def_dominates_uses_def] >>
  irule mm_local_prefix_phase_external_available >> metis_tac[]
QED

Definition mm_local_inst_covered_def:
  mm_local_inst_covered s i <=>
    MEM i.inst_id s.irs_used_inst_ids /\ i.inst_id < s.irs_next_inst /\
    list_subset (irSupply$inst_ir_vars i) s.irs_used_vars /\
    list_subset (irSupply$inst_ir_labels i) s.irs_used_labels
End

Theorem mm_local_extends_refl[local]:
  ir_supply_extends s s
Proof
  simp[ir_supply_extends_def, list_subset_def, EVERY_MEM]
QED

Theorem mm_local_extends_trans[local]:
  ir_supply_extends s t /\ ir_supply_extends t u ==> ir_supply_extends s u
Proof
  simp[ir_supply_extends_def, list_subset_def, EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem mm_local_inst_covered_mono[local]:
  ir_supply_extends s t /\ mm_local_inst_covered s i ==>
  mm_local_inst_covered t i
Proof
  simp[ir_supply_extends_def, mm_local_inst_covered_def, list_subset_def, EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem mm_local_mode_resources[local]:
  apply_groups_inst_supply mode ns rm s i = (out,t) ==>
  ir_supply_extends s t /\
  (mm_local_inst_covered s i ==> EVERY (mm_local_inst_covered t) out)
Proof
  simp[apply_groups_inst_supply_def] >>
  Cases_on `MEM i.inst_id ns` >> simp[]
  >- (strip_tac >> gvs[mm_local_extends_refl, mm_local_inst_covered_def,
       mk_nop_from_def, irSupplyTheory.inst_ir_vars_def,
       irSupplyTheory.inst_ir_labels_def, venomInstTheory.inst_uses_def,
       irSupplyTheory.operand_ir_labels_def, venomInstTheory.operand_vars_def,
       list_subset_def]) >>
  Cases_on `ALOOKUP rm i.inst_id` >> simp[]
  >- (strip_tac >> gvs[mm_local_extends_refl]) >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >>
  gvs[irSupplyTheory.fresh_inst_id_def, AllCaseEqs()] >>
  imp_res_tac irSupplyTheory.fresh_ir_var_contract >>
  gvs[ir_supply_extends_def, mm_local_inst_covered_def,
    mk_bulk_copy_inst_def, mk_load_inst_def, mk_mstore_from_load_def,
    irSupplyTheory.inst_ir_vars_def, irSupplyTheory.inst_ir_labels_def,
    venomInstTheory.inst_uses_def, irSupplyTheory.operand_ir_labels_def,
    venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
    list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Theorem mm_local_zero_resources[local]:
  apply_memzero_inst_supply ns rm s i = (out,t) ==>
  ir_supply_extends s t /\
  (mm_local_inst_covered s i ==> EVERY (mm_local_inst_covered t) out)
Proof
  simp[apply_memzero_inst_supply_def] >>
  Cases_on `MEM i.inst_id ns` >> simp[]
  >- (strip_tac >> gvs[mm_local_extends_refl, mm_local_inst_covered_def,
       mk_nop_from_def, irSupplyTheory.inst_ir_vars_def,
       irSupplyTheory.inst_ir_labels_def, venomInstTheory.inst_uses_def,
       irSupplyTheory.operand_ir_labels_def, venomInstTheory.operand_vars_def,
       list_subset_def]) >>
  Cases_on `ALOOKUP rm i.inst_id` >> simp[]
  >- (strip_tac >> gvs[mm_local_extends_refl]) >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >>
  gvs[irSupplyTheory.fresh_inst_id_def, AllCaseEqs()] >>
  imp_res_tac irSupplyTheory.fresh_ir_var_contract >>
  gvs[ir_supply_extends_def, mm_local_inst_covered_def,
    mk_zero_store_inst_def, mk_memzero_calldatacopy_def,
    irSupplyTheory.inst_ir_vars_def, irSupplyTheory.inst_ir_labels_def,
    venomInstTheory.inst_uses_def, irSupplyTheory.operand_ir_labels_def,
    venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
    list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Theorem mm_local_list_resources[local]:
  (!s i out t. f s i = (out,t) ==>
    ir_supply_extends s t /\
    (mm_local_inst_covered s i ==> EVERY (mm_local_inst_covered t) out)) ==>
  !xs s ys t. mm_flat_map_supply f s xs = (ys,t) ==>
    ir_supply_extends s t /\
    (EVERY (mm_local_inst_covered s) xs ==> EVERY (mm_local_inst_covered t) ys)
Proof
  strip_tac >> Induct >> simp[mm_flat_map_supply_def, mm_local_extends_refl] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `!s i out t. f s i = _ ==> _` drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- metis_tac[mm_local_extends_trans] >>
  strip_tac >>
  `EVERY (mm_local_inst_covered s1) xs` by
    (gvs[EVERY_MEM] >> metis_tac[mm_local_inst_covered_mono]) >>
  simp[EVERY_APPEND] >> gvs[EVERY_MEM] >> metis_tac[mm_local_inst_covered_mono]
QED

Theorem mm_local_phase_resources[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) ==>
  ir_supply_extends s t /\ cc.bb_label = bb.bb_label /\
  (EVERY (mm_local_inst_covered s) bb.bb_instructions ==>
    EVERY (mm_local_inst_covered t) cc.bb_instructions)
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_mode_supply_def,
    transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_local_list_resources >>
  (impl_tac >- metis_tac[mm_local_mode_resources, mm_local_zero_resources]) >> simp[]
QED

Theorem mm_local_prefix_resources[local]:
  !fn0 supply index k bb sk.
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) ==>
  ir_supply_extends supply sk /\ bb.bb_label = (EL index fn0.fn_blocks).bb_label /\
  (EVERY (mm_local_inst_covered supply) (EL index fn0.fn_blocks).bb_instructions ==>
    EVERY (mm_local_inst_covered sk) bb.bb_instructions)
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero, mm_local_extends_refl] >>
  rpt gen_tac >> strip_tac >>
  `k < 4 /\ k <= 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `ir_supply_extends supply sp /\ prev.bb_label = (EL index fn0.fn_blocks).bb_label /\
    (EVERY (mm_local_inst_covered supply) (EL index fn0.fn_blocks).bb_instructions ==>
      EVERY (mm_local_inst_covered sp) prev.bb_instructions)` by
    (first_x_assum irule >> simp[]) >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  drule mm_local_phase_resources >> strip_tac >>
  metis_tac[mm_local_extends_trans]
QED

Theorem mm_local_supply_coverage[local]:
  ir_supply_covers_fn s fn <=>
  MEM fn.fn_name s.irs_used_labels /\
  !bb. MEM bb fn.fn_blocks ==>
    MEM bb.bb_label s.irs_used_labels /\
    EVERY (mm_local_inst_covered s) bb.bb_instructions
Proof
  rewrite_tac[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
    irSupplyTheory.fn_ir_vars_def, irSupplyTheory.fn_ir_labels_def,
    list_subset_def] >>
  simp[EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF,
    irSupplyTheory.block_ir_inst_ids_def, irSupplyTheory.block_ir_vars_def,
    irSupplyTheory.block_ir_labels_def] >>
  simp[EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF,
    mm_local_inst_covered_def, list_subset_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem mm_local_prefix_supply_covers[local]:
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) ==>
  ir_supply_covers_fn sk (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
Proof
  strip_tac >> drule_all mm_local_prefix_resources >> strip_tac >>
  `MEM (EL index fn0.fn_blocks) fn0.fn_blocks` by simp[EL_MEM] >>
  `MEM fn0.fn_name supply.irs_used_labels /\
   !b. MEM b fn0.fn_blocks ==>
     MEM b.bb_label supply.irs_used_labels /\
     EVERY (mm_local_inst_covered supply) b.bb_instructions` by
    gvs[mm_local_supply_coverage] >>
  `EVERY (mm_local_inst_covered sk) bb.bb_instructions` by metis_tac[] >>
  simp[mm_local_supply_coverage] >> conj_tac
  >- (gvs[ir_supply_extends_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  `!b. MEM b fn0.fn_blocks ==>
    MEM b.bb_label sk.irs_used_labels /\
    EVERY (mm_local_inst_covered sk) b.bb_instructions` by
    (rpt strip_tac
     >- (gvs[ir_supply_extends_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
     gvs[EVERY_MEM] >> metis_tac[mm_local_inst_covered_mono]) >>
  rpt strip_tac >> gvs[MEM_LUPDATE] >> metis_tac[EL_MEM]
QED

Theorem mm_local_prefix_function_wf[local]:
  fn_inst_wf fn0 /\ wf_function fn0 /\ ssa_form fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) ==>
  wf_function (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM, MEM_MAP]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions)` by
    metis_tac[wf_function_def, mmWfProofsTheory.fn_inst_ids_distinct_block, EL_MEM] >>
  drule_all mm_local_prefix_ids >> strip_tac >>
  drule_all mm_local_prefix_wf_last >> strip_tac >>
  `fn_inst_ids_distinct (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (simp[fn_inst_ids_distinct_def] >> irule (cj 1 mm_projection_lupdate_ids) >>
     gvs[wf_function_def, fn_inst_ids_distinct_def, ir_supply_covers_fn_def,
       irSupplyTheory.fn_ir_inst_ids_def, irSupplyTheory.block_ir_inst_ids_def] >>
     qexistsl [`supply.irs_next_inst`, `sk.irs_next_inst`] >>
     gvs[irSupplyTheory.block_ir_inst_ids_def, EVERY_MAP, combinTheory.o_DEF] >>
     conj_tac
     >- (rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
     gvs[EVERY_FLAT, EVERY_MAP, irSupplyTheory.block_ir_inst_ids_def,
       combinTheory.o_DEF]) >>
  irule mmWfProofsTheory.indexed_replacement_wf >> simp[] >>
  `bb.bb_instructions <> [] /\ (EL index fn0.fn_blocks).bb_instructions <> []` by
    metis_tac[wf_function_def, EL_MEM, bb_well_formed_def] >>
  simp[venomInstTheory.bb_succs_def] >>
  Cases_on `bb.bb_instructions` >>
  Cases_on `(EL index fn0.fn_blocks).bb_instructions` >> gvs[]
QED

Theorem mm_local_prefix_frame[local]:
  !fn0 supply index k bb sk L R.
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  mm_frame supply.irs_used_vars L
    (FLAT (MAP (\i. i.inst_outputs) (EL index fn0.fn_blocks).bb_instructions)) R ==>
  mm_frame sk.irs_used_vars L (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) R
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_frame sp.irs_used_vars L
    (FLAT (MAP (\i. i.inst_outputs) prev.bb_instructions)) R` by
    (first_x_assum irule >> simp[]) >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  Cases_on `EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]` >>
  gvs[mm_local_phase_def] >>
  metis_tac[transform_block_mode_supply_frame, transform_block_memzero_supply_frame]
QED

Theorem mm_local_prefix_ssa_form[local]:
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  index < LENGTH fn0.fn_blocks /\ ssa_form fn0 /\
  ir_supply_covers_fn supply fn0 ==>
  ssa_form (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
Proof
  strip_tac >>
  `list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn0))) supply.irs_used_vars` by
    (simp[venomInstTheory.fn_insts_def] >> irule mm_supply_outputs_covered >>
     gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_vars_def]) >>
  simp[ssa_form_def, venomInstTheory.fn_insts_def, mmWfProofsTheory.block_outputs_projection] >>
  `mm_frame sk.irs_used_vars []
    (FLAT (MAP (\b. FLAT (MAP (\i. i.inst_outputs) b.bb_instructions))
      (LUPDATE bb index fn0.fn_blocks))) []` suffices_by simp[mm_frame_def] >>
  irule mm_projection_lupdate_frame >> simp[] >>
  qexists_tac `supply.irs_used_vars` >> simp[] >> reverse conj_tac
  >- gvs[mm_frame_def, ssa_form_def, venomInstTheory.fn_insts_def, mmWfProofsTheory.block_outputs_projection] >>
  metis_tac[mm_local_prefix_frame]
QED

Theorem mm_local_prefix_inst_wf[local]:
  !fn0 supply index k bb sk.
  fn_inst_wf fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) ==>
  fn_inst_wf (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero, LUPDATE_SAME] >>
  rpt gen_tac >> strip_tac >>
  `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `fn_inst_wf (fn0 with fn_blocks := LUPDATE prev index fn0.fn_blocks)` by
    (first_x_assum irule >> simp[]) >>
  `EVERY inst_wf prev.bb_instructions` by
    (gvs[fn_inst_wf_compute, EVERY_MEM] >> metis_tac[MEM_LUPDATE]) >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `EVERY inst_wf bb.bb_instructions` by
    (Cases_on `EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]` >>
     gvs[mm_local_phase_def] >>
     metis_tac[transform_block_mode_supply_inst_wf,
       transform_block_memzero_supply_inst_wf]) >>
  gvs[fn_inst_wf_compute, EVERY_MEM, MEM_LUPDATE] >> metis_tac[]
QED

Theorem mm_local_prefix_wf_ssa[local]:
  !fn0 supply index k bb sk.
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) ==>
  wf_ssa (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- simp[mm_local_prefix_zero, LUPDATE_SAME] >>
  rpt gen_tac >> strip_tac >>
  `k < 4 /\ k <= 4 /\ ssa_form fn0` by (gvs[wf_ssa_def] >> decide_tac) >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `wf_ssa (fn0 with fn_blocks := LUPDATE prev index fn0.fn_blocks)` by
    (first_x_assum irule >> simp[]) >>
  `fn_inst_wf (fn0 with fn_blocks := LUPDATE prev index fn0.fn_blocks) /\
    wf_function (fn0 with fn_blocks := LUPDATE prev index fn0.fn_blocks)` by
    metis_tac[mm_local_prefix_inst_wf, mm_local_prefix_function_wf] >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `def_dominates_uses (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (irule mm_local_prefix_phase_dominates_uses >>
     goal_assum (drule_at (Pat `mm_local_prefix _ _ _ k = _`)) >> simp[] >>
     metis_tac[]) >>
  simp[wf_ssa_def] >> irule mm_local_prefix_ssa_form >> metis_tac[]
QED

Theorem mm_local_prefix_structure[local]:
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks ==>
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ all_reachable fn /\
  ir_supply_covers_fn sk fn /\ fn_entry_label fn = fn_entry_label fn0
Proof
  strip_tac >>
  `ssa_form fn0` by gvs[wf_ssa_def] >>
  `EVERY (\i. i.inst_id < supply.irs_next_inst)
    (EL index fn0.fn_blocks).bb_instructions` by
    (gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM, MEM_MAP]) >>
  drule_all mm_local_prefix_cfg_transport >> strip_tac >>
  `fn_inst_wf fn` by metis_tac[mm_local_prefix_inst_wf] >>
  `wf_function fn` by metis_tac[mm_local_prefix_function_wf] >>
  `wf_ssa fn` by metis_tac[mm_local_prefix_wf_ssa] >>
  `ir_supply_covers_fn sk fn` by metis_tac[mm_local_prefix_supply_covers] >>
  simp[]
QED

Theorem mm_local_phase_structure[local]:
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (bb,sk) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks ==>
  fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\ all_reachable fn' /\
  ir_supply_covers_fn sk' fn' /\ fn_entry_label fn' = fn_entry_label fn0
Proof
  strip_tac >>
  `SUC k <= 4 /\ mm_local_prefix fn0 supply index (SUC k) = (bb',sk')` by
    (simp[mm_local_prefix_suc] >> decide_tac) >>
  irule mm_local_prefix_structure >> metis_tac[]
QED

Theorem mm_local_zero_merge_bound[local]:
  d1 <= d2 /\ d1 + n1 <= eom /\ d2 + n2 <= eom ==>
  d1 + (MAX (d1+n1) (d2+n2) - d1) <= eom
Proof
  simp[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem mm_local_zero_replace_merge[local]:
  d1 <= d2 /\ d2 <= d1+n1 /\
  MAX (d1+n1) (d2+n2) <= LENGTH mem ==>
  replace_bytes d2 (REPLICATE n2 0w)
    (replace_bytes d1 (REPLICATE n1 0w) mem) =
  replace_bytes d1 (REPLICATE (MAX (d1+n1) (d2+n2)-d1) 0w) mem
Proof
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE,
    LENGTH_DROP, LENGTH_REPLICATE] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
    LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE, arithmeticTheory.MAX_DEF] >>
  gvs[]
QED

Theorem mm_local_expand_mem_max[local]:
  expand_mem (expand_mem mem n) m = expand_mem mem (MAX n m)
Proof
  Cases_on `n <= m`
  >- (`MAX n m = m` by (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      simp[expand_mem_monotone]) >>
  `MAX n m = n` by simp[arithmeticTheory.MAX_DEF] >>
  `~(m > LENGTH (expand_mem mem n))` by
    (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  simp[Once expand_mem_def]
QED

Theorem mm_local_zero_write_merge[local]:
  d1 <= d2 /\ d2 <= d1+n1 ==>
  write_memory_with_expansion d2 (REPLICATE n2 0w)
    (write_memory_with_expansion d1 (REPLICATE n1 0w) s) =
  write_memory_with_expansion d1
    (REPLICATE (MAX (d1+n1) (d2+n2)-d1) 0w) s
Proof
  strip_tac >> simp[write_as_replace] >>
  `d1+n1 <= LENGTH (expand_mem s.vs_memory (d1+n1))` by simp[expand_mem_ge] >>
  simp[expand_replace] >>
  `d1 + (MAX (d1+n1) (d2+n2) - d1) = MAX (d1+n1) (d2+n2)` by
    (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  simp[venomStateTheory.venom_state_component_equality] >>
  simp[mm_local_expand_mem_max] >>
  irule mm_local_zero_replace_merge >> simp[]
QED

(* Analysis ancestry retains empty-copy endpoints as well as byte geometry.
   Defining-load IDs may be shared; this relation does not assert ownership. *)
Definition mm_local_copy_ancestor_def:
  mm_local_copy_ancestor h g <=>
    (!id. MEM id h.cg_inst_ids ==> MEM id g.cg_inst_ids) /\
    g.cg_dst <= h.cg_dst /\
    h.cg_dst + h.cg_length <= g.cg_dst + g.cg_length /\
    h.cg_src + g.cg_dst = h.cg_dst + g.cg_src
End

Theorem mm_local_copy_ancestor_refl[local]:
  mm_local_copy_ancestor h h
Proof
  simp[mm_local_copy_ancestor_def]
QED

Theorem mm_local_copy_ancestor_trans[local]:
  mm_local_copy_ancestor h g /\ mm_local_copy_ancestor g f ==>
  mm_local_copy_ancestor h f
Proof
  rw[mm_local_copy_ancestor_def]
QED

Theorem mm_local_copy_merge_ancestors[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  mm_local_copy_ancestor c1 (copy_merge c1 c2) /\
  mm_local_copy_ancestor c2 (copy_merge c1 c2)
Proof
  simp[mm_local_copy_ancestor_def, copy_merge_def, copy_can_merge_def,
       MEM_APPEND] >>
  rpt strip_tac >>
  simp[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem mm_local_insert_sorted_mem[local]:
  !cs c h. MEM h (insert_sorted cs c) <=> h = c \/ MEM h cs
Proof
  Induct >> simp[insert_sorted_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem mm_local_insert_sorted_order[local]:
  !cs c. SORTED (\a b. a.cg_dst <= b.cg_dst) cs ==>
    SORTED (\a b. a.cg_dst <= b.cg_dst) (insert_sorted cs c)
Proof
  Induct >> simp[insert_sorted_def] >>
  rpt gen_tac >>
  simp[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
  strip_tac >> IF_CASES_TAC >>
  simp[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
       mm_local_insert_sorted_mem] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.LESS_IMP_LESS_OR_EQ, arithmeticTheory.NOT_LESS]
QED

Theorem mm_local_merge_adjacent_lower_bound[local]:
  !cs. EVERY (\g. d <= g.cg_dst) cs ==>
    EVERY (\g. d <= g.cg_dst) (merge_adjacent cs)
Proof
  ho_match_mp_tac mm_local_merge_every >> simp[copy_merge_def]
QED

Theorem mm_local_merge_adjacent_order[local]:
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs ==>
    SORTED (\a b. a.cg_dst <= b.cg_dst) (merge_adjacent cs)
Proof
  recInduct merge_adjacent_ind >> simp[merge_adjacent_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2`
  >- (gvs[] >> first_x_assum match_mp_tac >>
      gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
          copy_merge_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[] >>
  simp[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
  mp_tac (Q.SPEC `c2::rest`
    (Q.INST [`d` |-> `c1.cg_dst`] mm_local_merge_adjacent_lower_bound)) >>
  simp[EVERY_MEM] >>
  gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem mm_local_merge_adjacent_ancestry[local]:
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs ==>
    !h. MEM h cs ==> ?g. MEM g (merge_adjacent cs) /\
      mm_local_copy_ancestor h g
Proof
  recInduct merge_adjacent_ind >>
  simp[merge_adjacent_def, mm_local_copy_ancestor_refl] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2`
  >- (gvs[] >>
      `SORTED (\a b. a.cg_dst <= b.cg_dst) (copy_merge c1 c2::rest)` by
        (gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
             copy_merge_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      first_x_assum drule >> strip_tac >>
      `c1.cg_dst <= c2.cg_dst` by gvs[sortingTheory.SORTED_DEF] >>
      drule_all mm_local_copy_merge_ancestors >> strip_tac >>
      metis_tac[mm_local_copy_ancestor_trans]) >>
  gvs[] >> metis_tac[mm_local_copy_ancestor_refl]
QED

Theorem mm_local_add_copy_order[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) cs ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (add_copy cs c)
Proof
  simp[add_copy_def] >>
  metis_tac[mm_local_insert_sorted_order, mm_local_merge_adjacent_order]
QED

Theorem mm_local_add_copy_ancestry[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\ MEM h (c::cs) ==>
  ?g. MEM g (add_copy cs c) /\ mm_local_copy_ancestor h g
Proof
  strip_tac >> simp[add_copy_def] >>
  irule mm_local_merge_adjacent_ancestry >>
  metis_tac[mm_local_insert_sorted_mem, mm_local_insert_sorted_order, MEM]
QED

Theorem mm_local_flush_fragment[local]:
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  MEM h ((flush_copies ss cs).ss_copies ++ (flush_copies ss cs).ss_flushed)
Proof
  simp[flush_copies_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_flush_order[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (flush_copies ss cs).ss_copies
Proof
  simp[flush_copies_def] >> strip_tac >> irule sortingTheory.SORTED_FILTER >>
  simp[relationTheory.transitive_def]
QED

Theorem mm_local_hazards_fragment[local]:
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  MEM h ((flush_hazards mode ss c).ss_copies ++
         (flush_hazards mode ss c).ss_flushed)
Proof
  simp[flush_hazards_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> metis_tac[mm_local_flush_fragment, MEM_APPEND]
QED

Theorem mm_local_hazards_order[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (flush_hazards mode ss c).ss_copies
Proof
  simp[flush_hazards_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> metis_tac[mm_local_flush_order]
QED

Theorem mm_local_load_order[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (scan_load mode ss inst).ss_copies
Proof
  strip_tac >> simp[scan_load_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def] >> rpt IF_CASES_TAC >> simp[mm_local_flush_order]
QED

Theorem mm_local_store_order[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (scan_store dfg mode ss inst).ss_copies
Proof
  strip_tac >> simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def] >> irule mm_local_add_copy_order >>
  irule mm_local_hazards_order >>
  simp[invalidate_loads_def]
QED

Theorem mm_local_bulk_order[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (scan_bulk_copy mode ss inst).ss_copies
Proof
  strip_tac >> simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def] >> irule mm_local_add_copy_order >>
  irule mm_local_hazards_order >>
  simp[invalidate_loads_def]
QED

Theorem mm_local_inst_order[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst) (scan_inst dfg mode ss inst).ss_copies
Proof
  simp[scan_inst_def] >> rpt IF_CASES_TAC >>
  simp[mm_local_load_order, mm_local_store_order, mm_local_bulk_order,
       hard_barrier_def]
QED

Theorem mm_local_insert_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  ?g. MEM g (add_copy ss.ss_copies c ++ ss.ss_flushed) /\
    mm_local_copy_ancestor h g
Proof
  simp[MEM_APPEND] >> rpt strip_tac
  >- (drule mm_local_add_copy_ancestry >>
      disch_then (qspecl_then [`h`, `c`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  metis_tac[mm_local_copy_ancestor_refl]
QED

Theorem mm_local_load_fragment[local]:
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  MEM h ((scan_load mode ss inst).ss_copies ++ (scan_load mode ss inst).ss_flushed)
Proof
  strip_tac >> simp[scan_load_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def] >> metis_tac[mm_local_flush_fragment, MEM_APPEND]
QED

Theorem mm_local_barrier_fragment[local]:
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  ?g. MEM g ((hard_barrier ss).ss_copies ++ (hard_barrier ss).ss_flushed) /\
    mm_local_copy_ancestor h g
Proof
  simp[hard_barrier_def, MEM_APPEND] >>
  metis_tac[mm_local_copy_ancestor_refl]
QED

Theorem mm_local_hazards_insert_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  ?g. MEM g (add_copy (flush_hazards mode ss c).ss_copies c ++
             (flush_hazards mode ss c).ss_flushed) /\
    mm_local_copy_ancestor h g
Proof
  strip_tac >> irule mm_local_insert_fragment >>
  simp[mm_local_hazards_fragment, mm_local_hazards_order]
QED

Theorem mm_local_store_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  ?g. MEM g ((scan_store dfg mode ss inst).ss_copies ++
             (scan_store dfg mode ss inst).ss_flushed) /\
    mm_local_copy_ancestor h g
Proof
  strip_tac >> simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  gvs[MEM_APPEND] >>
  simp[SRULE [MEM_APPEND] mm_local_barrier_fragment] >>
  irule (SRULE [MEM_APPEND] mm_local_hazards_insert_fragment) >>
  simp[invalidate_loads_def]
QED

Theorem mm_local_bulk_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  ?g. MEM g ((scan_bulk_copy mode ss inst).ss_copies ++
             (scan_bulk_copy mode ss inst).ss_flushed) /\
    mm_local_copy_ancestor h g
Proof
  strip_tac >> simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  gvs[MEM_APPEND] >>
  simp[SRULE [MEM_APPEND] mm_local_barrier_fragment] >>
  irule (SRULE [MEM_APPEND] mm_local_hazards_insert_fragment) >>
  simp[invalidate_loads_def]
QED

Theorem mm_local_inst_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  ?g. MEM g ((scan_inst dfg mode ss inst).ss_copies ++
             (scan_inst dfg mode ss inst).ss_flushed) /\
    mm_local_copy_ancestor h g
Proof
  strip_tac >> simp[scan_inst_def] >> rpt IF_CASES_TAC >>
  metis_tac[mm_local_load_fragment, mm_local_copy_ancestor_refl,
    mm_local_store_fragment, mm_local_bulk_fragment,
    mm_local_barrier_fragment, MEM_APPEND]
QED

Theorem mm_local_fold_order[local]:
  !xs ss. SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  SORTED (\a b. a.cg_dst <= b.cg_dst)
    (FOLDL (scan_inst dfg mode) ss xs).ss_copies
Proof
  Induct >> simp[] >> metis_tac[mm_local_inst_order]
QED

Theorem mm_local_fold_fragment[local]:
  !xs ss h. SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) ==>
  ?g. MEM g ((FOLDL (scan_inst dfg mode) ss xs).ss_copies ++
             (FOLDL (scan_inst dfg mode) ss xs).ss_flushed) /\
    mm_local_copy_ancestor h g
Proof
  Induct
  >- (simp[] >> metis_tac[mm_local_copy_ancestor_refl]) >>
  pure_rewrite_tac[FOLDL] >> rpt strip_tac >>
  drule_all mm_local_inst_fragment >>
  disch_then (qspecl_then [`mode`, `h`, `dfg`] strip_assume_tac) >>
  first_x_assum (qspec_then `scan_inst dfg mode ss h` mp_tac) >>
  simp[mm_local_inst_order] >>
  disch_then (qspec_then `g` mp_tac) >>
  simp[] >> metis_tac[mm_local_copy_ancestor_trans, MEM_APPEND]
QED

Theorem mm_local_hazards_flushed_extension[local]:
  ?tail. (flush_hazards mode ss c).ss_flushed = ss.ss_flushed ++ tail
Proof
  simp[flush_hazards_def] >> rpt IF_CASES_TAC >>
  simp[flush_copies_def, APPEND_ASSOC]
QED

Theorem mm_local_load_flushed_extension[local]:
  ?tail. (scan_load mode ss inst).ss_flushed = ss.ss_flushed ++ tail
Proof
  simp[scan_load_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def] >> rpt IF_CASES_TAC >> simp[flush_copies_def]
QED

Theorem mm_local_store_flushed_extension[local]:
  ?tail. (scan_store dfg mode ss inst).ss_flushed = ss.ss_flushed ++ tail
Proof
  simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def] >>
  simp[flush_hazards_def, invalidate_loads_def] >>
  rpt IF_CASES_TAC >> simp[flush_copies_def, APPEND_ASSOC]
QED

Theorem mm_local_bulk_flushed_extension[local]:
  ?tail. (scan_bulk_copy mode ss inst).ss_flushed = ss.ss_flushed ++ tail
Proof
  simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[hard_barrier_def] >>
  simp[flush_hazards_def, invalidate_loads_def] >>
  rpt IF_CASES_TAC >> simp[flush_copies_def, APPEND_ASSOC]
QED

Theorem mm_local_inst_flushed_extension[local]:
  ?tail. (scan_inst dfg mode ss inst).ss_flushed = ss.ss_flushed ++ tail
Proof
  simp[scan_inst_def] >> rpt IF_CASES_TAC >>
  simp[mm_local_load_flushed_extension, mm_local_store_flushed_extension,
       mm_local_bulk_flushed_extension, hard_barrier_def]
QED

Theorem mm_local_fold_flushed_extension[local]:
  !xs ss. ?tail.
    (FOLDL (scan_inst dfg mode) ss xs).ss_flushed = ss.ss_flushed ++ tail
Proof
  Induct
  >- (gen_tac >> qexists_tac `[]` >> simp[]) >>
  rpt gen_tac >> pure_rewrite_tac[FOLDL] >>
  first_x_assum (qspec_then `scan_inst dfg mode ss h` strip_assume_tac) >>
  qspecl_then [`ss`, `mode`, `h`, `dfg`] strip_assume_tac
    (GEN_ALL mm_local_inst_flushed_extension) >>
  simp[APPEND_ASSOC] >> metis_tac[]
QED

Theorem mm_local_prefix_final_fragment[local]:
  bb.bb_instructions = pre ++ post /\
  MEM h ((FOLDL (scan_inst dfg mode) empty_scan_state pre).ss_copies ++
         (FOLDL (scan_inst dfg mode) empty_scan_state pre).ss_flushed) ==>
  ?g. MEM g (scan_block dfg mode bb).ss_flushed /\
      mm_local_copy_ancestor h g
Proof
  strip_tac >> simp[scan_block_def, FOLDL_APPEND, hard_barrier_def] >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst)
     (FOLDL (scan_inst dfg mode) empty_scan_state pre).ss_copies` by
    (irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  drule_all mm_local_fold_fragment >>
  disch_then (qspecl_then [`mode`, `dfg`, `post`] mp_tac) >>
  metis_tac[MEM_APPEND]
QED

Theorem mm_local_hazards_new_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies ==>
  ?g. MEM g (add_copy (flush_hazards mode ss c).ss_copies c) /\
      mm_local_copy_ancestor c g
Proof
  strip_tac >> irule mm_local_add_copy_ancestry >>
  simp[mm_local_hazards_order]
QED

Theorem mm_local_store_new_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  inst.inst_operands = [dst_op; val_op] /\
  operand_var_name val_op = SOME var /\
  operand_lit_val dst_op = SOME dst /\
  FLOOKUP ss.ss_loads var = SOME src /\
  c = <| cg_dst := dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [inst.inst_id] ++
           (case dfg_get_def dfg var of NONE => [] | SOME li => [li.inst_id]) |> ==>
  ?g. MEM g (scan_store dfg mode ss inst).ss_copies /\
      mm_local_copy_ancestor c g
Proof
  strip_tac >> simp[scan_store_def] >>
  irule mm_local_hazards_new_fragment >>
  simp[invalidate_loads_def] >> IF_CASES_TAC >> simp[]
QED

Theorem mm_local_bulk_new_fragment[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  inst.inst_operands = [dst_op; src_op; size_op] /\
  operand_lit_val dst_op = SOME dst /\
  operand_lit_val src_op = SOME src /\
  operand_lit_val size_op = SOME len /\
  c = <| cg_dst := dst; cg_src := src; cg_length := len;
         cg_inst_ids := [inst.inst_id] |> ==>
  ?g. MEM g (scan_bulk_copy mode ss inst).ss_copies /\
      mm_local_copy_ancestor c g
Proof
  strip_tac >> simp[scan_bulk_copy_def] >>
  irule mm_local_hazards_new_fragment >>
  simp[invalidate_loads_def] >> IF_CASES_TAC >> simp[]
QED

Theorem mm_local_fold_ancestor[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) /\
  mm_local_copy_ancestor c h ==>
  ?g. MEM g (hard_barrier (FOLDL (scan_inst dfg mode) ss post)).ss_flushed /\
      mm_local_copy_ancestor c g
Proof
  strip_tac >> drule_all mm_local_fold_fragment >>
  disch_then (qspecl_then [`mode`, `dfg`, `post`] strip_assume_tac) >>
  simp[hard_barrier_def] >>
  metis_tac[MEM_APPEND, mm_local_copy_ancestor_trans]
QED

Theorem mm_local_prefix_cached_def_before_cut[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  bb.bb_instructions = pre ++ post /\
  FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state pre).ss_loads v = SOME a /\
  dfg_get_def (dfg_build_function fn0) v = SOME li ==>
  MEM li pre /\ li.inst_opcode = mode_load_opcode mode /\
  ?w. li.inst_operands = [Lit w] /\ li.inst_outputs = [v] /\ a = w2n w
Proof
  strip_tac >> drule mm_local_scan_lookup_origin >> strip_tac >>
  `MEM q bb.bb_instructions /\ MEM v q.inst_outputs` by simp[MEM_APPEND] >>
  `q = li` by (irule mm_local_prefix_producer_identify >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_prefix_fragment_ids_before_cut[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  bb.bb_instructions = pre ++ post /\
  MEM cg ((FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state pre).ss_copies ++
    (FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state pre).ss_flushed) /\ MEM id cg.cg_inst_ids ==>
  MEM id (MAP (\i. i.inst_id) pre)
Proof
  strip_tac >>
  `mm_local_scan_every
     (mm_local_group_roles (dfg_build_function fn0) mode pre)
     (FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state pre)` by
    (mp_tac (Q.SPECL [`pre`, `[]`, `[]`, `pre`]
       (Q.INST [`dfg` |-> `dfg_build_function fn0`] mm_local_fold_roles)) >>
     simp[mm_local_scan_every_def, empty_scan_state_def]) >>
  `mm_local_group_roles (dfg_build_function fn0) mode pre cg` by
    gvs[mm_local_scan_every_def, EVERY_MEM, MEM_APPEND] >>
  qpat_x_assum `mm_local_group_roles _ _ _ cg` mp_tac >>
  rewrite_tac[mm_local_group_roles_def] >>
  disch_then (qspec_then `id` mp_tac) >> simp[] >> strip_tac
  >- (simp[MEM_MAP] >> metis_tac[])
  >- (simp[MEM_MAP] >> metis_tac[]) >>
  `MEM q bb.bb_instructions /\ MEM v q.inst_outputs` by simp[MEM_APPEND] >>
  `q = li` by (irule mm_local_prefix_producer_identify >> metis_tac[]) >>
  simp[MEM_MAP] >> qexists_tac `q` >> gvs[MEM_APPEND]
QED

Theorem mm_local_prefix_rep_write[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM i bb.bb_instructions /\
  ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed) i.inst_id = SOME cg ==>
  i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  strip_tac >> drule alistTheory.ALOOKUP_MEM >>
  simp[rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >> strip_tac >>
  rename1 `IS_SOME opt` >> Cases_on `opt` >> gvs[] >>
  qpat_x_assum `SOME _ = rep_of_group _ _` (assume_tac o SYM) >>
  drule mm_local_rep_member >> strip_tac >> gvs[] >>
  drule_all mm_local_prefix_group_roles_elim >> strip_tac
  >- (`st = i` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >> gvs[])
  >- (rename1 `MEM copy_inst bb.bb_instructions` >>
      `copy_inst = i` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
      Cases_on `mode` >> gvs[mode_copy_opcode_def]) >>
  `MEM q bb.bb_instructions` by simp[MEM_APPEND] >>
  `q = i` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  metis_tac[mm_local_prefix_load_not_rep]
QED

Theorem mm_local_memzero_rep_write[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM i bb.bb_instructions /\
  ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block_memzero dfg bb).mz_flushed) i.inst_id = SOME cg ==>
  i.inst_opcode IN {MSTORE; CALLDATACOPY}
Proof
  strip_tac >> drule alistTheory.ALOOKUP_MEM >>
  simp[rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >> strip_tac >>
  rename1 `IS_SOME opt` >> Cases_on `opt` >> gvs[] >>
  qpat_x_assum `SOME _ = rep_of_group _ _` (assume_tac o SYM) >>
  drule mm_local_rep_member >> strip_tac >> gvs[] >>
  drule_all mm_local_memzero_group_roles >> strip_tac >>
  `i' = i` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  gvs[is_zero_store_def, is_calldatasize_copy_def]
QED

Theorem mm_local_mode_write_origin[local]:
  apply_groups_inst_supply mode ns rm s i = (out,t) /\ MEM j out /\
  j.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (!cg. ALOOKUP rm i.inst_id = SOME cg ==>
    i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}) ==>
  j.inst_id = i.inst_id /\
  i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def] >>
  Cases_on `mode` >> gvs[mode_load_opcode_def]
QED

Theorem mm_local_zero_write_origin[local]:
  apply_memzero_inst_supply ns rm s i = (out,t) /\ MEM j out /\
  j.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (!cg. ALOOKUP rm i.inst_id = SOME cg ==>
    i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}) ==>
  j.inst_id = i.inst_id /\
  i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  rw[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def]
QED

Theorem mm_local_list_write_origin[local]:
  !xs s ys t.
  (!u i out v j. MEM i xs /\ f u i = (out,v) /\ MEM j out /\
     j.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
     j.inst_id = i.inst_id /\
     i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}) /\
  mm_flat_map_supply f s xs = (ys,t) ==>
  !j. MEM j ys /\ j.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
  ?i. MEM i xs /\ i.inst_id = j.inst_id /\
      i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  Induct >> simp[mm_flat_map_supply_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum (qspecl_then [`s1`,`outs`,`t`] mp_tac) >>
  (impl_tac >- (conj_tac >- metis_tac[] >> simp[])) >>
  disch_tac >> gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  Cases_on `MEM j out`
  >- (qpat_x_assum `!u i out v j. _` (qspec_then `s` mp_tac) >>
      disch_then (qspec_then `h` mp_tac) >> simp[] >>
      disch_then drule >> metis_tac[])
  >> `MEM j outs` by metis_tac[] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
  metis_tac[]
QED

Theorem mm_local_prefix_phase_write_origin[local]:
  wf_ssa fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  mm_local_phase (dfg_build_function fn0) phase (bb,sk) = (cc,t) /\
  MEM j cc.bb_instructions /\
  j.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
  ?i. MEM i bb.bb_instructions /\ i.inst_id = j.inst_id /\
      i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  Cases_on `phase`
  >- (simp[mm_local_phase_def, transform_block_memzero_supply_def,
           AllCaseEqs()] >> strip_tac >> gvs[] >>
      drule_at (Pat `mm_flat_map_supply _ _ _ = _`)
        (SRULE [] mm_local_list_write_origin) >>
      disch_then (qspec_then `j` mp_tac) >> simp[] >>
      (impl_tac >- (rpt gen_tac >> strip_tac >>
        drule_at (Pat `apply_memzero_inst_supply _ _ _ _ = _`)
          (SRULE [] mm_local_zero_write_origin) >>
        disch_then (qspec_then `j'` mp_tac) >> simp[] >>
        (impl_tac >- metis_tac[SRULE [] mm_local_memzero_rep_write]) >> simp[])) >> simp[]) >>
  simp[mm_local_phase_def, transform_block_mode_supply_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`)
    (SRULE [] mm_local_list_write_origin) >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    drule_at (Pat `apply_groups_inst_supply _ _ _ _ _ = _`)
      (SRULE [] mm_local_mode_write_origin) >>
    disch_then (qspec_then `j'` mp_tac) >> simp[] >>
    (impl_tac >- metis_tac[SRULE [] mm_local_prefix_rep_write]) >> simp[])) >> simp[]
QED

Theorem mm_local_prefix_write_origin[local]:
  !fn0 supply index k bb sk w.
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM w bb.bb_instructions /\
  w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
  ?u. MEM u (EL index fn0.fn_blocks).bb_instructions /\
      u.inst_id = w.inst_id /\
      u.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  ntac 3 gen_tac >> Induct_on `k`
  >- (simp[mm_local_prefix_zero] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> `k < 4` by decide_tac >>
  Cases_on `mm_local_prefix fn0 supply index k` >>
  rename1 `mm_local_prefix fn0 supply index k = (prev,sp)` >>
  `mm_local_phase (dfg_build_function fn0)
    (EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])
    (prev,sp) = (bb,sk)` by metis_tac[mm_local_prefix_suc] >>
  `fn_inst_ids_distinct fn0 /\ MEM (EL index fn0.fn_blocks) fn0.fn_blocks` by
    (gvs[wf_function_def] >> metis_tac[MEM_EL]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) prev.bb_instructions)` by
    (irule mm_local_prefix_id_distinct >>
     qexistsl [`fn0`, `index`, `k`, `sp`, `supply`] >> simp[] >>
     conj_tac
     >- metis_tac[mmWfProofsTheory.fn_inst_ids_distinct_block] >>
     gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
         irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!id. _ ==> id < _` irule >>
     qexists_tac `MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions` >>
     conj_tac >- (qexists_tac `EL index fn0.fn_blocks` >> simp[]) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  `k <= 4` by decide_tac >>
  drule_all mm_local_prefix_phase_write_origin >> strip_tac >>
  first_x_assum (qspecl_then [`prev`,`sp`,`i`] mp_tac) >> simp[] >>
  metis_tac[]
QED

Theorem mm_local_prefix_write_not_def[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM w bb.bb_instructions /\
  w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  dfg_get_def (dfg_build_function fn0) v = SOME li ==>
  li.inst_id <> w.inst_id
Proof
  strip_tac >> drule_all mm_local_prefix_write_origin >> strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_correct_proof >> strip_tac >>
  `MEM u (fn_insts fn0)` by
    (irule mmWfProofsTheory.fn_insts_mem_block >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
  `inst_wf u` by
    (gvs[fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  `u.inst_outputs = []` by gvs[inst_wf_def] >>
  strip_tac >> `li = u` by
    (irule mmWfProofsTheory.fn_inst_ids_distinct_inj >>
     conj_tac >- simp[] >>
     qexists_tac `fn0` >> gvs[wf_function_def]) >> gvs[]
QED

Theorem mm_local_prefix_write_group_owner[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM w bb.bb_instructions /\
  w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM a (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM b (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM w.inst_id a.cg_inst_ids /\ MEM w.inst_id b.cg_inst_ids ==> a = b
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule mm_local_prefix_id_distinct >>
     qexistsl [`fn0`,`index`,`k`,`sk`,`supply`] >> simp[] >>
     conj_tac
     >- metis_tac[wf_function_def, mmWfProofsTheory.fn_inst_ids_distinct_block, EL_MEM] >>
     gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
       irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     gen_tac >> strip_tac >> qpat_x_assum `!id. _ ==> id < _` irule >>
     qexists_tac `MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions` >>
     (conj_tac >- (qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM])) >>
     simp[MEM_MAP] >> qexists_tac `i` >> simp[]) >>
  irule mm_local_scan_group_owner >>
  qexistsl [`bb`,`dfg_build_function fn0`,`w.inst_id`,`mode`,
            `\id. id = w.inst_id`] >> simp[] >>
  metis_tac[mm_local_prefix_write_not_def]
QED

Theorem mm_local_cut_pending_ancestor[local]:
  bb.bb_instructions = pre ++ post /\
  ss = FOLDL (scan_inst dfg mode) empty_scan_state pre /\
  (!a b. MEM a (scan_block dfg mode bb).ss_flushed /\
         MEM b (scan_block dfg mode bb).ss_flushed /\
         MEM id a.cg_inst_ids /\ MEM id b.cg_inst_ids ==> a = b) /\
  (!a j. MEM a ss.ss_flushed /\ MEM j a.cg_inst_ids ==>
         MEM j (MAP (\i. i.inst_id) pre)) /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) /\ MEM id h.cg_inst_ids /\
  MEM g (scan_block dfg mode bb).ss_flushed /\ MEM id g.cg_inst_ids /\
  rep_of_group bb.bb_instructions g = SOME (r,g) /\
  ~MEM r (MAP (\i. i.inst_id) pre) ==>
  MEM h ss.ss_copies /\ mm_local_copy_ancestor h g
Proof
  strip_tac >>
  `?a. MEM a (scan_block dfg mode bb).ss_flushed /\
       mm_local_copy_ancestor h a` by
    (irule mm_local_prefix_final_fragment >> metis_tac[]) >>
  `MEM id a.cg_inst_ids` by gvs[mm_local_copy_ancestor_def] >>
  `a = g` by metis_tac[] >>
  `?tail. (FOLDL (scan_inst dfg mode) ss post).ss_flushed = ss.ss_flushed ++ tail`
    by metis_tac[mm_local_fold_flushed_extension] >>
  `MEM h ss.ss_flushed ==> MEM h (scan_block dfg mode bb).ss_flushed` by
    (simp[scan_block_def, FOLDL_APPEND, hard_barrier_def] >>
     metis_tac[MEM_APPEND]) >>
  drule mm_local_rep_member >> strip_tac >>
  gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_prefix_write_pending_ancestor[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM w bb.bb_instructions /\
  w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  bb.bb_instructions = pre ++ post /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state pre /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) /\ MEM w.inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM w.inst_id g.cg_inst_ids /\ rep_of_group bb.bb_instructions g = SOME (r,g) /\
  ~MEM r (MAP (\i. i.inst_id) pre) ==>
  MEM h ss.ss_copies /\ mm_local_copy_ancestor h g
Proof
  strip_tac >> irule mm_local_cut_pending_ancestor >>
  conj_tac >- simp[] >>
  qexistsl [`bb`,`dfg_build_function fn0`,`w.inst_id`,`mode`,`post`,`pre`,`r`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule mm_local_prefix_write_group_owner >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >> irule mm_local_prefix_fragment_ids_before_cut >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM_APPEND]
QED

Theorem mm_local_memzero_merge_effect[local]:
  d1 <= d2 /\ d2 <= d1+n1 /\
  cg = copy_merge (copy_memzero d1 n1 ids1) (copy_memzero d2 n2 ids2) ==>
  write_memory_with_expansion d2 (REPLICATE n2 0w)
    (write_memory_with_expansion d1 (REPLICATE n1 0w) s) =
  write_memory_with_expansion cg.cg_dst (REPLICATE cg.cg_length 0w) s
Proof
  simp[copy_merge_def, copy_memzero_def] >>
  metis_tac[mm_local_zero_write_merge]
QED

Theorem mm_local_zero_write_empty[local]:
  write_memory_with_expansion dst [] s =
    s with vs_memory := expand_mem s.vs_memory dst
Proof
  simp[write_as_replace, replace_bytes_def, TAKE_DROP]
QED

Definition mm_local_write_compatible_def:
  mm_local_write_compatible d bs a cs <=>
    !x. d <= x /\ x < d + LENGTH bs /\ a <= x /\ x < a + LENGTH cs ==>
      EL (x-d) bs = EL (x-a) cs
End

Theorem mm_local_write_compatible_sym[local]:
  mm_local_write_compatible d bs a cs <=> mm_local_write_compatible a cs d bs
Proof
  metis_tac[mm_local_write_compatible_def]
QED

Theorem mm_local_write_compatible_disjoint[local]:
  d + LENGTH bs <= a \/ a + LENGTH cs <= d ==>
  mm_local_write_compatible d bs a cs
Proof
  rw[mm_local_write_compatible_def] >> gvs[]
QED

Theorem mm_local_write_compatible_empty[local]:
  mm_local_write_compatible d [] a cs /\ mm_local_write_compatible a cs d []
Proof
  simp[mm_local_write_compatible_def]
QED

Theorem mm_local_replace_compatible_commute[local]:
  mm_local_write_compatible d1 bs1 d2 bs2 /\
  MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) <= LENGTH mem ==>
  replace_bytes d2 bs2 (replace_bytes d1 bs1 mem) =
  replace_bytes d1 bs1 (replace_bytes d2 bs2 mem)
Proof
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE,
    LENGTH_DROP] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, LENGTH_APPEND,
    LENGTH_TAKE, LENGTH_DROP, arithmeticTheory.MAX_DEF] >> gvs[] >>
  fs[mm_local_write_compatible_def] >> metis_tac[]
QED

Theorem mm_local_replace_disjoint_commute[local]:
  (d1 + LENGTH bs1 <= d2 \/ d2 + LENGTH bs2 <= d1) /\
  MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) <= LENGTH mem ==>
  replace_bytes d2 bs2 (replace_bytes d1 bs1 mem) =
  replace_bytes d1 bs1 (replace_bytes d2 bs2 mem)
Proof
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE,
    LENGTH_DROP] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, LENGTH_APPEND,
    LENGTH_TAKE, LENGTH_DROP, arithmeticTheory.MAX_DEF] >> gvs[]
QED

Theorem mm_local_write_disjoint_commute[local]:
  (d1 + LENGTH bs1 <= d2 \/ d2 + LENGTH bs2 <= d1) ==>
  write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 s) =
  write_memory_with_expansion d1 bs1 (write_memory_with_expansion d2 bs2 s)
Proof
  strip_tac >> simp[write_as_replace] >>
  `d1 + LENGTH bs1 <= LENGTH (expand_mem s.vs_memory (d1 + LENGTH bs1))` by
    simp[expand_mem_ge] >>
  `d2 + LENGTH bs2 <= LENGTH (expand_mem s.vs_memory (d2 + LENGTH bs2))` by
    simp[expand_mem_ge] >>
  simp[expand_replace, mm_local_expand_mem_max,
       venomStateTheory.venom_state_component_equality] >>
  simp[arithmeticTheory.MAX_COMM] >>
  irule mm_local_replace_disjoint_commute >> simp[] >>
  simp[arithmeticTheory.MAX_DEF]
QED

Theorem mm_local_write_compatible_commute[local]:
  mm_local_write_compatible d1 bs1 d2 bs2 ==>
  write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 s) =
  write_memory_with_expansion d1 bs1 (write_memory_with_expansion d2 bs2 s)
Proof
  strip_tac >> simp[write_as_replace] >>
  `d1 + LENGTH bs1 <= LENGTH (expand_mem s.vs_memory (d1 + LENGTH bs1))` by
    simp[expand_mem_ge] >>
  `d2 + LENGTH bs2 <= LENGTH (expand_mem s.vs_memory (d2 + LENGTH bs2))` by
    simp[expand_mem_ge] >>
  simp[expand_replace, mm_local_expand_mem_max,
       venomStateTheory.venom_state_component_equality] >>
  simp[arithmeticTheory.MAX_COMM] >>
  irule mm_local_replace_compatible_commute >> simp[] >>
  simp[arithmeticTheory.MAX_DEF]
QED

Theorem mm_local_write_log_compatible_commute[local]:
  !ws s. EVERY (\(d,bs). mm_local_write_compatible d bs a bytes) ws ==>
  write_memory_with_expansion a bytes
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (write_memory_with_expansion a bytes s) ws
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then (fn th => rewrite_tac[th])) >>
  AP_THM_TAC >> AP_TERM_TAC >>
  irule mm_local_write_compatible_commute >> simp[]
QED

Theorem mm_local_write_log_commute[local]:
  !ws s. EVERY (\(d,bs). d + LENGTH bs <= a \/ a + LENGTH bytes <= d) ws ==>
  write_memory_with_expansion a bytes
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (write_memory_with_expansion a bytes s) ws
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then (fn th => rewrite_tac[th])) >>
  simp[mm_local_write_disjoint_commute]
QED

Theorem mm_local_zero_log_merge[local]:
  d1 <= d2 /\ d2 <= d1+n1 /\
  EVERY (\(d,bs). d + LENGTH bs <= d2 \/ d2+n2 <= d) ws ==>
  write_memory_with_expansion d2 (REPLICATE n2 0w)
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 (REPLICATE n1 0w) s) ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (write_memory_with_expansion d1
      (REPLICATE (MAX (d1+n1) (d2+n2)-d1) 0w) s) ws
Proof
  strip_tac >> simp[mm_local_write_log_commute, mm_local_zero_write_merge]
QED

Theorem mm_local_write_pair_length[local]:
  LENGTH (write_memory_with_expansion d2 bs2
    (write_memory_with_expansion d1 bs1 s)).vs_memory =
  MAX (LENGTH s.vs_memory) (MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2))
Proof
  simp[write_as_replace, replace_bytes_len, expand_mem_ge] >>
  simp[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem mm_local_load_pending_disjoint[local]:
  inst.inst_operands = [Lit w] /\ inst.inst_outputs = [out] /\
  MEM cg (scan_load Mem2Mem ss inst).ss_copies /\ 0 < cg.cg_length ==>
  w2n w + 32 <= cg.cg_dst \/ cg.cg_dst + cg.cg_length <= w2n w
Proof
  strip_tac >>
  gvs[scan_load_def, operand_lit_val_def, mode_allows_overlap_def] >>
  Cases_on `copies_that_overwrite ss.ss_copies (mk_interval (w2n w) 32) = []` >>
  gvs[flush_copies_def, MEM_FILTER, copies_that_overwrite_def] >>
  `~copy_overwrites cg (mk_interval (w2n w) 32)` by
    (spose_not_then assume_tac >>
     `MEM cg (FILTER (\c. copy_overwrites c (mk_interval (w2n w) 32)) ss.ss_copies)` by
       simp[MEM_FILTER] >> gvs[]) >>
  gvs[copy_overwrites_def, copy_dst_interval_def,
      mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
      mmIntervalTheory.interval_end_def,
      arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem mm_local_flush_hazards_survivor[local]:
  MEM h (flush_hazards Mem2Mem ss c).ss_copies ==>
  ~copy_overwrites c (copy_src_interval h)
Proof
  simp[flush_hazards_def, mode_allows_overlap_def] >>
  rpt IF_CASES_TAC >>
  gvs[flush_copies_def, war_hazards_def, MEM_FILTER] >>
  rpt strip_tac >> gvs[FILTER_EQ_NIL, EVERY_MEM, MEM_FILTER]
QED

Theorem mm_local_invalidate_binding[local]:
  FLOOKUP (invalidate_loads ss iv).ss_loads v = SOME src ==>
  FLOOKUP ss.ss_loads v = SOME src /\ ~load_conflicts iv src
Proof
  simp[invalidate_loads_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  Cases_on `FLOOKUP ss.ss_loads v` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem mm_local_invalidate_disjoint[local]:
  0 < n /\
  FLOOKUP (invalidate_loads ss (mk_interval dst n)).ss_loads v = SOME src ==>
  src+32 <= dst \/ dst+n <= src
Proof
  strip_tac >> drule mm_local_invalidate_binding >>
  simp[load_conflicts_def, mmIntervalTheory.interval_overlaps_def,
       mmIntervalTheory.mk_interval_def, mmIntervalTheory.interval_end_def,
       arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem mm_local_flush_hazards_read[local]:
  MEM h (flush_hazards Mem2Mem ss c).ss_copies /\
  LENGTH bytes = c.cg_length ==>
  TAKE h.cg_length
    (DROP h.cg_src (write_memory_with_expansion c.cg_dst bytes s).vs_memory ++
     REPLICATE h.cg_length (0w:word8)) =
  TAKE h.cg_length (DROP h.cg_src s.vs_memory ++ REPLICATE h.cg_length 0w)
Proof
  strip_tac >> drule mm_local_flush_hazards_survivor >> strip_tac >>
  irule frameViewMemoryTheory.padded_memory_read_cong >> rpt strip_tac >>
  irule frameViewMemoryTheory.write_memory_byte_outside >>
  gvs[copy_overwrites_def, copy_dst_interval_def, copy_src_interval_def,
      mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
      mmIntervalTheory.interval_end_def,
      arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem mm_local_invalidate_read[local]:
  FLOOKUP (invalidate_loads ss (mk_interval dst (LENGTH bytes))).ss_loads v = SOME src ==>
  TAKE 32 (DROP src (write_memory_with_expansion dst bytes s).vs_memory ++
           REPLICATE 32 (0w:word8)) =
  TAKE 32 (DROP src s.vs_memory ++ REPLICATE 32 0w)
Proof
  strip_tac >> drule mm_local_invalidate_binding >> strip_tac >>
  irule frameViewMemoryTheory.padded_memory_read_cong >> rpt strip_tac >>
  irule frameViewMemoryTheory.write_memory_byte_outside >>
  gvs[load_conflicts_def,
      mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
      mmIntervalTheory.interval_end_def,
      arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem mm_local_live_cut_fresh[local]:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  j < LENGTH bb.bb_instructions /\
  FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE j bb.bb_instructions)).ss_loads v = SOME src ==>
  ~MEM v (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >> drule mm_local_scan_lookup_origin >> strip_tac >>
  `MEM q bb.bb_instructions` by metis_tac[MEM_TAKE] >>
  `MEM q (EL index fn0.fn_blocks).bb_instructions` by
    (irule mm_local_pending_load_origin >> metis_tac[]) >>
  `MEM q (fn_insts fn0)` by
    (irule mmWfProofsTheory.fn_insts_mem_block >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
  `?li. dfg_get_def (dfg_build_function fn0) v = SOME li` by
    (irule dfgCorrectnessProofTheory.dfg_build_function_defs_complete_proof >>
     qexists_tac `q` >> simp[]) >>
  `MEM v q.inst_outputs` by simp[] >>
  `q = li` by (irule mm_local_prefix_producer_identify >> metis_tac[]) >>
  strip_tac >>
  `EL j bb.bb_instructions = li` by
    (irule mm_local_prefix_producer_identify >> metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule mm_local_prefix_id_distinct >>
     qexistsl [`fn0`,`index`,`k`,`sk`,`supply`] >> simp[] >>
     conj_tac
     >- metis_tac[wf_function_def, mmWfProofsTheory.fn_inst_ids_distinct_block, EL_MEM] >>
     gvs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
       irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     gen_tac >> strip_tac >> qpat_x_assum `!id. _ ==> id < _` irule >>
     qexists_tac `MAP (\i. i.inst_id) (EL index fn0.fn_blocks).bb_instructions` >>
     (conj_tac >- (qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM])) >>
     simp[MEM_MAP] >> qexists_tac `i` >> simp[]) >>
  qpat_x_assum `MEM q (TAKE j _)` mp_tac >>
  simp[MEM_EL, EL_TAKE] >> rpt strip_tac >>
  `n < LENGTH bb.bb_instructions` by decide_tac >>
  `n = j` by
    (irule mmCorrectnessProofsTheory.all_distinct_inst_id_idx >>
     qexists_tac `bb.bb_instructions` >> simp[EL_TAKE]) >>
  decide_tac
QED

Theorem mm_local_live_load_empty[local]:
  !v src. FLOOKUP empty_scan_state.ss_loads v = SOME src ==>
    lookup_var v s = SOME (mload src s)
Proof
  simp[empty_scan_state_def]
QED

Theorem mm_local_live_load_barrier[local]:
  !v src. FLOOKUP (hard_barrier ss).ss_loads v = SOME src ==>
    lookup_var v s = SOME (mload src s)
Proof
  simp[hard_barrier_def]
QED

Theorem mm_local_live_load_create[local]:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [Lit a] /\
  inst.inst_outputs = [out] /\ step_inst_base inst s = OK t /\
  (!v src. FLOOKUP ss.ss_loads v = SOME src ==>
     lookup_var v s = SOME (mload src s)) /\
  (!v src. FLOOKUP ss.ss_loads v = SOME src /\ v <> out ==>
     lookup_var v t = lookup_var v s) ==>
  !v src. FLOOKUP (scan_load Mem2Mem ss inst).ss_loads v = SOME src ==>
    lookup_var v t = SOME (mload src t)
Proof
  strip_tac >>
  `t = update_var out (mload (w2n a) s) s` by
    gvs[venomExecSemanticsTheory.step_inst_base_def,
        venomExecSemanticsTheory.exec_read1_def,
        venomStateTheory.eval_operand_def] >>
  gvs[scan_load_def, operand_lit_val_def, mode_allows_overlap_def] >>
  IF_CASES_TAC >>
  simp[flush_copies_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `out = v` >>
  gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
      venomStateTheory.mload_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem mm_local_live_load_write[local]:
  (!v src. FLOOKUP ss.ss_loads v = SOME src ==>
     lookup_var v s = SOME (mload src s)) /\
  t.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  (!v src.
     FLOOKUP (invalidate_loads ss (mk_interval dst (LENGTH bytes))).ss_loads v = SOME src ==>
     lookup_var v t = lookup_var v s) ==>
  !v src.
    FLOOKUP (invalidate_loads ss (mk_interval dst (LENGTH bytes))).ss_loads v = SOME src ==>
    lookup_var v t = SOME (mload src t)
Proof
  rpt strip_tac >>
  drule mm_local_invalidate_binding >> strip_tac >>
  drule mm_local_invalidate_read >> strip_tac >>
  `mload src t = mload src s` by simp[venomStateTheory.mload_def] >>
  metis_tac[]
QED

Theorem mm_local_live_load_step[local]:
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode /\
  (!v src. FLOOKUP ss.ss_loads v = SOME src ==>
     lookup_var v s = SOME (mload src s)) /\
  (!v src. FLOOKUP ss.ss_loads v = SOME src ==> ~MEM v inst.inst_outputs) ==>
  !v src. FLOOKUP (scan_inst dfg Mem2Mem ss inst).ss_loads v = SOME src ==>
    lookup_var v t = SOME (mload src t)
Proof
  strip_tac >>
  `!v src. FLOOKUP ss.ss_loads v = SOME src ==>
      lookup_var v t = lookup_var v s` by
    (rpt strip_tac >> irule basePtrProofsTheory.step_inst_preserves_lookup >>
     metis_tac[]) >>
  Cases_on `inst.inst_opcode = MLOAD`
  >- (gvs[scan_inst_def, mode_load_opcode_def] >>
      `step_inst_base inst s = OK t` by
        (qpat_x_assum `step_inst fuel ctx inst s = OK t` mp_tac >>
         simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
      gvs[venomExecSemanticsTheory.step_inst_base_def,
          venomExecSemanticsTheory.exec_read1_def, AllCaseEqs()] >>
      rename1 `inst.inst_operands = [op]` >>
      Cases_on `op` >>
      gvs[scan_load_def, operand_lit_val_def, hard_barrier_def,
          venomStateTheory.eval_operand_def, mode_allows_overlap_def] >>
      IF_CASES_TAC >>
      simp[flush_copies_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `out = v` >>
      gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
          venomStateTheory.mload_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  Cases_on `inst.inst_opcode = MSTORE`
  >- suspend "store"
  >> Cases_on `inst.inst_opcode = MCOPY`
  >- suspend "copy"
  >> Cases_on `is_volatile_memory inst`
  >- simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def, hard_barrier_def] >>
  `t.vs_memory = s.vs_memory` by
    (`inst.inst_opcode <> INVOKE` by
       (strip_tac >> gvs[is_volatile_memory_def, venomEffectsTheory.read_effects_def,
                        venomEffectsTheory.all_effects_def]) >>
     Cases_on `is_alloca_op inst.inst_opcode`
     >- (irule venomMemPropsTheory.step_inst_alloca_preserves_memory >> metis_tac[]) >>
     irule venomInstProofsTheory.write_effects_sound_memory >>
     gvs[is_volatile_memory_def] >> metis_tac[]) >>
  simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  rpt strip_tac >> `mload src t = mload src s` by simp[venomStateTheory.mload_def] >>
  metis_tac[]
QED

Resume mm_local_live_load_step[store]:
  gvs[scan_inst_def, mode_load_opcode_def] >>
      simp[scan_store_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >>
           gvs[hard_barrier_def, operand_var_name_def, operand_lit_val_def,
               mode_allows_overlap_def]) >>
      rename1 `inst.inst_operands = [dst_op; val_op]` >>
      Cases_on `dst_op` >> Cases_on `val_op` >>
      gvs[operand_lit_val_def, operand_var_name_def] >>
      qmatch_goalsub_abbrev_tac `flush_hazards Mem2Mem ss0 cg` >>
      `!u g. (flush_hazards Mem2Mem u g).ss_loads = u.ss_loads` by
        (rpt gen_tac >> simp[flush_hazards_def, mode_allows_overlap_def] >>
         rpt IF_CASES_TAC >> simp[flush_copies_def]) >>
      simp[] >> simp[Abbr `ss0`] >>
      `step_inst_base inst s = OK t` by
        (qpat_x_assum `step_inst fuel ctx inst s = OK t` mp_tac >>
         simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
      gvs[venomExecSemanticsTheory.step_inst_base_def,
          venomExecSemanticsTheory.exec_write2_def,
          venomStateTheory.eval_operand_def, AllCaseEqs()] >>
      `LENGTH (word_to_bytes val T) = 32` by
        simp[byteTheory.LENGTH_word_to_bytes] >>
      qpat_assum `LENGTH (word_to_bytes val T) = 32`
        (fn th => once_rewrite_tac[GSYM th]) >>
      match_mp_tac mm_local_live_load_write >>
      simp[venomMemPropsTheory.mstore_eq_write_mem] >> rpt strip_tac >>
      drule mm_local_invalidate_binding >> metis_tac[]
QED

Resume mm_local_live_load_step[copy]:
  gvs[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
      simp[scan_bulk_copy_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >>
           gvs[hard_barrier_def, operand_lit_val_def, mode_allows_overlap_def]) >>
      rename1 `inst.inst_operands = [dst_op; src_op; size_op]` >>
      Cases_on `dst_op` >> Cases_on `src_op` >> Cases_on `size_op` >>
      gvs[operand_lit_val_def] >>
      `!u g. (flush_hazards Mem2Mem u g).ss_loads = u.ss_loads` by
        (rpt gen_tac >> simp[flush_hazards_def, mode_allows_overlap_def] >>
         rpt IF_CASES_TAC >> simp[flush_copies_def]) >>
      simp[] >>
      `step_inst_base inst s = OK t` by
        (qpat_x_assum `step_inst fuel ctx inst s = OK t` mp_tac >>
         simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
      gvs[venomExecSemanticsTheory.step_inst_base_def,
          venomStateTheory.eval_operand_def, AllCaseEqs()] >>
      `LENGTH (TAKE (w2n c'') (DROP (w2n c') s.vs_memory ++
          REPLICATE (w2n c'') 0w)) = w2n c''` by simp[] >>
      pop_assum (fn th => once_rewrite_tac[GSYM th]) >>
      match_mp_tac mm_local_live_load_write >>
      simp[venomExecSemanticsTheory.mcopy_def] >> rpt strip_tac >>
      drule mm_local_invalidate_binding >> metis_tac[]
QED

Finalise mm_local_live_load_step

Theorem mm_local_scan_phi_prefix[local]:
  !xs ss. FOLDL (scan_inst dfg Mem2Mem) ss
    (TAKE (phi_prefix_length xs) xs) = ss
Proof
  Induct_on `xs` >> simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rpt gen_tac >> IF_CASES_TAC >>
  simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def,
       is_volatile_memory_def, venomEffectsTheory.read_effects_def,
       venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def,
       venomEffectsTheory.empty_effects_def]
QED

Theorem mm_local_live_load_cut[local]:
  !n h states fn0 supply index k bb sk fuel ctx.
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  h+n <= LENGTH bb.bb_instructions /\ n < LENGTH states /\
  (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state
    (TAKE h bb.bb_instructions)).ss_loads = FEMPTY /\
  (!r. r < n ==>
    ~is_terminator (EL (h+r) bb.bb_instructions).inst_opcode /\
    ?t. step_inst fuel ctx (EL (h+r) bb.bb_instructions) (EL r states) = OK t /\
        EL (SUC r) states = t with vs_inst_idx := SUC (EL r states).vs_inst_idx) ==>
  !v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE (h+n) bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (EL n states) = SOME (mload src (EL n states))
Proof
  Induct_on `n`
  >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE (h+n) bb.bb_instructions)).ss_loads v = SOME src ==>
    lookup_var v (EL n states) = SOME (mload src (EL n states))` by
    (first_x_assum match_mp_tac >>
     qexistsl [`supply`,`index`,`k`,`sk`,`fuel`,`ctx`] >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `h+n < LENGTH bb.bb_instructions` by decide_tac >>
  `~is_terminator (EL (h+n) bb.bb_instructions).inst_opcode /\
    ?t. step_inst fuel ctx (EL (h+n) bb.bb_instructions) (EL n states) = OK t /\
        EL (SUC n) states = t with vs_inst_idx := SUC (EL n states).vs_inst_idx` by
    (first_x_assum irule >> simp[]) >>
  gvs[arithmeticTheory.ADD_CLAUSES, rich_listTheory.TAKE_SUC_BY_TAKE,
      rich_listTheory.FOLDL_SNOC] >>
  `!u a. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE (h+n) bb.bb_instructions)).ss_loads u = SOME a ==>
    ~MEM u (EL (h+n) bb.bb_instructions).inst_outputs` by
    (metis_tac[mm_local_live_cut_fresh]) >>
  `~is_terminator (EL (h+n) bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `!r. r < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  drule_all mm_local_live_load_step >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.mload_def,
       venomStateTheory.read_memory_def]
QED

Theorem mm_local_live_load_post_phis[local]:
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
      (TAKE j bb.bb_instructions) ==>
  !v src. FLOOKUP ss.ss_loads v = SOME src ==>
    lookup_var v (EL (j-h) states) = SOME (mload src (EL (j-h) states))
Proof
  strip_tac >>
  `j = h + (j-h)` by decide_tac >>
  qpat_x_assum `ss = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `j = h + (j-h)` (fn th => once_rewrite_tac[th]) >>
  simp[NoAsms] >>
  match_mp_tac mm_local_live_load_cut >>
  qexistsl [`supply`,`index`,`k`,`sk`,`fuel`,`ctx`] >>
  simp[mm_local_scan_phi_prefix, empty_scan_state_def] >>
  metis_tac[]
QED

(* Capture only the memory projection: bookkeeping is not part of the event. *)
Theorem mm_local_capture_store[local]:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [Lit dst; Var v] /\
  lookup_var v s = SOME (mload src s) /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_memory =
    (write_memory_with_expansion (w2n dst) (read_memory src 32 s) s).vs_memory
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK t` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  gvs[venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_write2_def,
      venomStateTheory.eval_operand_def] >>
  simp[mload_mstore_eq_mcopy_state, venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.read_memory_def]
QED

Theorem mm_local_capture_copy[local]:
  inst.inst_opcode = MCOPY /\
  inst.inst_operands = [Lit dst; Lit src; Lit len] /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_memory =
    (write_memory_with_expansion (w2n dst)
      (read_memory (w2n src) (w2n len) s) s).vs_memory
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK t` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  gvs[venomExecSemanticsTheory.step_inst_base_def,
      venomStateTheory.eval_operand_def] >>
  simp[venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]
QED

Theorem mm_local_capture_store_post_phis[local]:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  h = phi_prefix_length bb.bb_instructions /\ h <= j /\ j < LENGTH bb.bb_instructions /\
  LENGTH states = SUC (j-h) /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  EL 0 states = s_phi with vs_inst_idx := h /\
  (!r. r < j-h ==>
    ~is_terminator (EL (h+r) bb.bb_instructions).inst_opcode /\
    ?t. step_inst fuel ctx (EL (h+r) bb.bb_instructions) (EL r states) = OK t /\
        EL (SUC r) states = t with vs_inst_idx := SUC (EL r states).vs_inst_idx) /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state
      (TAKE j bb.bb_instructions) /\
  inst = EL j bb.bb_instructions /\ inst.inst_opcode = MSTORE /\
  inst.inst_operands = [Lit dst; Var v] /\ FLOOKUP ss.ss_loads v = SOME src /\
  step_inst fuel ctx inst (EL (j-h) states) = OK t ==>
  t.vs_memory = (write_memory_with_expansion (w2n dst)
    (read_memory src 32 (EL (j-h) states)) (EL (j-h) states)).vs_memory
Proof
  strip_tac >>
  `!u a. FLOOKUP ss.ss_loads u = SOME a ==>
     lookup_var u (EL (j-h) states) = SOME (mload a (EL (j-h) states))` by
    (match_mp_tac mm_local_live_load_post_phis >> simp[]) >>
  irule mm_local_capture_store >> metis_tac[]
QED

Theorem mm_local_supply_append[local]:
  !xs s ys t zs u ws.
  mm_flat_map_supply f s xs = (ys,t) /\
  mm_flat_map_supply f t zs = (ws,u) ==>
  mm_flat_map_supply f s (xs ++ zs) = (ys ++ ws,u)
Proof
  Induct_on `xs` >> simp[mm_flat_map_supply_def] >>
  rpt gen_tac >>
  Cases_on `f s h` >> Cases_on `mm_flat_map_supply f r xs` >>
  simp[mm_flat_map_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> first_x_assum drule >> gvs[]
QED

Theorem mm_local_supply_cut[local]:
  j < LENGTH xs /\ mm_flat_map_supply f s xs = (ys,t) ==>
  ?pre chunk post u v.
    mm_flat_map_supply f s (TAKE j xs) = (pre,u) /\
    f u (EL j xs) = (chunk,v) /\
    mm_flat_map_supply f v (DROP (SUC j) xs) = (post,t) /\
    ys = pre ++ chunk ++ post
Proof
  strip_tac >>
  Cases_on `mm_flat_map_supply f s (TAKE j xs)` >>
  rename1 `mm_flat_map_supply f s (TAKE j xs) = (pre,u)` >>
  Cases_on `f u (EL j xs)` >> rename1 `f u (EL j xs) = (chunk,v)` >>
  Cases_on `mm_flat_map_supply f v (DROP (SUC j) xs)` >>
  rename1 `mm_flat_map_supply f v (DROP (SUC j) xs) = (post,z)` >>
  `xs = TAKE j xs ++ EL j xs :: DROP (SUC j) xs` by
    simp[rich_listTheory.TAKE_DROP_SUC] >>
  `mm_flat_map_supply f u (EL j xs :: DROP (SUC j) xs) = (chunk ++ post,z)` by
    simp[mm_flat_map_supply_def] >>
  drule_all mm_local_supply_append >>
  strip_tac >>
  gvs[GSYM rich_listTheory.DROP_CONS_EL, listTheory.TAKE_DROP] >>
  metis_tac[]
QED

Theorem mm_local_event_rep_position[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\ j < LENGTH xs /\
  MEM (EL j xs).inst_id cg.cg_inst_ids ==>
  ?r. j <= r /\ r < LENGTH xs /\
    rep_of_group xs cg = SOME ((EL r xs).inst_id,cg)
Proof
  strip_tac >>
  `MEM (EL j xs).inst_id (sort_ids_by_block xs cg.cg_inst_ids)` by
    (simp[sort_ids_by_block_def, MEM_FILTER, MEM_MAP] >>
     qexists `EL j xs` >> simp[EL_MEM]) >>
  Cases_on `REVERSE (sort_ids_by_block xs cg.cg_inst_ids)`
  >- gvs[MEM_REVERSE] >>
  rename1 `REVERSE (sort_ids_by_block xs cg.cg_inst_ids) = id::ids` >>
  `rep_of_group xs cg = SOME (id,cg)` by simp[rep_of_group_def] >>
  drule mm_local_rep_member >> strip_tac >>
  qpat_x_assum `MEM id (MAP _ xs)` mp_tac >> simp[MEM_EL] >> strip_tac >>
  qexists `n` >> gvs[EL_MAP] >>
  irule mm_local_rep_position_max >> metis_tac[]
QED

Theorem mm_local_mode_emission_cut[local]:
  transform_block_mode_supply dfg mode supply bb = (cc,sk) /\
  j < LENGTH bb.bb_instructions ==>
  ?pre chunk post u v.
    mm_flat_map_supply
      (apply_groups_inst_supply mode
        (nop_ids_of_groups dfg mode bb.bb_instructions (scan_block dfg mode bb).ss_flushed)
        (rep_map_of_groups bb.bb_instructions (scan_block dfg mode bb).ss_flushed))
      supply (TAKE j bb.bb_instructions) = (pre,u) /\
    apply_groups_inst_supply mode
      (nop_ids_of_groups dfg mode bb.bb_instructions (scan_block dfg mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions (scan_block dfg mode bb).ss_flushed)
      u (EL j bb.bb_instructions) = (chunk,v) /\
    cc.bb_instructions = pre ++ chunk ++ post
Proof
  simp[transform_block_mode_supply_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule_all mm_local_supply_cut >> metis_tac[]
QED

Theorem mm_local_rep_not_nop_own[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  rep_of_group xs cg = SOME (id,cg) ==>
  ~MEM id (nop_ids_of_group dfg mode xs cg)
Proof
  strip_tac >>
  `ALL_DISTINCT (REVERSE (sort_ids_by_block xs cg.cg_inst_ids))` by
    simp[sort_ids_by_block_def, FILTER_ALL_DISTINCT] >>
  gvs[rep_of_group_def, nop_ids_of_group_def, AllCaseEqs(),
      MEM_FILTER, MEM_REVERSE] >>
  disj2_tac >>
  qpat_x_assum `ALL_DISTINCT (sort_ids_by_block _ _)` mp_tac >>
  once_rewrite_tac[GSYM ALL_DISTINCT_REVERSE] >>
  pure_asm_rewrite_tac[] >> simp[]
QED

Theorem mm_local_rep_not_nop[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  rep_of_group xs cg = SOME (id,cg) /\
  (!g. MEM g groups /\ MEM id g.cg_inst_ids ==> g = cg) ==>
  ~MEM id (nop_ids_of_groups dfg mode xs groups)
Proof
  strip_tac >> strip_tac >>
  `~MEM id (nop_ids_of_group dfg mode xs cg)` by
    metis_tac[mm_local_rep_not_nop_own] >>
  gvs[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >>
  rename1 `MEM g groups` >>
  `MEM id g.cg_inst_ids` by
    (qpat_x_assum `MEM id (nop_ids_of_group _ _ _ _)` mp_tac >>
     simp[nop_ids_of_group_def] >>
     Cases_on `REVERSE (sort_ids_by_block xs g.cg_inst_ids)` >>
     simp[MEM_FILTER, MEM_REVERSE] >> strip_tac >>
     `MEM id (REVERSE (sort_ids_by_block xs g.cg_inst_ids))` by metis_tac[MEM] >>
     gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER]) >>
  metis_tac[]
QED

Theorem mm_local_scan_selected_rep[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM cg (scan_block dfg mode bb).ss_flushed /\
  rep_of_group bb.bb_instructions cg = SOME (id,cg) /\
  (!v li. dfg_get_def dfg v = SOME li ==> li.inst_id <> id) ==>
  ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block dfg mode bb).ss_flushed) id = SOME cg /\
  ~MEM id (nop_ids_of_groups dfg mode bb.bb_instructions
    (scan_block dfg mode bb).ss_flushed)
Proof
  strip_tac >>
  conj_tac
  >- (irule mm_local_scan_rep_lookup >>
      conj_tac >- (qexists `\x. x = id` >> simp[] >> metis_tac[]) >>
      simp[]) >>
  irule mm_local_rep_not_nop >> simp[] >>
  qexists `cg` >> simp[] >> rpt strip_tac >>
  irule mm_local_scan_group_owner >>
  qexistsl [`bb`,`dfg`,`id`,`mode`,`\x. x = id`] >>
  drule mm_local_rep_member >> simp[] >> metis_tac[]
QED

Theorem mm_local_prefix_selected_rep[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM i bb.bb_instructions /\
  MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  rep_of_group bb.bb_instructions cg = SOME (i.inst_id,cg) ==>
  ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed) i.inst_id = SOME cg /\
  ~MEM i.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
Proof
  strip_tac >>
  `?g. ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed) i.inst_id = SOME g` by
    (Cases_on `ALOOKUP (rep_map_of_groups bb.bb_instructions
       (scan_block (dfg_build_function fn0) mode bb).ss_flushed) i.inst_id`
     >- (gvs[alistTheory.ALOOKUP_FAILS] >>
         `MEM (i.inst_id,cg) (rep_map_of_groups bb.bb_instructions
           (scan_block (dfg_build_function fn0) mode bb).ss_flushed)` by
           (simp[NoAsms, rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
            qexists `SOME (i.inst_id,cg)` >> simp[] >>
            qexists `cg` >> simp[]) >>
         metis_tac[]) >> simp[]) >>
  `i.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (irule mm_local_prefix_rep_write >> metis_tac[]) >>
  irule mm_local_scan_selected_rep >> simp[] >>
  metis_tac[mm_local_prefix_write_not_def]
QED

Theorem mm_local_selected_chunk[local]:
  ~MEM i.inst_id ns /\ ALOOKUP rm i.inst_id = SOME cg /\
  apply_groups_inst_supply mode ns rm u i = (chunk,v) ==>
  ((cg.cg_length <> 32 \/ mode = DloadMerge) /\
    chunk = [mk_bulk_copy_inst mode i cg] /\ v = u) \/
  (cg.cg_length = 32 /\ mode <> DloadMerge /\ i.inst_opcode = MSTORE /\
    chunk = [i] /\ v = u) \/
  (cg.cg_length = 32 /\ mode <> DloadMerge /\ i.inst_opcode <> MSTORE /\
    ?load_id s1 load_var. fresh_inst_id u = (load_id,s1) /\
      fresh_ir_var s1 = (load_var,v) /\
      chunk = [mk_load_inst mode (i with inst_id := load_id) cg.cg_src load_var;
               mk_mstore_from_load i cg.cg_dst load_var])
Proof
  simp[apply_groups_inst_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem mm_local_event_emission[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  j < LENGTH bb.bb_instructions /\
  MEM (EL j bb.bb_instructions).inst_id cg.cg_inst_ids /\
  MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  transform_block_mode_supply (dfg_build_function fn0) mode sk bb = (cc,t) ==>
  ?r pre chunk post u v.
    j <= r /\ r < LENGTH bb.bb_instructions /\
    rep_of_group bb.bb_instructions cg = SOME ((EL r bb.bb_instructions).inst_id,cg) /\
    cc.bb_instructions = pre ++ chunk ++ post /\
    mm_flat_map_supply
      (apply_groups_inst_supply mode
        (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
          (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
        (rep_map_of_groups bb.bb_instructions
          (scan_block (dfg_build_function fn0) mode bb).ss_flushed))
      sk (TAKE r bb.bb_instructions) = (pre,u) /\
    (((cg.cg_length <> 32 \/ mode = DloadMerge) /\
       chunk = [mk_bulk_copy_inst mode (EL r bb.bb_instructions) cg] /\ v = u) \/
     (cg.cg_length = 32 /\ mode <> DloadMerge /\
       (EL r bb.bb_instructions).inst_opcode = MSTORE /\
       chunk = [EL r bb.bb_instructions] /\ v = u) \/
     (cg.cg_length = 32 /\ mode <> DloadMerge /\
       (EL r bb.bb_instructions).inst_opcode <> MSTORE /\
       ?load_id s1 load_var. fresh_inst_id u = (load_id,s1) /\
         fresh_ir_var s1 = (load_var,v) /\
         chunk = [mk_load_inst mode ((EL r bb.bb_instructions) with inst_id := load_id)
                    cg.cg_src load_var;
                  mk_mstore_from_load (EL r bb.bb_instructions) cg.cg_dst load_var]))
Proof
  strip_tac >> drule_all mm_local_event_rep_position >> strip_tac >>
  `MEM (EL r bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_all mm_local_prefix_selected_rep >> strip_tac >>
  drule mm_local_mode_emission_cut >> disch_then (qspec_then `r` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all mm_local_selected_chunk >> strip_tac >>
  qexistsl [`r`,`pre`,`chunk`,`post`,`u`,`v`] >> simp[]
QED

Theorem mm_local_zero_add_unique[local]:
  ALL_DISTINCT (mm_local_group_ids mz.mz_flushed ++
    mm_local_group_ids mz.mz_copies ++ id::todo) /\ cg.cg_inst_ids = [id] ==>
  ALL_DISTINCT (mm_local_group_ids mz.mz_flushed ++
    mm_local_group_ids (add_copy mz.mz_copies cg) ++ todo)
Proof
  strip_tac >>
  mp_tac (Q.INST [`proj` |-> `\x:num. T`, `ss` |->
    `<| ss_flushed := mz.mz_flushed; ss_copies := mz.mz_copies; ss_loads := FEMPTY |>`]
    mm_local_add_current_unique) >>
  simp[mm_local_scan_unique_def]
QED

Theorem mm_local_zero_inst_unique[local]:
  ALL_DISTINCT (mm_local_group_ids mz.mz_flushed ++
    mm_local_group_ids mz.mz_copies ++ inst.inst_id::todo) ==>
  ALL_DISTINCT (mm_local_group_ids (scan_inst_memzero dfg mz inst).mz_flushed ++
    mm_local_group_ids (scan_inst_memzero dfg mz inst).mz_copies ++ todo)
Proof
  strip_tac >>
  `ALL_DISTINCT (mm_local_group_ids mz.mz_flushed ++
    mm_local_group_ids mz.mz_copies ++ todo)` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `ALL_DISTINCT (mm_local_group_ids (memzero_barrier mz).mz_flushed ++
      mm_local_group_ids (memzero_barrier mz).mz_copies ++ todo)` by
    gvs[memzero_barrier_def, mm_local_group_ids_append,
        mm_local_group_ids_def, APPEND_ASSOC] >>
  Cases_on `inst.inst_operands`
  >- (simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
      IF_CASES_TAC >> simp[]) >>
  rename1 `inst.inst_operands = dst::ops` >> Cases_on `ops`
  >- (simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
      IF_CASES_TAC >> simp[]) >>
  rename1 `inst.inst_operands = dst::src::ops` >> Cases_on `ops`
  >- (simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
      rpt IF_CASES_TAC >> simp[] >>
      Cases_on `operand_lit_val dst` >> simp[] >>
      irule mm_local_zero_add_unique >> qexists `inst.inst_id` >> simp[copy_memzero_def]) >>
  rename1 `inst.inst_operands = dst::src::len::ops` >> Cases_on `ops` >>
  simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `operand_lit_val dst` >> simp[] >>
  Cases_on `operand_lit_val len` >> simp[] >>
  irule mm_local_zero_add_unique >> qexists `inst.inst_id` >> simp[copy_memzero_def]
QED

Theorem mm_local_zero_fold_unique[local]:
  !xs mz. ALL_DISTINCT (mm_local_group_ids mz.mz_flushed ++
    mm_local_group_ids mz.mz_copies ++ MAP (\i. i.inst_id) xs ++ todo) ==>
  ALL_DISTINCT (mm_local_group_ids (FOLDL (scan_inst_memzero dfg) mz xs).mz_flushed ++
    mm_local_group_ids (FOLDL (scan_inst_memzero dfg) mz xs).mz_copies ++ todo)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  mp_tac (Q.INST [`todo` |-> `MAP (\i. i.inst_id) xs ++ todo`,
    `inst` |-> `h`, `mz` |-> `mz`] mm_local_zero_inst_unique) >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, listTheory.APPEND] >>
  metis_tac[]
QED

Theorem mm_local_zero_scan_unique[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  ALL_DISTINCT (mm_local_group_ids (scan_block_memzero dfg bb).mz_flushed)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`bb.bb_instructions`,`empty_memzero_state`]
    (Q.INST [`todo` |-> `[]`] mm_local_zero_fold_unique)) >>
  simp[empty_memzero_state_def, mm_local_group_ids_def] >>
  simp[GSYM mm_local_group_ids_def, scan_block_memzero_def,
       memzero_barrier_def, mm_local_group_ids_append, empty_memzero_state_def]
QED

Theorem mm_local_zero_selected_rep[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM cg (scan_block_memzero dfg bb).mz_flushed /\
  rep_of_group bb.bb_instructions cg = SOME (id,cg) ==>
  ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block_memzero dfg bb).mz_flushed) id = SOME cg /\
  ~MEM id (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
    (scan_block_memzero dfg bb).mz_flushed)
Proof
  strip_tac >>
  `ALL_DISTINCT (FILTER (\x:num. T)
      (mm_local_group_ids (scan_block_memzero dfg bb).mz_flushed))` by
    simp[mm_local_zero_scan_unique] >>
  `MEM id cg.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  conj_tac
  >- (irule mm_local_rep_lookup >> simp[] >> qexists `\x:num. T` >> simp[]) >>
  irule mm_local_rep_not_nop >> simp[] >> qexists `cg` >> simp[] >>
  rpt strip_tac >> irule mm_local_projected_owner >>
  qexistsl [`(scan_block_memzero dfg bb).mz_flushed`,`id`,`\x:num. T`] >> simp[]
QED

Theorem mm_local_zero_emission_cut[local]:
  transform_block_memzero_supply dfg supply bb = (cc,sk) /\
  j < LENGTH bb.bb_instructions ==>
  ?pre chunk post u v.
    mm_flat_map_supply
      (apply_memzero_inst_supply
        (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed)
        (rep_map_of_groups bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed))
      supply (TAKE j bb.bb_instructions) = (pre,u) /\
    apply_memzero_inst_supply
      (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed)
      (rep_map_of_groups bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed)
      u (EL j bb.bb_instructions) = (chunk,v) /\
    cc.bb_instructions = pre ++ chunk ++ post
Proof
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule_all mm_local_supply_cut >> metis_tac[]
QED

Theorem mm_local_zero_selected_chunk[local]:
  ~MEM i.inst_id ns /\ ALOOKUP rm i.inst_id = SOME cg /\
  apply_memzero_inst_supply ns rm u i = (chunk,v) ==>
  (cg.cg_length = 32 /\ chunk = [mk_zero_store_inst i cg.cg_dst] /\ v = u) \/
  (cg.cg_length <> 32 /\
    ?cds_id s1 cds_var. fresh_inst_id u = (cds_id,s1) /\
      fresh_ir_var s1 = (cds_var,v) /\
      chunk = [<| inst_id := cds_id; inst_opcode := CALLDATASIZE;
                  inst_operands := []; inst_outputs := [cds_var] |>;
               mk_memzero_calldatacopy i cg cds_var])
Proof
  simp[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem mm_local_zero_event_emission[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  j < LENGTH bb.bb_instructions /\
  MEM (EL j bb.bb_instructions).inst_id cg.cg_inst_ids /\
  MEM cg (scan_block_memzero dfg bb).mz_flushed /\
  transform_block_memzero_supply dfg supply bb = (cc,t) ==>
  ?r pre chunk post u v.
    j <= r /\ r < LENGTH bb.bb_instructions /\
    rep_of_group bb.bb_instructions cg = SOME ((EL r bb.bb_instructions).inst_id,cg) /\
    cc.bb_instructions = pre ++ chunk ++ post /\
    mm_flat_map_supply
      (apply_memzero_inst_supply
        (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed)
        (rep_map_of_groups bb.bb_instructions (scan_block_memzero dfg bb).mz_flushed))
      supply (TAKE r bb.bb_instructions) = (pre,u) /\
    ((cg.cg_length = 32 /\
      chunk = [mk_zero_store_inst (EL r bb.bb_instructions) cg.cg_dst] /\ v = u) \/
     (cg.cg_length <> 32 /\
      ?cds_id s1 cds_var. fresh_inst_id u = (cds_id,s1) /\
        fresh_ir_var s1 = (cds_var,v) /\
        chunk = [<| inst_id := cds_id; inst_opcode := CALLDATASIZE;
                    inst_operands := []; inst_outputs := [cds_var] |>;
                 mk_memzero_calldatacopy (EL r bb.bb_instructions) cg cds_var]))
Proof
  strip_tac >> drule_all mm_local_event_rep_position >> strip_tac >>
  drule_all mm_local_zero_selected_rep >> strip_tac >>
  drule mm_local_zero_emission_cut >> disch_then (qspec_then `r` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all mm_local_zero_selected_chunk >> strip_tac >>
  qexistsl [`r`,`pre`,`chunk`,`post`,`u`,`v`] >> simp[]
QED

Theorem mm_local_known_value_frame[local]:
  lookup_var x s = SOME value /\ step_inst_base inst s = OK t /\
  ~MEM (Var x) inst.inst_operands /\ ~MEM x inst.inst_outputs ==>
  lookup_var x t = SOME value
Proof
  strip_tac >>
  `update_var x value s = s` by
    (simp[venomStateTheory.update_var_def] >>
     `s.vs_vars |+ (x,value) = s.vs_vars` by
       (irule finite_mapTheory.FUPDATE_ELIM >>
        gvs[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DEF]) >>
     simp[]) >>
  `step_inst_base inst (update_var x value s) =
   map_result_state (update_var x value) (step_inst_base inst s)` by
    (irule step_inst_base_frame >> metis_tac[]) >>
  gvs[map_result_state_def] >>
  qpat_x_assum `t = update_var x value t` (fn th => once_rewrite_tac[th]) >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem mm_local_read_write_disjoint[local]:
  n = 0 \/ bs = [] \/ a+n <= d \/ d+LENGTH bs <= a ==>
  read_memory a n (write_memory_with_expansion d bs s) = read_memory a n s
Proof
  Cases_on `n = 0` >- simp[venomStateTheory.read_memory_def] >>
  Cases_on `bs = []`
  >- (gvs[venomStateTheory.read_memory_def, write_as_replace,
          replace_bytes_def, expand_mem_def] >>
      rw[LIST_EQ_REWRITE, EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE] >>
      rw[] >> gvs[]) >>
  strip_tac >>
  simp[venomStateTheory.read_memory_def, write_as_replace] >>
  irule read_nonoverlap_expand >> simp[]
QED

Theorem mm_local_read_write_log[local]:
  !ws s. EVERY (\(d,bs). n = 0 \/ bs = [] \/ a+n <= d \/ d+LENGTH bs <= a) ws ==>
  read_memory a n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
  read_memory a n s
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then (fn th => rewrite_tac[th])) >>
  simp[mm_local_read_write_disjoint]
QED

Theorem mm_local_read_write_log_memory[local]:
  u.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory /\
  EVERY (\(d,bs). n = 0 \/ bs = [] \/ a+n <= d \/ d+LENGTH bs <= a) ws ==>
  read_memory a n u = read_memory a n v
Proof
  strip_tac >>
  `read_memory a n u = read_memory a n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws)` by
    simp[venomStateTheory.read_memory_def] >>
  metis_tac[mm_local_read_write_log]
QED

Theorem mm_local_mload_write_log_memory[local]:
  u.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory /\
  EVERY (\(d,bs). a+32 <= d \/ d+LENGTH bs <= a) ws ==>
  mload a u = mload a v
Proof
  strip_tac >>
  `read_memory a 32 u = read_memory a 32 v` by
    (irule mm_local_read_write_log_memory >> qexists_tac `ws` >>
     simp[] >> gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  gvs[venomStateTheory.read_memory_def, venomStateTheory.mload_def]
QED

Theorem mm_local_mcopy_write_log[local]:
  EVERY (\(d,bs). (src+n <= d \/ d+LENGTH bs <= src) /\
                     (dst+n <= d \/ d+LENGTH bs <= dst)) ws ==>
  mcopy dst src n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (mcopy dst src n s) ws
Proof
  strip_tac >>
  `EVERY (\(d,bs). n = 0 \/ bs = [] \/ src+n <= d \/ d+LENGTH bs <= src) ws` by
    (gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `read_memory src n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
    read_memory src n s` by simp[mm_local_read_write_log] >>
  simp[venomExecSemanticsTheory.mcopy_def,
       GSYM venomStateTheory.read_memory_def] >>
  irule mm_local_write_log_commute >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD, venomStateTheory.read_memory_def,
      LENGTH_TAKE, LENGTH_DROP] >> metis_tac[]
QED

Theorem mm_local_mcopy_write_log_memory[local]:
  u.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory /\
  EVERY (\(d,bs). (src+n <= d \/ d+LENGTH bs <= src) /\
                     (dst+n <= d \/ d+LENGTH bs <= dst)) ws ==>
  (mcopy dst src n u).vs_memory =
  (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (mcopy dst src n v) ws).vs_memory
Proof
  strip_tac >>
  drule mm_local_mcopy_write_log >>
  disch_then (qspec_then `v` (fn th => once_rewrite_tac[GSYM th])) >>
  simp[venomExecSemanticsTheory.mcopy_def, write_as_replace]
QED

(* Byte compatibility, not disjointness, is needed for an overlapping discharge. *)
Theorem mm_local_payload_replace_merge[local]:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  d1 + LENGTH merged <= LENGTH mem ==>
  replace_bytes d2 bs2 (replace_bytes d1 bs1 mem) =
  replace_bytes d1 merged mem
Proof
  strip_tac >>
  `LENGTH bs1 <= LENGTH merged /\ d2-d1 + LENGTH bs2 <= LENGTH merged` by
    (gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!i. i < LENGTH bs1 ==> EL i bs1 = EL i merged` by
    metis_tac[EL_TAKE] >>
  `!i. i < LENGTH bs2 ==> EL i bs2 = EL (i + (d2-d1)) merged` by
    (rpt strip_tac >> qpat_x_assum `bs2 = _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_TAKE, EL_DROP]) >>
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  gvs[EL_DROP, arithmeticTheory.MAX_DEF]
QED

Theorem mm_local_payload_write_merge[local]:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) ==>
  write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 s) =
  write_memory_with_expansion d1 merged s
Proof
  strip_tac >> simp[write_as_replace] >>
  `d1 + LENGTH bs1 <= LENGTH (expand_mem s.vs_memory (d1 + LENGTH bs1))` by
    simp[expand_mem_ge] >>
  simp[expand_replace, venomStateTheory.venom_state_component_equality,
       mm_local_expand_mem_max] >>
  irule mm_local_payload_replace_merge >> simp[expand_mem_ge]
QED

Theorem mm_local_payload_log_merge[local]:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  EVERY (\(d,bs). d + LENGTH bs <= d2 \/ d2 + LENGTH bs2 <= d) ws ==>
  write_memory_with_expansion d2 bs2
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 bs1 s) ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (write_memory_with_expansion d1 merged s) ws
Proof
  strip_tac >>
  drule_all mm_local_payload_write_merge >>
  disch_then (qspec_then `s` assume_tac) >>
  simp[mm_local_write_log_commute]
QED

(* Runtime discharge is at the later representative, not scanner flush time. *)
Theorem mm_local_payload_late_discharge[local]:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  EVERY (\(d,bs). d + LENGTH bs <= d1 \/ d1 + LENGTH bs1 <= d) ws ==>
  write_memory_with_expansion d2 bs2
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 bs1 s) ws) =
  write_memory_with_expansion d1 merged
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws)
Proof
  strip_tac >>
  drule_all mm_local_payload_write_merge >> strip_tac >>
  drule mm_local_write_log_commute >>
  disch_then (qspec_then `s` (fn th => once_rewrite_tac[GSYM th])) >>
  simp[]
QED

Theorem mm_local_payload_replace_merge_reverse[local]:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  d1 + LENGTH merged <= LENGTH mem ==>
  replace_bytes d1 bs1 (replace_bytes d2 bs2 mem) =
  replace_bytes d1 merged mem
Proof
  strip_tac >>
  `LENGTH bs1 <= LENGTH merged /\ d2-d1 + LENGTH bs2 <= LENGTH merged` by
    (gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!i. i < LENGTH bs1 ==> EL i bs1 = EL i merged` by
    metis_tac[EL_TAKE] >>
  `!i. i < LENGTH bs2 ==> EL i bs2 = EL (i + (d2-d1)) merged` by
    (rpt strip_tac >> qpat_x_assum `bs2 = _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_TAKE, EL_DROP]) >>
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  gvs[EL_DROP, arithmeticTheory.MAX_DEF]
QED

Theorem mm_local_payload_write_merge_reverse[local]:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) ==>
  write_memory_with_expansion d1 bs1 (write_memory_with_expansion d2 bs2 s) =
  write_memory_with_expansion d1 merged s
Proof
  strip_tac >> simp[write_as_replace] >>
  `d2 + LENGTH bs2 <= LENGTH (expand_mem s.vs_memory (d2 + LENGTH bs2))` by
    simp[expand_mem_ge] >>
  simp[expand_replace, venomStateTheory.venom_state_component_equality,
       mm_local_expand_mem_max, arithmeticTheory.MAX_COMM] >>
  irule mm_local_payload_replace_merge_reverse >> simp[expand_mem_ge]
QED

Theorem mm_local_payload_write_merge_unordered[local]:
  dst = MIN d1 d2 /\
  MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) = dst + LENGTH merged /\
  (d1 <= d2 /\ d2 <= d1 + LENGTH bs1 \/
   d2 <= d1 /\ d1 <= d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) (DROP (d1-dst) merged) /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-dst) merged) ==>
  write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 s) =
  write_memory_with_expansion dst merged s
Proof
  strip_tac >> Cases_on `d1 <= d2`
  >- (`dst = d1` by simp[arithmeticTheory.MIN_DEF] >> gvs[] >>
      irule mm_local_payload_write_merge >>
      simp[] >> gvs[arithmeticTheory.MAX_DEF]) >>
  `dst = d2` by simp[arithmeticTheory.MIN_DEF] >> gvs[] >>
  irule mm_local_payload_write_merge_reverse >>
  simp[arithmeticTheory.MAX_COMM]
QED

Theorem mm_local_payload_late_discharge_unordered[local]:
  dst = MIN d1 d2 /\
  MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) = dst + LENGTH merged /\
  (d1 <= d2 /\ d2 <= d1 + LENGTH bs1 \/
   d2 <= d1 /\ d1 <= d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) (DROP (d1-dst) merged) /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-dst) merged) /\
  EVERY (\(d,bs). d + LENGTH bs <= d1 \/ d1 + LENGTH bs1 <= d) ws ==>
  write_memory_with_expansion d2 bs2
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 bs1 s) ws) =
  write_memory_with_expansion dst merged
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws)
Proof
  strip_tac >>
  `!v. write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 v) =
       write_memory_with_expansion dst merged v` by
    (gen_tac >> irule mm_local_payload_write_merge_unordered >> simp[]) >>
  drule mm_local_write_log_commute >>
  disch_then (qspec_then `s` (fn th => once_rewrite_tac[GSYM th])) >>
  simp[]
QED

(* Historical cuts keep captures and static emission schedules separate. *)
Definition mm_local_history_def:
  mm_local_history is H n <=>
    n <= LENGTH is /\
    !j. j < n ==> step_inst_base (EL j is) (H j) = OK (H (SUC j))
End

Definition mm_local_write_capture_def:
  mm_local_write_capture is H n j =
    if j < n /\ j < LENGTH is then
      if (EL j is).inst_opcode = MSTORE then
        (case (EL j is).inst_operands of
           [a;b] =>
             (case (eval_operand a (H j), eval_operand b (H j)) of
                (SOME dst,SOME value) => SOME (w2n dst,word_to_bytes value T)
              | _ => NONE)
         | _ => NONE)
      else if (EL j is).inst_opcode = MCOPY then
        (case (EL j is).inst_operands of
           [a;b;c] =>
             (case (eval_operand a (H j),eval_operand b (H j),eval_operand c (H j)) of
                (SOME dst,SOME src,SOME len) =>
                  SOME (w2n dst,read_memory (w2n src) (w2n len) (H j))
              | _ => NONE)
         | _ => NONE)
      else NONE
    else NONE
End

Theorem mm_local_write_capture_past[local]:
  j < n /\ n <= m ==>
  mm_local_write_capture is H n j = mm_local_write_capture is H m j
Proof
  simp[mm_local_write_capture_def]
QED

Theorem mm_local_write_capture_future[local]:
  n <= j ==> mm_local_write_capture is H n j = NONE
Proof
  simp[mm_local_write_capture_def]
QED

Theorem mm_local_write_capture_sound[local]:
  mm_local_history is H n /\ mm_local_write_capture is H n j = SOME (d,bs) ==>
  (H (SUC j)).vs_memory = (write_memory_with_expansion d bs (H j)).vs_memory
Proof
  simp[mm_local_write_capture_def] >>
  rpt IF_CASES_TAC >> gvs[AllCaseEqs()] >> strip_tac >>
  `step_inst_base (EL j is) (H j) = OK (H (SUC j))` by
    metis_tac[mm_local_history_def] >>
  gvs[venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_write2_def,
      venomMemPropsTheory.mstore_eq_write_mem,
      venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]
QED

Theorem mm_local_write_capture_copy[local]:
  j < n /\ mm_local_history is H n /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] ==>
  mm_local_write_capture is H n j =
    SOME (w2n dst,read_memory (w2n src) (w2n len) (H j)) /\
  LENGTH (read_memory (w2n src) (w2n len) (H j)) = w2n len
Proof
  simp[mm_local_history_def, mm_local_write_capture_def,
       venomStateTheory.eval_operand_def, venomStateTheory.read_memory_def] >>
  rpt strip_tac >> simp[]
QED

Theorem mm_local_write_capture_store[local]:
  j < n /\ mm_local_history is H n /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\ lookup_var v (H j) = SOME value ==>
  mm_local_write_capture is H n j = SOME (w2n dst,word_to_bytes value T) /\
  LENGTH (word_to_bytes value T) = 32
Proof
  simp[mm_local_history_def, mm_local_write_capture_def,
       venomStateTheory.eval_operand_def] >> rpt strip_tac >> simp[]
QED

Theorem mm_local_write_capture_expansion[local]:
  mm_local_history is H n /\ mm_local_write_capture is H n j = SOME (d,bs) ==>
  LENGTH (H (SUC j)).vs_memory = MAX (LENGTH (H j).vs_memory) (d + LENGTH bs)
Proof
  strip_tac >> drule_all mm_local_write_capture_sound >>
  disch_then SUBST1_TAC >> simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion]
QED

Definition mm_local_owned_def:
  mm_local_owned (cap:num -> (num # word8 list) option) rep n js <=>
    ALL_DISTINCT js /\ SORTED ($<) js /\
    EVERY (\j. j < n /\ n <= rep j /\ ?d bs. cap j = SOME (d,bs)) js
End

Definition mm_local_pending_def:
  mm_local_pending cap js s t <=>
    ?ws. LIST_REL (\j w. cap j = SOME w) js ws /\
      s.vs_memory =
        (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) t ws).vs_memory
End

Theorem mm_local_pending_empty[local]:
  mm_local_pending cap [] s t <=> s.vs_memory = t.vs_memory
Proof
  simp[mm_local_pending_def]
QED

Theorem mm_local_history_last[local]:
  mm_local_history is H (SUC n) ==>
  mm_local_history is H n /\ step_inst_base (EL n is) (H n) = OK (H (SUC n))
Proof
  simp[mm_local_history_def] >> rpt strip_tac >> gvs[]
QED

Theorem mm_local_pending_log[local]:
  !js ws s t. mm_local_pending cap js s t /\
    LIST_REL (\j w. cap j = SOME w) js ws ==>
    s.vs_memory =
      (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) t ws).vs_memory
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >>
  `MAP cap js = MAP SOME ws` by metis_tac[MAP_EQ_EVERY2, LIST_REL_LENGTH] >>
  `MAP cap js = MAP SOME ws'` by metis_tac[MAP_EQ_EVERY2, LIST_REL_LENGTH] >>
  `ws = ws'` by
    (qpat_x_assum `MAP cap js = MAP SOME ws` mp_tac >> simp[] >>
     disch_then (mp_tac o AP_TERM
       ``MAP (THE : (num # word8 list) option -> num # word8 list)``) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, MAP_ID]) >>
  gvs[]
QED

Theorem mm_local_write_log_memory_cong[local]:
  !ws s t. s.vs_memory = t.vs_memory ==>
  (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws).vs_memory =
  (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) t ws).vs_memory
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[write_as_replace]
QED

Theorem mm_local_pending_create[local]:
  mm_local_pending cap js s t /\ cap n = SOME (d,bs) /\
  s'.vs_memory = (write_memory_with_expansion d bs s).vs_memory ==>
  mm_local_pending cap (js ++ [n]) s' t
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >>
  qexists `ws ++ [(d,bs)]` >>
  simp[LIST_REL_APPEND, FOLDL_APPEND, write_as_replace]
QED

Theorem mm_local_owned_create[local]:
  mm_local_owned cap rep n js /\ cap n = SOME (d,bs) /\
  SUC n <= rep n /\ EVERY (\j. SUC n <= rep j) js ==>
  mm_local_owned cap rep (SUC n) (js ++ [n])
Proof
  simp[mm_local_owned_def, EVERY_MEM] >> strip_tac >>
  `!j. MEM j js ==> j < n` by metis_tac[] >>
  `~MEM n js` by metis_tac[prim_recTheory.LESS_REFL] >>
  simp[ALL_DISTINCT_APPEND, sortingTheory.SORTED_APPEND,
       relationTheory.transitive_def] >>
  rpt strip_tac >> gvs[] >> irule prim_recTheory.SUC_LESS >> simp[]
QED

Theorem mm_local_capture_create[local]:
  EVERY (\j. ?d bs. cap j = SOME (d,bs) /\ C (EL j is) (H j) d bs) js /\
  cap n = SOME (d,bs) /\ C (EL n is) (H n) d bs ==>
  EVERY (\j. ?d bs. cap j = SOME (d,bs) /\ C (EL j is) (H j) d bs) (js ++ [n])
Proof
  simp[] >> metis_tac[]
QED

Theorem mm_local_pending_survivor[local]:
  mm_local_pending cap js s t /\ LIST_REL (\j w. cap j = SOME w) js ws /\
  EVERY (\(a,bs). a + LENGTH bs <= d \/ d + LENGTH payload <= a) ws /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion d payload t).vs_memory ==>
  mm_local_pending cap js s' t'
Proof
  strip_tac >> drule_all mm_local_pending_log >> strip_tac >>
  simp[mm_local_pending_def] >> qexists `ws` >> simp[] >>
  drule mm_local_write_log_commute >>
  disch_then (qspec_then `t` mp_tac) >> strip_tac >>
  `s'.vs_memory =
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st)
      (write_memory_with_expansion d payload t) ws).vs_memory` by
    (qpat_x_assum `write_memory_with_expansion _ _ _ = _`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[write_as_replace]) >>
  metis_tac[mm_local_write_log_memory_cong]
QED

Theorem mm_local_owned_discharge[local]:
  mm_local_owned cap rep n (done ++ keep) /\
  EVERY (\j. rep j = n) done /\ EVERY (\j. SUC n <= rep j) keep ==>
  mm_local_owned cap rep (SUC n) keep
Proof
  simp[mm_local_owned_def, EVERY_MEM, ALL_DISTINCT_APPEND,
       sortingTheory.SORTED_APPEND_GEN] >> rpt strip_tac >> gvs[] >>
  simp[prim_recTheory.SUC_LESS]
QED

Theorem mm_local_pending_discharge_prefix[local]:
  mm_local_pending cap (done ++ keep) s t /\
  LIST_REL (\j w. cap j = SOME w) done old /\
  LIST_REL (\j w. cap j = SOME w) keep rest /\
  (!v. write_memory_with_expansion d payload
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st) v old) =
    write_memory_with_expansion dst merged v) /\
  EVERY (\(a,bs). a + LENGTH bs <= d \/ d + LENGTH payload <= a) rest /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion dst merged t).vs_memory ==>
  mm_local_pending cap keep s' t'
Proof
  strip_tac >>
  `LIST_REL (\j w. cap j = SOME w) (done ++ keep) (old ++ rest)` by
    (irule rich_listTheory.EVERY2_APPEND_suff >> simp[]) >>
  drule_all mm_local_pending_log >> simp[FOLDL_APPEND] >> strip_tac >>
  drule mm_local_write_log_commute >>
  disch_then (qspec_then
    `FOLDL (\st (a,bs). write_memory_with_expansion a bs st) t old` mp_tac) >>
  simp[] >> strip_tac >>
  `s'.vs_memory =
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st)
      (write_memory_with_expansion dst merged t) rest).vs_memory` by
    (qpat_x_assum `write_memory_with_expansion _ _ _ = _`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[write_as_replace]) >>
  simp[mm_local_pending_def] >> qexists `rest` >> simp[] >>
  metis_tac[mm_local_write_log_memory_cong]
QED

Theorem mm_local_snapshot_copy[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [Lit dst; Lit src; Lit len] /\
  step_inst fuel ctx inst s = OK t /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
          cg_inst_ids := [inst.inst_id] |> /\
  MEM g (flush_hazards Mem2Mem ss c).ss_copies ==>
  read_memory g.cg_src g.cg_length t = read_memory g.cg_src g.cg_length s
Proof
  strip_tac >> drule_all mm_local_capture_copy >> strip_tac >>
  drule mm_local_flush_hazards_read >>
  disch_then (qspecl_then [`s`, `read_memory (w2n src) (w2n len) s`] mp_tac) >>
  gvs[venomStateTheory.read_memory_def, LENGTH_TAKE, LENGTH_DROP]
QED

Theorem mm_local_snapshot_store[local]:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [Lit dst; Var v] /\
  lookup_var v s = SOME (mload src s) /\ step_inst fuel ctx inst s = OK t /\
  c.cg_dst = w2n dst /\ c.cg_src = src /\ c.cg_length = 32 /\
  MEM g (flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval (w2n dst) 32)) c).ss_copies ==>
  read_memory g.cg_src g.cg_length t = read_memory g.cg_src g.cg_length s
Proof
  strip_tac >> drule_all mm_local_capture_store >> strip_tac >>
  drule mm_local_flush_hazards_read >>
  disch_then (qspecl_then [`s`, `read_memory src 32 s`] mp_tac) >>
  gvs[venomStateTheory.read_memory_def, LENGTH_TAKE, LENGTH_DROP]
QED

Theorem mm_local_snapshot_copy_base[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [Lit dst; Lit src; Lit len] /\
  step_inst_base inst s = OK t /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
          cg_inst_ids := [inst.inst_id] |> /\
  MEM g (flush_hazards Mem2Mem ss c).ss_copies ==>
  read_memory g.cg_src g.cg_length t = read_memory g.cg_src g.cg_length s
Proof
  strip_tac >>
  `step_inst 0 ARB inst s = OK t` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all mm_local_snapshot_copy >> simp[]
QED

Theorem mm_local_snapshot_store_base[local]:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [Lit dst; Var v] /\
  lookup_var v s = SOME (mload src s) /\ step_inst_base inst s = OK t /\
  c.cg_dst = w2n dst /\ c.cg_src = src /\ c.cg_length = 32 /\
  MEM g (flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval (w2n dst) 32)) c).ss_copies ==>
  read_memory g.cg_src g.cg_length t = read_memory g.cg_src g.cg_length s
Proof
  strip_tac >>
  `step_inst 0 ARB inst s = OK t` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all mm_local_snapshot_store >> simp[]
QED

Theorem mm_local_snapshot_segment[local]:
  !b a. a <= b /\ mm_local_history is H b /\
  (!j. a <= j /\ j < b ==>
    (H (SUC j)).vs_memory = (H j).vs_memory \/
    (?dst src len. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
      c j = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
                cg_inst_ids := [(EL j is).inst_id] |> /\
      MEM g (flush_hazards Mem2Mem (ss j) (c j)).ss_copies) \/
    (?dst v src. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Var v] /\
      lookup_var v (H j) = SOME (mload src (H j)) /\
      (c j).cg_dst = w2n dst /\ (c j).cg_src = src /\ (c j).cg_length = 32 /\
      MEM g (flush_hazards Mem2Mem
        (invalidate_loads (ss j) (mk_interval (w2n dst) 32)) (c j)).ss_copies)) ==>
  read_memory g.cg_src g.cg_length (H b) = read_memory g.cg_src g.cg_length (H a)
Proof
  Induct_on `b` >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `a = SUC b` >- simp[] >>
  `a <= b` by decide_tac >>
  drule mm_local_history_last >> strip_tac >>
  `read_memory g.cg_src g.cg_length (H (SUC b)) =
   read_memory g.cg_src g.cg_length (H b)` by
    (qpat_x_assum `!j. _` (qspec_then `b` mp_tac) >> simp[] >>
     strip_tac
     >- simp[venomStateTheory.read_memory_def]
     >- (drule_all mm_local_snapshot_copy_base >> simp[]) >>
     metis_tac[mm_local_snapshot_store_base]) >>
  simp[] >> first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Definition mm_local_bytes_def:
  mm_local_bytes (B:num -> word8) a n = GENLIST (\i. B (a+i)) n
End

Theorem mm_local_bytes_length[local, simp]:
  LENGTH (mm_local_bytes B a n) = n
Proof
  simp[mm_local_bytes_def]
QED

Theorem mm_local_bytes_restrict[local]:
  off+n <= len ==>
  mm_local_bytes B (a+off) n = TAKE n (DROP off (mm_local_bytes B a len))
Proof
  strip_tac >>
  pure_rewrite_tac[mm_local_bytes_def, DROP_GENLIST, TAKE_GENLIST,
                   combinTheory.o_DEF] >>
  `MIN n (len-off) = n` by (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  asm_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> irule GENLIST_EQ >> simp[]
QED

Theorem mm_local_bytes_merge_compat[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  c2.cg_dst <= c1.cg_dst + c1.cg_length /\
  c1.cg_dst + (copy_merge c1 c2).cg_length =
    MAX (c1.cg_dst + c1.cg_length) (c2.cg_dst + c2.cg_length) /\
  mm_local_bytes B c1.cg_src c1.cg_length =
    TAKE c1.cg_length (mm_local_bytes B (copy_merge c1 c2).cg_src
      (copy_merge c1 c2).cg_length) /\
  mm_local_bytes B c2.cg_src c2.cg_length =
    TAKE c2.cg_length (DROP (c2.cg_dst-c1.cg_dst)
      (mm_local_bytes B (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length))
Proof
  simp[copy_can_merge_def, copy_merge_def] >> strip_tac >>
  `c2.cg_src = c1.cg_src + (c2.cg_dst-c1.cg_dst)` by decide_tac >>
  `c1.cg_length <= MAX (c1.cg_dst+c1.cg_length)
      (c2.cg_dst+c2.cg_length) - c1.cg_dst /\
   c2.cg_dst-c1.cg_dst+c2.cg_length <= MAX (c1.cg_dst+c1.cg_length)
      (c2.cg_dst+c2.cg_length) - c1.cg_dst` by
    (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  conj_tac >- (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`off` |-> `0`] mm_local_bytes_restrict)) >> simp[]) >>
  metis_tac[mm_local_bytes_restrict]
QED

Theorem mm_local_bytes_write_merge[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  write_memory_with_expansion c2.cg_dst (mm_local_bytes B c2.cg_src c2.cg_length)
    (write_memory_with_expansion c1.cg_dst (mm_local_bytes B c1.cg_src c1.cg_length) s) =
  write_memory_with_expansion (copy_merge c1 c2).cg_dst
    (mm_local_bytes B (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length) s
Proof
  strip_tac >> drule_all mm_local_bytes_merge_compat >>
  disch_then (qspec_then `B` strip_assume_tac) >>
  simpLib.SIMP_TAC (srw_ss()) [copy_merge_def] >>
  irule mm_local_payload_write_merge >>
  pure_rewrite_tac[mm_local_bytes_length] >> gvs[copy_merge_def]
QED

Theorem mm_local_bytes_write_merge_reverse[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  write_memory_with_expansion c1.cg_dst (mm_local_bytes B c1.cg_src c1.cg_length)
    (write_memory_with_expansion c2.cg_dst (mm_local_bytes B c2.cg_src c2.cg_length) s) =
  write_memory_with_expansion (copy_merge c1 c2).cg_dst
    (mm_local_bytes B (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length) s
Proof
  strip_tac >> drule_all mm_local_bytes_merge_compat >>
  disch_then (qspec_then `B` strip_assume_tac) >>
  simpLib.SIMP_TAC (srw_ss()) [copy_merge_def] >>
  irule mm_local_payload_write_merge_reverse >>
  pure_rewrite_tac[mm_local_bytes_length] >> gvs[copy_merge_def]
QED

Theorem mm_local_bytes_merge_agreement[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 /\
  mm_local_bytes B c1.cg_src c1.cg_length = mm_local_bytes C c1.cg_src c1.cg_length /\
  mm_local_bytes B c2.cg_src c2.cg_length = mm_local_bytes C c2.cg_src c2.cg_length ==>
  mm_local_bytes B (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length =
  mm_local_bytes C (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length
Proof
  simp[mm_local_bytes_def, GENLIST_FUN_EQ, copy_can_merge_def, copy_merge_def] >>
  strip_tac >> qx_gen_tac `i` >> strip_tac >>
  Cases_on `i < c1.cg_length`
  >- (first_x_assum irule >> simp[]) >>
  `c2.cg_src = c1.cg_src + (c2.cg_dst-c1.cg_dst)` by decide_tac >>
  `c2.cg_dst-c1.cg_dst <= i /\ i-(c2.cg_dst-c1.cg_dst) < c2.cg_length` by
    (qpat_x_assum `i < MAX _ _ - _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
  `c1.cg_src+i = c2.cg_src + (i-(c2.cg_dst-c1.cg_dst))` by decide_tac >>
  metis_tac[arithmeticTheory.ADD_SYM]
QED

Theorem mm_local_read_memory_bytes[local]:
  read_memory a n s =
  mm_local_bytes (\i. if i < LENGTH s.vs_memory then EL i s.vs_memory else 0w) a n
Proof
  simp[venomStateTheory.read_memory_def, mm_local_bytes_def,
       regularMemorySimTheory.venom_returndata_read_byte, codegenRelTheory.read_byte_def]
QED

Theorem mm_local_capture_rebase[local]:
  payload = read_memory a n (H j) /\
  read_memory a n (H k) = read_memory a n (H j) ==>
  payload = mm_local_bytes
    (\i. if i < LENGTH (H k).vs_memory then EL i (H k).vs_memory else 0w) a n
Proof
  metis_tac[mm_local_read_memory_bytes]
QED

Theorem mm_local_history_copy_compatible[local]:
  j < k /\ k < n /\ mm_local_history is H n /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst1; Lit src1; Lit len1] /\
  (EL k is).inst_opcode = MCOPY /\
  (EL k is).inst_operands = [Lit dst2; Lit src2; Lit len2] /\
  c1 = <| cg_dst := w2n dst1; cg_src := w2n src1; cg_length := w2n len1;
           cg_inst_ids := [(EL j is).inst_id] |> /\
  c2 = <| cg_dst := w2n dst2; cg_src := w2n src2; cg_length := w2n len2;
           cg_inst_ids := [(EL k is).inst_id] |> /\
  c1.cg_src + c2.cg_dst = c2.cg_src + c1.cg_dst /\
  mm_local_write_capture is H n j = SOME (d,bs) /\
  mm_local_write_capture is H n k = SOME (a,cs) /\
  LIST_REL (\q w. mm_local_write_capture is H n q = SOME w) (j::between) ws /\
  EVERY (\q. j < q /\ q < k) between /\
  (H k).vs_memory =
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st) (H j) ws).vs_memory /\
  EVERY (\(a,bs). c2.cg_length = 0 \/ bs = [] \/
    c2.cg_src + c2.cg_length <= a \/ a + LENGTH bs <= c2.cg_src) ws ==>
  mm_local_write_compatible d bs a cs
Proof
  strip_tac >>
  `j < n` by decide_tac >>
  `mm_local_write_capture is H n j =
    SOME (w2n dst1,read_memory (w2n src1) (w2n len1) (H j))` by
    (irule (cj 1 mm_local_write_capture_copy) >> simp[]) >>
  `mm_local_write_capture is H n k =
    SOME (w2n dst2,read_memory (w2n src2) (w2n len2) (H k))` by
    (irule (cj 1 mm_local_write_capture_copy) >> simp[]) >>
  `read_memory c2.cg_src c2.cg_length (H k) =
   read_memory c2.cg_src c2.cg_length (H j)` by
    (irule mm_local_read_write_log_memory >> qexists_tac `ws` >> simp[]) >>
  Cases_on `bs = []` >- simp[mm_local_write_compatible_def] >>
  gvs[] >>
  pure_rewrite_tac[mm_local_write_compatible_def, mm_local_read_memory_bytes,
       mm_local_bytes_def, LENGTH_GENLIST] >> rpt strip_tac >>
  `x - w2n dst1 < w2n len1 /\ x - w2n dst2 < w2n len2 /\
   w2n src1 + (x - w2n dst1) = w2n src2 + (x - w2n dst2)` by decide_tac >>
  asm_simp_tac bool_ss [EL_GENLIST] >> simp[]
QED

Theorem mm_local_capture_write_merge[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 /\
  p1 = read_memory c1.cg_src c1.cg_length (H j1) /\
  p2 = read_memory c2.cg_src c2.cg_length (H j2) /\
  read_memory c1.cg_src c1.cg_length (H k) = read_memory c1.cg_src c1.cg_length (H j1) /\
  read_memory c2.cg_src c2.cg_length (H k) = read_memory c2.cg_src c2.cg_length (H j2) ==>
  write_memory_with_expansion c2.cg_dst p2
    (write_memory_with_expansion c1.cg_dst p1 s) =
  write_memory_with_expansion (copy_merge c1 c2).cg_dst
    (read_memory (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length (H k)) s
Proof
  strip_tac >>
  `p1 = read_memory c1.cg_src c1.cg_length (H k) /\
   p2 = read_memory c2.cg_src c2.cg_length (H k)` by metis_tac[] >>
  qpat_x_assum `p1 = read_memory _ _ (H k)` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `p2 = read_memory _ _ (H k)` (fn th => once_rewrite_tac[th]) >>
  simpLib.SIMP_TAC (srw_ss()) [mm_local_read_memory_bytes] >>
  irule mm_local_bytes_write_merge >> simp[]
QED

Theorem mm_local_write_log_partition[local]:
  !js s.
  (!pre j mid k post. js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k ==>
    FST (wr j) + LENGTH (SND (wr j)) <= FST (wr k) \/
    FST (wr k) + LENGTH (SND (wr k)) <= FST (wr j)) ==>
  FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st) s js =
  FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
    (FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
      s (FILTER P js)) (FILTER (\j. ~P j) js)
Proof
  Induct_on `js` >- simp[] >> rpt gen_tac >> strip_tac >>
  `!pre j mid k post. js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k ==>
    FST (wr j) + LENGTH (SND (wr j)) <= FST (wr k) \/
    FST (wr k) + LENGTH (SND (wr k)) <= FST (wr j)` by
      (rpt strip_tac >>
       first_x_assum (qspecl_then [`h::pre`, `j`, `mid`, `k`, `post`] mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `write_memory_with_expansion (FST (wr h)) (SND (wr h)) s` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> Cases_on `P h`
  >- simp[] >>
  `EVERY (\(d,bs). d + LENGTH bs <= FST (wr h) \/
    FST (wr h) + LENGTH (SND (wr h)) <= d) (MAP wr (FILTER P js))` by
    (simp[EVERY_MEM, MEM_MAP, MEM_FILTER, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> gvs[] >>
     rename1 `MEM k js` >>
     qpat_x_assum `MEM k js`
       (qx_choose_then `pre` (qx_choose_then `post` assume_tac) o REWRITE_RULE [MEM_SPLIT]) >>
     qpat_x_assum `!pre j mid k post. h::js = _ /\ _ ==> _`
       (qspecl_then [`[]`, `h`, `pre`, `k`, `post`] mp_tac) >>
     gvs[quantHeuristicsTheory.PAIR_EQ_EXPAND]) >>
  drule mm_local_write_log_commute >> disch_then (qspec_then `s` mp_tac) >>
  simp[FOLDL_MAP, pairTheory.UNCURRY, combinTheory.o_DEF] >>
  strip_tac >> simp[]
QED

Theorem mm_local_write_log_compatible_partition[local]:
  !js s.
  (!pre j mid k post. js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k ==>
    mm_local_write_compatible (FST (wr j)) (SND (wr j))
      (FST (wr k)) (SND (wr k))) ==>
  FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st) s js =
  FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
    (FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
      s (FILTER P js)) (FILTER (\j. ~P j) js)
Proof
  Induct_on `js` >- simp[] >> rpt gen_tac >> strip_tac >>
  `!pre j mid k post. js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k ==>
    mm_local_write_compatible (FST (wr j)) (SND (wr j))
      (FST (wr k)) (SND (wr k))` by
      (rpt strip_tac >>
       first_x_assum (qspecl_then [`h::pre`, `j`, `mid`, `k`, `post`] mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `write_memory_with_expansion (FST (wr h)) (SND (wr h)) s` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> Cases_on `P h`
  >- simp[] >>
  `EVERY (\(d,bs). mm_local_write_compatible d bs (FST (wr h)) (SND (wr h)))
    (MAP wr (FILTER P js))` by
    (simp[EVERY_MEM, MEM_MAP, MEM_FILTER, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> gvs[] >>
     rename1 `MEM k js` >>
     qpat_x_assum `MEM k js`
       (qx_choose_then `pre` (qx_choose_then `post` assume_tac) o REWRITE_RULE [MEM_SPLIT]) >>
     qpat_x_assum `!pre j mid k post. h::js = _ /\ _ ==> _`
       (qspecl_then [`[]`, `h`, `pre`, `k`, `post`] mp_tac) >>
     gvs[quantHeuristicsTheory.PAIR_EQ_EXPAND] >>
     metis_tac[mm_local_write_compatible_sym]) >>
  drule mm_local_write_log_compatible_commute >> disch_then (qspec_then `s` mp_tac) >>
  simp[FOLDL_MAP, pairTheory.UNCURRY, combinTheory.o_DEF] >>
  strip_tac >> simp[]
QED

Theorem mm_local_capture_log_canonical[local]:
  !js ws. LIST_REL (\j w. cap j = SOME w) js ws ==>
    ws = MAP (THE o cap) js /\ EVERY (\j. IS_SOME (cap j)) js
Proof
  Induct_on `js` >> Cases_on `ws` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem mm_local_pending_partition[local]:
  mm_local_pending cap js s t /\
  (!pre j mid k post d bs a cs.
    js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k /\
    cap j = SOME (d,bs) /\ cap k = SOME (a,cs) ==>
    d + LENGTH bs <= a \/ a + LENGTH cs <= d) ==>
  mm_local_pending cap (FILTER P js ++ FILTER (\j. ~P j) js) s t
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >>
  drule mm_local_capture_log_canonical >> strip_tac >> gvs[] >>
  qexists `MAP (THE o cap) (FILTER P js ++ FILTER (\j. ~P j) js)` >>
  conj_tac
  >- (simp[LIST_REL_MAP2] >> irule EVERY2_refl >>
      gvs[EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
      `IS_SOME (cap x)` by metis_tac[] >>
      Cases_on `cap x` >> gvs[]) >>
  `FOLDL (\st j. write_memory_with_expansion
      (FST (THE (cap j))) (SND (THE (cap j))) st) t js =
    FOLDL (\st j. write_memory_with_expansion
      (FST (THE (cap j))) (SND (THE (cap j))) st)
      (FOLDL (\st j. write_memory_with_expansion
        (FST (THE (cap j))) (SND (THE (cap j))) st) t (FILTER P js))
      (FILTER (\j. ~P j) js)` by
    (irule (SRULE [combinTheory.o_DEF]
      (Q.INST [`wr` |-> `THE o cap`] mm_local_write_log_partition)) >>
      rpt strip_tac >>
      `IS_SOME (cap j) /\ IS_SOME (cap k)` by gvs[EVERY_MEM, MEM_APPEND] >>
      Cases_on `cap j` >> Cases_on `cap k` >> gvs[] >>
      PairCases_on `x` >> PairCases_on `x'` >> gvs[] >> metis_tac[]) >>
  gvs[FOLDL_MAP, FOLDL_APPEND, pairTheory.UNCURRY, combinTheory.o_DEF]
QED

Theorem mm_local_pending_discharge_filter[local]:
  mm_local_pending cap js s t /\
  (!pre j mid k post d bs a cs.
    js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k /\
    cap j = SOME (d,bs) /\ cap k = SOME (a,cs) ==>
    d + LENGTH bs <= a \/ a + LENGTH cs <= d) /\
  LIST_REL (\j w. cap j = SOME w) (FILTER P js) old /\
  LIST_REL (\j w. cap j = SOME w) (FILTER (\j. ~P j) js) rest /\
  (!v. write_memory_with_expansion d payload
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st) v old) =
    write_memory_with_expansion dst merged v) /\
  EVERY (\(a,bs). a + LENGTH bs <= d \/ d + LENGTH payload <= a) rest /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion dst merged t).vs_memory ==>
  mm_local_pending cap (FILTER (\j. ~P j) js) s' t'
Proof
  strip_tac >>
  `mm_local_pending cap (FILTER P js ++ FILTER (\j. ~P j) js) s t` by
    (irule mm_local_pending_partition >> simp[] >> metis_tac[]) >>
  drule_all mm_local_pending_discharge_prefix >> simp[]
QED

Theorem mm_local_pending_compatible_partition[local]:
  mm_local_pending cap js s t /\
  (!pre j mid k post d bs a cs.
    js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k /\
    cap j = SOME (d,bs) /\ cap k = SOME (a,cs) ==>
    mm_local_write_compatible d bs a cs) ==>
  mm_local_pending cap (FILTER P js ++ FILTER (\j. ~P j) js) s t
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >>
  drule mm_local_capture_log_canonical >> strip_tac >> gvs[] >>
  qexists `MAP (THE o cap) (FILTER P js ++ FILTER (\j. ~P j) js)` >>
  conj_tac
  >- (simp[LIST_REL_MAP2] >> irule EVERY2_refl >>
      gvs[EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
      `IS_SOME (cap x)` by metis_tac[] >>
      Cases_on `cap x` >> gvs[]) >>
  `FOLDL (\st j. write_memory_with_expansion
      (FST (THE (cap j))) (SND (THE (cap j))) st) t js =
    FOLDL (\st j. write_memory_with_expansion
      (FST (THE (cap j))) (SND (THE (cap j))) st)
      (FOLDL (\st j. write_memory_with_expansion
        (FST (THE (cap j))) (SND (THE (cap j))) st) t (FILTER P js))
      (FILTER (\j. ~P j) js)` by
    (irule (SRULE [combinTheory.o_DEF]
      (Q.INST [`wr` |-> `THE o cap`] mm_local_write_log_compatible_partition)) >>
      rpt strip_tac >>
      `IS_SOME (cap j) /\ IS_SOME (cap k)` by gvs[EVERY_MEM, MEM_APPEND] >>
      Cases_on `cap j` >> Cases_on `cap k` >> gvs[] >>
      PairCases_on `x` >> PairCases_on `x'` >> gvs[] >> metis_tac[]) >>
  gvs[FOLDL_MAP, FOLDL_APPEND, pairTheory.UNCURRY, combinTheory.o_DEF]
QED

Theorem mm_local_pending_compatible_discharge_prefix[local]:
  mm_local_pending cap (done ++ keep) s t /\
  LIST_REL (\j w. cap j = SOME w) done old /\
  LIST_REL (\j w. cap j = SOME w) keep rest /\
  (!v. write_memory_with_expansion d payload
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st) v old) =
    write_memory_with_expansion dst merged v) /\
  EVERY (\(a,bs). mm_local_write_compatible a bs d payload) rest /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion dst merged t).vs_memory ==>
  mm_local_pending cap keep s' t'
Proof
  strip_tac >>
  `LIST_REL (\j w. cap j = SOME w) (done ++ keep) (old ++ rest)` by
    (irule rich_listTheory.EVERY2_APPEND_suff >> simp[]) >>
  drule_all mm_local_pending_log >> simp[FOLDL_APPEND] >> strip_tac >>
  drule mm_local_write_log_compatible_commute >>
  disch_then (qspec_then
    `FOLDL (\st (a,bs). write_memory_with_expansion a bs st) t old` mp_tac) >>
  simp[] >> strip_tac >>
  `s'.vs_memory =
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st)
      (write_memory_with_expansion dst merged t) rest).vs_memory` by
    (qpat_x_assum `write_memory_with_expansion _ _ _ = _`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[write_as_replace]) >>
  simp[mm_local_pending_def] >> qexists `rest` >> simp[] >>
  metis_tac[mm_local_write_log_memory_cong]
QED

Theorem mm_local_pending_compatible_discharge_filter[local]:
  mm_local_pending cap js s t /\
  (!pre j mid k post d bs a cs.
    js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k /\
    cap j = SOME (d,bs) /\ cap k = SOME (a,cs) ==>
    mm_local_write_compatible d bs a cs) /\
  LIST_REL (\j w. cap j = SOME w) (FILTER P js) old /\
  LIST_REL (\j w. cap j = SOME w) (FILTER (\j. ~P j) js) rest /\
  (!v. write_memory_with_expansion d payload
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st) v old) =
    write_memory_with_expansion dst merged v) /\
  EVERY (\(a,bs). mm_local_write_compatible a bs d payload) rest /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion dst merged t).vs_memory ==>
  mm_local_pending cap (FILTER (\j. ~P j) js) s' t'
Proof
  strip_tac >>
  `mm_local_pending cap (FILTER P js ++ FILTER (\j. ~P j) js) s t` by
    (irule mm_local_pending_compatible_partition >> simp[] >> metis_tac[]) >>
  drule_all mm_local_pending_compatible_discharge_prefix >> simp[]
QED

Theorem mm_local_pending_copy_birth[local]:
  mm_local_pending cap js s t /\
  LIST_REL (\j w. cap j = SOME w) js ws /\
  EVERY (\(d,bs). len = 0 \/ bs = [] \/ src+len <= d \/ d+LENGTH bs <= src) ws /\
  payload = read_memory src len s /\ cap n = SOME (dst,payload) /\
  s'.vs_memory = (write_memory_with_expansion dst payload s).vs_memory ==>
  payload = read_memory src len t /\ LENGTH payload = len /\
  mm_local_pending cap (js ++ [n]) s' t
Proof
  strip_tac >>
  `payload = read_memory src len t` by
    (drule_all mm_local_pending_log >> strip_tac >>
     drule_all mm_local_read_write_log_memory >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[mm_local_read_memory_bytes] >>
  irule mm_local_pending_create >> metis_tac[]
QED

Theorem mm_local_pending_mcopy_birth[local]:
  mm_local_pending cap js s t /\
  LIST_REL (\j w. cap j = SOME w) js ws /\
  EVERY (\(d,bs). src+len <= d \/ d+LENGTH bs <= src) ws /\
  payload = read_memory src len s /\ cap n = SOME (dst,payload) ==>
  payload = read_memory src len t /\ LENGTH payload = len /\
  mm_local_pending cap (js ++ [n]) (mcopy dst src len s) t
Proof
  strip_tac >> irule mm_local_pending_copy_birth >>
  conj_tac >- (qexists `ws` >> simp[] >>
    gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  qexistsl [`dst`, `s`] >>
  simp[venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]
QED

Definition mm_local_group_captures_def:
  mm_local_group_captures is cap B g <=>
    !j d bs. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      cap j = SOME (d,bs) ==>
      g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
      bs = mm_local_bytes B (g.cg_src + (d-g.cg_dst)) (LENGTH bs)
End

Theorem mm_local_group_captures_empty[local]:
  mm_local_group_captures is (\j. NONE) B g
Proof
  simp[mm_local_group_captures_def]
QED

Theorem mm_local_group_captures_birth[local]:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  g.cg_inst_ids = [(EL j is).inst_id] /\
  cap j = SOME (g.cg_dst, mm_local_bytes B g.cg_src g.cg_length) ==>
  mm_local_group_captures is cap B g
Proof
  simp[mm_local_group_captures_def] >> rpt strip_tac >>
  `j' = j` by
    (metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]) >> gvs[]
QED

Theorem mm_local_group_captures_merge[local]:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 /\
  mm_local_group_captures is cap B c1 /\ mm_local_group_captures is cap B c2 ==>
  mm_local_group_captures is cap B (copy_merge c1 c2)
Proof
  simp[mm_local_group_captures_def, copy_merge_def, copy_can_merge_def] >>
  rpt strip_tac >>
  `MAX (c1.cg_dst + c1.cg_length) (c2.cg_dst + c2.cg_length) >=
     c1.cg_dst + c1.cg_length /\
   MAX (c1.cg_dst + c1.cg_length) (c2.cg_dst + c2.cg_length) >=
     c2.cg_dst + c2.cg_length` by simp[arithmeticTheory.MAX_DEF] >>
  `!d. c2.cg_dst <= d ==>
    c1.cg_src + (d-c1.cg_dst) = c2.cg_src + (d-c2.cg_dst)` by decide_tac >>
  res_tac >> fs[] >> gvs[] >> decide_tac
QED

Theorem mm_local_group_captures_rebase[local]:
  mm_local_group_captures is cap B g /\
  mm_local_bytes B g.cg_src g.cg_length = mm_local_bytes C g.cg_src g.cg_length ==>
  mm_local_group_captures is cap C g
Proof
  simp[mm_local_group_captures_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
   bs = mm_local_bytes B (g.cg_src + (d-g.cg_dst)) (LENGTH bs)` by metis_tac[] >>
  simp[] >>
  `d-g.cg_dst + LENGTH bs <= g.cg_length` by decide_tac >>
  `mm_local_bytes B (g.cg_src + (d-g.cg_dst)) (LENGTH bs) =
   TAKE (LENGTH bs) (DROP (d-g.cg_dst) (mm_local_bytes B g.cg_src g.cg_length))` by
    (irule mm_local_bytes_restrict >> simp[]) >>
  `mm_local_bytes C (g.cg_src + (d-g.cg_dst)) (LENGTH bs) =
   TAKE (LENGTH bs) (DROP (d-g.cg_dst) (mm_local_bytes C g.cg_src g.cg_length))` by
    (irule mm_local_bytes_restrict >> simp[]) >>
  gvs[]
QED

Theorem mm_local_merge_adjacent_captures[local]:
  !cs. SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
    EVERY (mm_local_group_captures is cap B) cs ==>
    EVERY (mm_local_group_captures is cap B) (merge_adjacent cs)
Proof
  recInduct merge_adjacent_ind >> simp[merge_adjacent_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `copy_can_merge c1 c2`
  >- (gvs[] >> first_x_assum irule >> conj_tac
      >- (gvs[sortingTheory.SORTED_EQ, relationTheory.transitive_def,
              copy_merge_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      simp[] >> irule mm_local_group_captures_merge >>
      gvs[sortingTheory.SORTED_DEF]) >>
  gvs[] >> first_x_assum irule >> gvs[sortingTheory.SORTED_DEF]
QED

Theorem mm_local_add_copy_captures[local]:
  SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
  EVERY (mm_local_group_captures is cap B) cs /\ mm_local_group_captures is cap B c ==>
  EVERY (mm_local_group_captures is cap B) (add_copy cs c)
Proof
  strip_tac >> simp[add_copy_def] >> irule mm_local_merge_adjacent_captures >>
  metis_tac[mm_local_insert_sorted_order, mm_local_insert_every]
QED

Theorem mm_local_bulk_capture_birth[local]:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  i = EL j is /\ i.inst_opcode = MCOPY /\
  i.inst_operands = [Lit dst; Lit src; Lit len] /\ step_inst_base i s = OK t /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [i.inst_id] |> /\
  hs = flush_hazards Mem2Mem
    (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c /\
  cap' = (\q. if q = j then SOME (w2n dst, read_memory (w2n src) (w2n len) s)
             else cap q) /\
  mm_local_bytes B (w2n src) (w2n len) = read_memory (w2n src) (w2n len) s ==>
  scan_bulk_copy Mem2Mem ss i = hs with ss_copies := add_copy hs.ss_copies c /\
  t.vs_memory = (write_memory_with_expansion (w2n dst)
    (read_memory (w2n src) (w2n len) s) s).vs_memory /\
  cap' j = SOME (w2n dst, read_memory (w2n src) (w2n len) s) /\
  mm_local_group_captures is cap' B c
Proof
  strip_tac >> conj_tac
  >- gvs[scan_bulk_copy_def, mode_allows_overlap_def, operand_lit_val_def] >>
  conj_tac
  >- (irule mm_local_capture_copy >>
      qexistsl [`ARB`, `0`, `i`] >>
      gvs[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  conj_tac >- simp[] >>
  irule mm_local_group_captures_birth >> conj_tac >- simp[] >>
  qexists `j` >> gvs[]
QED

Theorem mm_local_store_capture_birth[local]:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  i = EL j is /\ i.inst_opcode = MSTORE /\ i.inst_operands = [Lit dst; Var v] /\
  FLOOKUP ss.ss_loads v = SOME src /\ lookup_var v s = SOME (mload src s) /\
  step_inst_base i s = OK t /\
  lids = (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) /\
  ~MEM i.inst_id lids /\
  (!q. q < LENGTH is /\ MEM (EL q is).inst_id lids ==> cap q = NONE) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [i.inst_id] ++ lids |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) 32)) c /\
  cap' = (\q. if q = j then SOME (w2n dst, read_memory src 32 s) else cap q) /\
  mm_local_bytes B src 32 = read_memory src 32 s ==>
  scan_store dfg Mem2Mem ss i = hs with ss_copies := add_copy hs.ss_copies c /\
  t.vs_memory = (write_memory_with_expansion (w2n dst) (read_memory src 32 s) s).vs_memory /\
  cap' j = SOME (w2n dst, read_memory src 32 s) /\
  mm_local_group_captures is cap' B c
Proof
  strip_tac >> conj_tac
  >- gvs[scan_store_def, mode_allows_overlap_def, operand_lit_val_def,
         operand_var_name_def] >>
  conj_tac
  >- (irule mm_local_capture_store >> qexistsl [`ARB`, `0`, `i`, `v`] >>
      gvs[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  conj_tac >- simp[] >>
  pure_rewrite_tac[mm_local_group_captures_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `j' = j` >- gvs[] >>
  `~((EL j' is).inst_id = i.inst_id)` by
    metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
  gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem mm_local_group_captures_extend[local]:
  j < LENGTH is /\ ~MEM (EL j is).inst_id g.cg_inst_ids /\
  mm_local_group_captures is cap B g /\
  cap' = (\q. if q = j then SOME (d,bs) else cap q) ==>
  mm_local_group_captures is cap' B g
Proof
  pure_rewrite_tac[mm_local_group_captures_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `j' = j` >> gvs[] >> metis_tac[]
QED

Theorem mm_local_hazards_partition[local]:
  MEM h ss.ss_copies ==>
  MEM h (flush_hazards Mem2Mem ss c).ss_copies \/
  MEM h (flush_hazards Mem2Mem ss c).ss_flushed
Proof
  simp[flush_hazards_def, mode_allows_overlap_def] >>
  rpt IF_CASES_TAC >>
  gvs[flush_copies_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_hazards_source_exclusion[local]:
  MEM h (flush_hazards Mem2Mem ss c).ss_copies ==>
  ~copy_overwrites h (copy_src_interval c)
Proof
  simp[flush_hazards_def, mode_allows_overlap_def] >>
  rpt IF_CASES_TAC >>
  gvs[flush_copies_def, raw_hazards_def, copies_that_overwrite_def, MEM_FILTER] >>
  rpt strip_tac >> gvs[FILTER_EQ_NIL, EVERY_MEM, MEM_FILTER]
QED

Theorem mm_local_hazards_capture_source_exclusion[local]:
  MEM c1 (flush_hazards Mem2Mem ss c2).ss_copies /\
  LENGTH bs = c1.cg_length ==>
  c2.cg_length = 0 \/ bs = [] \/
  c2.cg_src + c2.cg_length <= c1.cg_dst \/
  c1.cg_dst + LENGTH bs <= c2.cg_src
Proof
  strip_tac >> drule mm_local_hazards_source_exclusion >>
  simp[copy_overwrites_def, copy_dst_interval_def, copy_src_interval_def,
       mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
       mmIntervalTheory.interval_end_def,
       arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `bs = []` >> gvs[] >>
  `0 < LENGTH bs` by (Cases_on `bs` >> gvs[]) >> decide_tac
QED

Theorem mm_local_prefix_future_hazard[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  bb.bb_instructions = pre ++ i::post /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state pre /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss iv) c /\
  (scan_inst (dfg_build_function fn0) Mem2Mem ss i).ss_flushed = hs.ss_flushed /\
  MEM w pre /\ w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM h ss.ss_copies /\ MEM w.inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM w.inst_id g.cg_inst_ids /\ rep_of_group bb.bb_instructions g = SOME (r,g) /\
  ~MEM r (MAP (\i. i.inst_id) pre) ==>
  MEM h hs.ss_copies /\ ~copy_overwrites h (copy_src_interval c)
Proof
  strip_tac >>
  `MEM h hs.ss_copies \/ MEM h hs.ss_flushed` by
    (gvs[] >> irule mm_local_hazards_partition >> simp[invalidate_loads_def]) >>
  `MEM h hs.ss_copies` by
    (spose_not_then assume_tac >> fs[] >>
     `MEM h (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by
       (qspecl_then [`post`, `scan_inst (dfg_build_function fn0) Mem2Mem ss i`]
          strip_assume_tac (Q.INST [`dfg` |-> `dfg_build_function fn0`,
            `mode` |-> `Mem2Mem`] mm_local_fold_flushed_extension) >>
        gvs[scan_block_def, FOLDL_APPEND, hard_barrier_def, MEM_APPEND]) >>
     `h = g` by
       (irule mm_local_prefix_write_group_owner >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM_APPEND]) >>
     `MEM r h.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
     `MEM r (MAP (\i. i.inst_id) pre)` by
       (irule mm_local_prefix_fragment_ids_before_cut >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[APPEND_ASSOC]) >>
     metis_tac[]) >>
  simp[] >> gvs[] >> metis_tac[mm_local_hazards_source_exclusion]
QED

Theorem mm_local_prefix_bulk_future_hazard[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  bb.bb_instructions = pre ++ i::post /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state pre /\
  i.inst_opcode = MCOPY /\ i.inst_operands = [Lit dst; Lit src; Lit len] /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [i.inst_id] |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c /\
  MEM w pre /\ w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM h ss.ss_copies /\ MEM w.inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM w.inst_id g.cg_inst_ids /\ rep_of_group bb.bb_instructions g = SOME (r,g) /\
  ~MEM r (MAP (\i. i.inst_id) pre) ==>
  MEM h hs.ss_copies /\ ~copy_overwrites h (copy_src_interval c)
Proof
  strip_tac >>
  `(scan_inst (dfg_build_function fn0) Mem2Mem ss i).ss_flushed = hs.ss_flushed` by
    simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def,
      scan_bulk_copy_def, operand_lit_val_def, mode_allows_overlap_def] >>
  drule_all mm_local_prefix_future_hazard >> simp[]
QED

Theorem mm_local_prefix_store_future_hazard[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  bb.bb_instructions = pre ++ i::post /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state pre /\
  i.inst_opcode = MSTORE /\ i.inst_operands = [Lit dst; Var v] /\
  FLOOKUP ss.ss_loads v = SOME src /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [i.inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of
              SOME li => [li.inst_id] | NONE => []) |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) 32)) c /\
  MEM w pre /\ w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM h ss.ss_copies /\ MEM w.inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM w.inst_id g.cg_inst_ids /\ rep_of_group bb.bb_instructions g = SOME (r,g) /\
  ~MEM r (MAP (\i. i.inst_id) pre) ==>
  MEM h hs.ss_copies /\ ~copy_overwrites h (copy_src_interval c)
Proof
  strip_tac >>
  `(scan_inst (dfg_build_function fn0) Mem2Mem ss i).ss_flushed = hs.ss_flushed` by
    (simp[scan_inst_def, mode_load_opcode_def, scan_store_def,
      operand_lit_val_def, operand_var_name_def, mode_allows_overlap_def] >> gvs[]) >>
  drule_all mm_local_prefix_future_hazard >> simp[]
QED

Theorem mm_local_future_id_not_prefix[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) is) /\ n <= r /\ r < LENGTH is ==>
  ~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))
Proof
  strip_tac >> disch_then (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
  qpat_x_assum `MEM _ (TAKE n is)`
    (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `q < LENGTH (TAKE n is)` >>
  `q < LENGTH is /\ q < n` by gvs[] >>
  `EL q (TAKE n is) = EL q is` by simp[EL_TAKE] >>
  `q = r` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
  decide_tac
QED

Theorem mm_local_prefix_wf_id_distinct[local]:
  wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  strip_tac >> irule mm_local_prefix_id_distinct >>
  qexistsl [`fn0`, `index`, `k`, `sk`, `supply`] >> simp[] >> conj_tac
  >- (fs[wf_function_def] >>
      metis_tac[mmWfProofsTheory.fn_inst_ids_distinct_block, EL_MEM]) >>
  fs[ir_supply_covers_fn_def, irSupplyTheory.fn_ir_inst_ids_def,
     irSupplyTheory.block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  metis_tac[EL_MEM, MEM_MAP]
QED

Theorem mm_local_indexed_future_hazard[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\ j < n /\
  n <= r /\ r < LENGTH is /\ i = EL n is /\ w = EL j is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss iv) c /\
  (scan_inst (dfg_build_function fn0) Mem2Mem ss i).ss_flushed = hs.ss_flushed /\
  w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM h ss.ss_copies /\ MEM w.inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM w.inst_id g.cg_inst_ids /\ rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  MEM h hs.ss_copies /\ ~copy_overwrites h (copy_src_interval c)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `MEM w (TAKE n is)` by
    (pure_rewrite_tac[MEM_EL] >> qexists_tac `j` >> gvs[EL_TAKE, LENGTH_TAKE]) >>
  `~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule mm_local_future_id_not_prefix >> simp[]) >>
  `bb.bb_instructions = TAKE n is ++ i::DROP (SUC n) is` by
    (qspec_then `n` (qspec_then `is` mp_tac) rich_listTheory.TAKE_DROP_SUC >> simp[]) >>
  `rep_of_group bb.bb_instructions g = SOME ((EL r is).inst_id,g)` by metis_tac[] >>
  drule_all mm_local_prefix_future_hazard >> simp[]
QED

Theorem mm_local_capture_source_exclusion[local]:
  ~copy_overwrites h (copy_src_interval c) /\
  h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length ==>
  LENGTH bs = 0 \/ c.cg_length = 0 \/
  c.cg_src + c.cg_length <= d \/ d + LENGTH bs <= c.cg_src
Proof
  Cases_on `bs` >- simp[] >>
  simp[copy_overwrites_def, copy_dst_interval_def, copy_src_interval_def,
    mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
    mmIntervalTheory.interval_end_def, arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem mm_local_bulk_cut_fragment[local]:
  j < n /\ n <= LENGTH is /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  ss = FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE n is) /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id] |> ==>
  ?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor c h
Proof
  strip_tac >>
  qabbrev_tac `s0 = FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE j is)` >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst) s0.ss_copies` by
    (simp[Abbr `s0`] >> irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  `?a. MEM a (scan_bulk_copy Mem2Mem s0 (EL j is)).ss_copies /\
    mm_local_copy_ancestor c a` by
    (irule mm_local_bulk_new_fragment >> simp[operand_lit_val_def] >> metis_tac[]) >>
  `scan_inst dfg Mem2Mem s0 (EL j is) = scan_bulk_copy Mem2Mem s0 (EL j is)` by
    simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  `TAKE n is = (TAKE j is ++ [EL j is]) ++ TAKE (n-SUC j) (DROP (SUC j) is)` by
    (qspec_then `n` (qspec_then `SUC j` (qspec_then `is` mp_tac))
       rich_listTheory.take_drop_partition >>
     simp[rich_listTheory.TAKE_SUC, rich_listTheory.DROP_EL_CONS]) >>
  `ss = FOLDL (scan_inst dfg Mem2Mem)
    (scan_inst dfg Mem2Mem s0 (EL j is)) (TAKE (n-SUC j) (DROP (SUC j) is))` by
    simp[Abbr `s0`, FOLDL_APPEND] >>
  `?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor a h` by
    (qpat_assum `ss = _` SUBST1_TAC >> irule mm_local_fold_fragment >>
     simp[MEM_APPEND] >> metis_tac[mm_local_inst_order]) >>
  metis_tac[mm_local_copy_ancestor_trans]
QED

Theorem mm_local_store_cut_fragment[local]:
  j < n /\ n <= LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  s0 = FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads v = SOME src /\
  ss = FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE n is) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) |> ==>
  ?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor c h
Proof
  strip_tac >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst) s0.ss_copies` by
    (simp[] >> irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  `?a. MEM a (scan_store dfg Mem2Mem s0 (EL j is)).ss_copies /\
    mm_local_copy_ancestor c a` by
    (irule mm_local_store_new_fragment >> simp[operand_lit_val_def, operand_var_name_def] >>
     metis_tac[]) >>
  `scan_inst dfg Mem2Mem s0 (EL j is) = scan_store dfg Mem2Mem s0 (EL j is)` by
    simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  `TAKE n is = (TAKE j is ++ [EL j is]) ++ TAKE (n-SUC j) (DROP (SUC j) is)` by
    (qspec_then `n` (qspec_then `SUC j` (qspec_then `is` mp_tac))
       rich_listTheory.take_drop_partition >>
     simp[rich_listTheory.TAKE_SUC, rich_listTheory.DROP_EL_CONS]) >>
  `ss = FOLDL (scan_inst dfg Mem2Mem)
    (scan_inst dfg Mem2Mem s0 (EL j is)) (TAKE (n-SUC j) (DROP (SUC j) is))` by
    (simp[FOLDL_APPEND] >> gvs[]) >>
  `?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor a h` by
    (qpat_assum `ss = _` SUBST1_TAC >> irule mm_local_fold_fragment >>
     simp[MEM_APPEND] >> metis_tac[mm_local_inst_order]) >>
  metis_tac[mm_local_copy_ancestor_trans]
QED

Theorem mm_local_indexed_bulk_owner[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  j < n /\ n <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    h.cg_dst <= w2n dst /\ w2n dst + w2n len <= h.cg_dst + h.cg_length
Proof
  strip_tac >>
  `?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\
    mm_local_copy_ancestor
      <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id] |> h` by
    (irule mm_local_bulk_cut_fragment >> simp[] >>
     qexistsl [`dfg_build_function fn0`, `is`, `j`, `n`] >> simp[] >> gvs[]) >>
  `MEM (EL j is).inst_id h.cg_inst_ids /\ h.cg_dst <= w2n dst /\
    w2n dst + w2n len <= h.cg_dst + h.cg_length` by
    gvs[mm_local_copy_ancestor_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule mm_local_future_id_not_prefix >> simp[]) >>
  `bb.bb_instructions = TAKE n is ++ DROP n is` by simp[] >>
  `MEM (EL j is) bb.bb_instructions` by
    (gvs[] >> irule EL_MEM >> decide_tac) >>
  `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by simp[] >>
  `rep_of_group bb.bb_instructions g = SOME ((EL r is).inst_id,g)` by metis_tac[] >>
  `MEM h ss.ss_copies` by
    (drule_all (REWRITE_RULE [] (Q.INST [`w` |-> `EL j is`]
       (SPEC_ALL mm_local_prefix_write_pending_ancestor))) >>
     disch_then (assume_tac o CONJUNCT1) >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem mm_local_indexed_store_owner[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  j < n /\ n <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads v = SOME src /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    h.cg_dst <= w2n dst /\ w2n dst + 32 <= h.cg_dst + h.cg_length
Proof
  strip_tac >>
  `n <= LENGTH is` by decide_tac >>
  drule_all (REWRITE_RULE [] (Q.INST
    [`dfg` |-> `dfg_build_function fn0`,
     `c` |-> `<| cg_dst := w2n dst; cg_src := src; cg_length := 32;
      cg_inst_ids := [(EL j is).inst_id] ++
        (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id]) |>`]
    (SPEC_ALL mm_local_store_cut_fragment))) >> strip_tac >>
  `MEM (EL j is).inst_id h.cg_inst_ids /\ h.cg_dst <= w2n dst /\
    w2n dst + 32 <= h.cg_dst + h.cg_length` by
    (gvs[mm_local_copy_ancestor_def] >> metis_tac[MEM_APPEND, MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule mm_local_future_id_not_prefix >> simp[]) >>
  `bb.bb_instructions = TAKE n is ++ DROP n is` by simp[] >>
  `MEM (EL j is) bb.bb_instructions` by
    (gvs[] >> irule EL_MEM >> decide_tac) >>
  `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by simp[] >>
  `rep_of_group bb.bb_instructions g = SOME ((EL r is).inst_id,g)` by metis_tac[] >>
  drule_all (REWRITE_RULE [] (Q.INST [`w` |-> `EL j is`]
    (SPEC_ALL mm_local_prefix_write_pending_ancestor))) >> strip_tac >>
  metis_tac[]
QED

Theorem mm_local_history_store_value[local]:
  mm_local_history is H N /\ j < N /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] ==>
  ?value. lookup_var v (H j) = SOME value
Proof
  strip_tac >>
  `step_inst_base (EL j is) (H j) = OK (H (SUC j))` by
    metis_tac[mm_local_history_def] >>
  gvs[venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_write2_def,
      venomStateTheory.eval_operand_def, AllCaseEqs()]
QED

Theorem mm_local_indexed_store_history_owner[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  j < n /\ n <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads v = SOME src /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_history is H N /\ n <= N ==>
  ?h d bs. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    mm_local_write_capture is H N j = SOME (d,bs) /\
    d = w2n dst /\ LENGTH bs = 32 /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length
Proof
  strip_tac >>
  drule_all mm_local_indexed_store_owner >> strip_tac >>
  `j < N` by decide_tac >>
  drule_all mm_local_history_store_value >> strip_tac >>
  drule_all mm_local_write_capture_store >> strip_tac >>
  qexistsl [`h`, `w2n dst`, `word_to_bytes value T`] >> asm_rewrite_tac[]
QED

Theorem mm_local_indexed_bulk_history_owner[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  j < n /\ n <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  mm_local_history is H N /\ n <= N ==>
  ?h d bs. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    mm_local_write_capture is H N j = SOME (d,bs) /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length
Proof
  strip_tac >>
  drule_all mm_local_indexed_bulk_owner >> strip_tac >>
  `j < N` by decide_tac >>
  drule_all mm_local_write_capture_copy >> strip_tac >>
  qexistsl [`h`, `w2n dst`, `read_memory (w2n src) (w2n len) (H j)`] >>
  asm_rewrite_tac[]
QED

Theorem mm_local_indexed_bulk_pending_birth[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ mm_local_history is H (SUC n) /\ n < LENGTH is /\
  (EL n is).inst_opcode = MCOPY /\
  (EL n is).inst_operands = [Lit dst; Lit src; Lit len] /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL n is).inst_id] |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) (w2n len))) c /\
  mm_local_pending (mm_local_write_capture is H (SUC n)) js (H n) t /\
  (!j. MEM j js ==> j < n /\ ?h g r d bs.
    mm_local_write_capture is H (SUC n) j = SOME (d,bs) /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n <= r /\ r < LENGTH is /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length) ==>
  read_memory (w2n src) (w2n len) (H n) = read_memory (w2n src) (w2n len) t /\
  mm_local_pending (mm_local_write_capture is H (SUC n)) (js ++ [n]) (H (SUC n)) t
Proof
  strip_tac >>
  `(scan_inst (dfg_build_function fn0) Mem2Mem ss (EL n is)).ss_flushed = hs.ss_flushed` by
    simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def,
      scan_bulk_copy_def, operand_lit_val_def, mode_allows_overlap_def] >>
  `!j d bs. MEM j js /\ mm_local_write_capture is H (SUC n) j = SOME (d,bs) ==>
    w2n len = 0 \/ bs = [] \/ w2n src + w2n len <= d \/ d + LENGTH bs <= w2n src` by
    (rpt strip_tac >>
     qpat_x_assum `!j. MEM j js ==> _` (qspec_then `j` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     `~copy_overwrites h (copy_src_interval c)` by
       (drule_all (REWRITE_RULE [] (Q.INST [`i` |-> `EL n is`, `w` |-> `EL j is`]
          (SPEC_ALL mm_local_indexed_future_hazard))) >> simp[]) >>
     drule (INST_TYPE [alpha |-> ``:word8``] mm_local_capture_source_exclusion) >>
     disch_then (qspecl_then [`d`, `bs`] mp_tac) >> gvs[] >> metis_tac[]) >>
  `mm_local_write_capture is H (SUC n) n =
    SOME (w2n dst,read_memory (w2n src) (w2n len) (H n)) /\
    LENGTH (read_memory (w2n src) (w2n len) (H n)) = w2n len` by
    (irule mm_local_write_capture_copy >> simp[]) >>
  ` (H (SUC n)).vs_memory =
    (write_memory_with_expansion (w2n dst)
      (read_memory (w2n src) (w2n len) (H n)) (H n)).vs_memory` by
    (drule_all mm_local_write_capture_sound >> simp[]) >>
  qpat_assum `mm_local_pending _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_def]) >>
  `EVERY (\(d,bs). w2n len = 0 \/ bs = [] \/
    w2n src + w2n len <= d \/ d + LENGTH bs <= w2n src) ws` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP_R >> strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[mm_local_pending_copy_birth]
QED

Theorem mm_local_mload_bytes[local]:
  word_to_bytes (mload src s) T = read_memory src 32 s
Proof
  simp[venomStateTheory.mload_def, venomStateTheory.read_memory_def] >>
  irule venomMemPropsTheory.word_bytes_roundtrip_256 >> simp[LENGTH_TAKE_EQ]
QED

Theorem mm_local_indexed_store_pending_birth[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ mm_local_history is H (SUC n) /\ n < LENGTH is /\
  (EL n is).inst_opcode = MSTORE /\ (EL n is).inst_operands = [Lit dst; Var v] /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  FLOOKUP ss.ss_loads v = SOME src /\ lookup_var v (H n) = SOME (mload src (H n)) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL n is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of NONE => [] | SOME li => [li.inst_id]) |> /\
  hs = flush_hazards Mem2Mem (invalidate_loads ss (mk_interval (w2n dst) 32)) c /\
  mm_local_pending (mm_local_write_capture is H (SUC n)) js (H n) t /\
  (!j. MEM j js ==> j < n /\ ?h g r d bs.
    mm_local_write_capture is H (SUC n) j = SOME (d,bs) /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n <= r /\ r < LENGTH is /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length) ==>
  read_memory src 32 (H n) = read_memory src 32 t /\
  mm_local_pending (mm_local_write_capture is H (SUC n)) (js ++ [n]) (H (SUC n)) t
Proof
  strip_tac >>
  `(scan_inst (dfg_build_function fn0) Mem2Mem ss (EL n is)).ss_flushed = hs.ss_flushed` by
    (simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def,
      scan_store_def, operand_lit_val_def, operand_var_name_def,
      mode_allows_overlap_def] >> gvs[]) >>
  `!j d bs. MEM j js /\ mm_local_write_capture is H (SUC n) j = SOME (d,bs) ==>
    bs = [] \/ src + 32 <= d \/ d + LENGTH bs <= src` by
    (rpt strip_tac >>
     qpat_x_assum `!j. MEM j js ==> _` (qspec_then `j` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     `~copy_overwrites h (copy_src_interval c)` by
       (drule_all (REWRITE_RULE [] (Q.INST [`i` |-> `EL n is`, `w` |-> `EL j is`]
          (SPEC_ALL mm_local_indexed_future_hazard))) >> simp[]) >>
     drule (INST_TYPE [alpha |-> ``:word8``] mm_local_capture_source_exclusion) >>
     disch_then (qspecl_then [`d`, `bs`] mp_tac) >> gvs[] >> metis_tac[]) >>
  `mm_local_write_capture is H (SUC n) n =
    SOME (w2n dst,read_memory src 32 (H n))` by
    (`n < SUC n` by simp[] >>
     drule_all mm_local_write_capture_store >> simp[mm_local_mload_bytes]) >>
  `(H (SUC n)).vs_memory =
    (write_memory_with_expansion (w2n dst) (read_memory src 32 (H n)) (H n)).vs_memory` by
    (drule_all mm_local_write_capture_sound >> simp[]) >>
  qpat_assum `mm_local_pending _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mm_local_pending_def]) >>
  `EVERY (\(d,bs). bs = [] \/ src + 32 <= d \/ d + LENGTH bs <= src) ws` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP_R >> strip_tac >> gvs[] >> metis_tac[]) >>
  `EVERY (\(d,bs). 32 = 0 \/ bs = [] \/ src + 32 <= d \/ d + LENGTH bs <= src) ws` by
    simp[] >>
  conj_tac >-
    (irule mm_local_read_write_log_memory >> qexists `ws` >> simp[]) >>
  irule mm_local_pending_create >>
  qexistsl [`read_memory src 32 (H n)`, `w2n dst`, `H n`] >>
  simp[]
QED

Theorem mm_local_indexed_store_pending_post_phis[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ mm_local_history is H (SUC n) /\ n < LENGTH is /\
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
  mm_local_pending (mm_local_write_capture is H (SUC n)) js (H n) t /\
  (!j. MEM j js ==> j < n /\ ?h g r d bs.
    mm_local_write_capture is H (SUC n) j = SOME (d,bs) /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
    MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g) /\ n <= r /\ r < LENGTH is /\
    h.cg_dst <= d /\ d + LENGTH bs <= h.cg_dst + h.cg_length) ==>
  read_memory src 32 (H n) = read_memory src 32 t /\
  mm_local_pending (mm_local_write_capture is H (SUC n)) (js ++ [n]) (H (SUC n)) t
Proof
  strip_tac >>
  `n <= LENGTH bb.bb_instructions` by (gvs[] >> decide_tac) >>
  `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state
      (TAKE n bb.bb_instructions)` by metis_tac[] >>
  `lookup_var v (H n) = SOME (mload src (H n))` by
    (drule_all (Q.INST [`j` |-> `n`] (SPEC_ALL mm_local_live_load_post_phis)) >>
     simp[]) >>
  drule_all mm_local_indexed_store_pending_birth >> simp[]
QED

Definition mm_local_pending_indices_def:
  mm_local_pending_indices is gs n = FILTER (\j.
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    ?g r. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      r < LENGTH is /\ n <= r /\
      rep_of_group is g = SOME ((EL r is).inst_id,g)) (COUNT_LIST n)
End

Theorem mm_local_pending_indices_mem[local]:
  MEM j (mm_local_pending_indices is gs n) <=>
  j < n /\ (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  ?g r. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    r < LENGTH is /\ n <= r /\ rep_of_group is g = SOME ((EL r is).inst_id,g)
Proof
  simp[mm_local_pending_indices_def, MEM_FILTER, MEM_COUNT_LIST] >> metis_tac[]
QED

Theorem mm_local_pending_indices_order[local]:
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
      simp[scan_store_def, operand_var_name_def, operand_lit_val_def,
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

Theorem mm_local_inst_birth_every[local]:
  (!a b. P a /\ P b ==> P (copy_merge a b)) /\
  mm_local_scan_every P ss /\
  (inst.inst_opcode = MSTORE ==>
    !dst v src. inst.inst_operands = [Lit dst; Var v] /\ FLOOKUP ss.ss_loads v = SOME src ==>
      P <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
        cg_inst_ids := inst.inst_id ::
          (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) |>) /\
  (inst.inst_opcode = MCOPY ==>
    !dst src len. inst.inst_operands = [Lit dst; Lit src; Lit len] ==>
      P <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
        cg_inst_ids := [inst.inst_id] |>) ==>
  mm_local_scan_every P (scan_inst dfg Mem2Mem ss inst)
Proof
  strip_tac >> simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  IF_CASES_TAC >- (irule mm_local_load_every >> simp[]) >>
  IF_CASES_TAC >- (irule mm_local_store_birth_every >> metis_tac[]) >>
  IF_CASES_TAC >- (irule mm_local_bulk_birth_every >> metis_tac[]) >>
  rpt IF_CASES_TAC >> simp[mm_local_barrier_every]
QED

Definition mm_local_id_birth_def:
  mm_local_id_birth dfg is id <=> ?p. p < LENGTH is /\
    ((?dst src len. (EL p is).inst_opcode = MCOPY /\
       (EL p is).inst_operands = [Lit dst; Lit src; Lit len] /\ id = (EL p is).inst_id) \/
     (?dst v src. (EL p is).inst_opcode = MSTORE /\
       (EL p is).inst_operands = [Lit dst; Var v] /\
       FLOOKUP (FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE p is)).ss_loads v = SOME src /\
       (id = (EL p is).inst_id \/ ?li. dfg_get_def dfg v = SOME li /\ id = li.inst_id)))
End

Theorem mm_local_birth_merge[local]:
  (!id. MEM id a.cg_inst_ids ==> mm_local_id_birth dfg is id) /\
  (!id. MEM id b.cg_inst_ids ==> mm_local_id_birth dfg is id) ==>
  !id. MEM id (copy_merge a b).cg_inst_ids ==> mm_local_id_birth dfg is id
Proof
  simp[copy_merge_def, MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_scan_births[local]:
  !t. t <= LENGTH is ==>
    mm_local_scan_every (\g. !id. MEM id g.cg_inst_ids ==> mm_local_id_birth dfg is id)
      (FOLDL (scan_inst dfg Mem2Mem) empty_scan_state (TAKE t is))
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

Theorem mm_local_final_write_birth[local]:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\ is = bb.bb_instructions /\
  j < LENGTH is /\ MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} ==>
  (?dst src len. (EL j is).inst_opcode = MCOPY /\
    (EL j is).inst_operands = [Lit dst; Lit src; Lit len]) \/
  (?dst v src. (EL j is).inst_opcode = MSTORE /\
    (EL j is).inst_operands = [Lit dst; Var v] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `mm_local_scan_every
    (\g. !id. MEM id g.cg_inst_ids ==> mm_local_id_birth (dfg_build_function fn0) is id)
    (scan_block (dfg_build_function fn0) Mem2Mem bb)` by
    (simp[scan_block_def] >> irule mm_local_barrier_every >>
     mp_tac (Q.SPEC `LENGTH (bb.bb_instructions)`
       (Q.INST [`dfg` |-> `dfg_build_function fn0`, `is` |-> `bb.bb_instructions`]
         mm_local_scan_births)) >> simp[]) >>
  `mm_local_id_birth (dfg_build_function fn0) is (EL j is).inst_id` by
    (gnvs[mm_local_scan_every_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `mm_local_id_birth _ _ _`
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
  simp[mode_load_opcode_def]
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
  drule_all mm_local_final_write_birth >> strip_tac
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

Theorem mm_local_write_rep_unique[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
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
     qexistsl [`bb`, `fn0`, `index`, `k`, `Mem2Mem`, `sk`, `supply`, `EL j is`] >>
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

Theorem mm_local_rep_index_eq[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
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

Theorem mm_local_canonical_pending_keep[local]:
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

Theorem mm_local_canonical_rep_write[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  n < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL n is).inst_id,g) ==>
  (EL n is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `MEM (EL n is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `ALOOKUP (rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed)
    (EL n is).inst_id = SOME g` by
    (qpat_x_assum `is = _` SUBST_ALL_TAC >>
     qpat_x_assum `gs = _` SUBST_ALL_TAC >>
     drule_all mm_local_prefix_selected_rep >> simp[]) >>
  drule_all mm_local_prefix_rep_write >> simp[]
QED

Theorem mm_local_canonical_due_group[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
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
         qexistsl [`bb`, `fn0`, `index`, `k`, `Mem2Mem`, `sk`, `supply`, `EL n is`] >>
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

Theorem mm_local_canonical_rep_capture[local]:
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
  drule_all mm_local_final_write_birth >> strip_tac
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
  irule mm_local_read_write_disjoint >>
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

Theorem mm_local_group_coverage_merge[local]:
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

Theorem mm_local_zero_capture_past[local]:
  j < n /\ n <= m ==>
  mm_local_zero_capture dfg is m j = mm_local_zero_capture dfg is n j
Proof
  simp[mm_local_zero_capture_def]
QED

Theorem mm_local_zero_capture_cases[local]:
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
      gvs[oneline operand_lit_val_def, oneline operand_var_name_def, AllCaseEqs()] >>
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

Theorem mm_local_zero_representative_certificate[local]:
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

Theorem mm_local_zero_capture_sound[local]:
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

(* Essential counterexample evidence: a variable-free unreachable block. *)
Theorem mm_local_dead_input:
  fn0 = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []] |>;
     <| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 MSTORE [Lit 0w; Lit 0w] [];
        mk_inst 2 MSTORE [Lit 32w; Lit 0w] [];
        mk_inst 3 STOP [] []] |>] /\
  supply = <| irs_next_inst := 4; irs_next_var := 0; irs_next_label := 0;
              irs_used_inst_ids := [0;1;2;3]; irs_used_vars := [];
              irs_used_labels := ["f";"entry";"dead"] |> ==>
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\
  ir_supply_covers_fn supply fn0 /\ 1 < LENGTH fn0.fn_blocks
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem mm_local_dead_transform:
  transform_block_memzero_supply (dfg_build_function (mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []] |>;
     <| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 MSTORE [Lit 0w; Lit 0w] [];
        mk_inst 2 MSTORE [Lit 32w; Lit 0w] [];
        mk_inst 3 STOP [] []] |>]))
    <| irs_next_inst := 4; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0;1;2;3]; irs_used_vars := [];
       irs_used_labels := ["f";"entry";"dead"] |>
    <| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 MSTORE [Lit 0w; Lit 0w] [];
        mk_inst 2 MSTORE [Lit 32w; Lit 0w] [];
        mk_inst 3 STOP [] []] |> =
  (<| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 NOP [] [];
        mk_inst 4 CALLDATASIZE [] ["formal_var_0"];
        mk_inst 2 CALLDATACOPY [Lit 0w; Var "formal_var_0"; Lit 64w] [];
        mk_inst 3 STOP [] []] |>,
   <| irs_next_inst := 5; irs_next_var := 1; irs_next_label := 0;
      irs_used_inst_ids := [4;0;1;2;3]; irs_used_vars := ["formal_var_0"];
      irs_used_labels := ["f";"entry";"dead"] |>)
Proof
  EVAL_TAC
QED

Theorem mm_local_dead_not_ssa:
  ~wf_ssa (mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []] |>;
     <| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 NOP [] [];
        mk_inst 4 CALLDATASIZE [] ["formal_var_0"];
        mk_inst 2 CALLDATACOPY [Lit 0w; Var "formal_var_0"; Lit 64w] [];
        mk_inst 3 STOP [] []] |>])
Proof
  simp[wf_ssa_def, def_dominates_uses_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def, def_available_at_def, fn_dominates_def] >>
  disj2_tac >>
  qexistsl [`<| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 NOP [] [];
        mk_inst 4 CALLDATASIZE [] ["formal_var_0"];
        mk_inst 2 CALLDATACOPY [Lit 0w; Var "formal_var_0"; Lit 64w] [];
        mk_inst 3 STOP [] []] |>`,
    `mk_inst 2 CALLDATACOPY [Lit 0w; Var "formal_var_0"; Lit 64w] []`] >>
  simp[venomInstTheory.mk_inst_def, fn_reachable_def] >>
  once_rewrite_tac[relationTheory.RTC_CASES1] >>
  simp[fn_cfg_edge_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
       EXISTS_OR_THM, venomInstTheory.bb_succs_def,
       venomInstTheory.mk_inst_def] >> EVAL_TAC >> simp[]
QED

(* All outer premises of the frozen theorem, at index=1 and k=0,
   are realizable, but its unconditional SSA conclusion is false. *)
Theorem mm_local_stage_counterexample:
  fn0 = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []] |>;
     <| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 MSTORE [Lit 0w; Lit 0w] [];
        mk_inst 2 MSTORE [Lit 32w; Lit 0w] [];
        mk_inst 3 STOP [] []] |>] /\
  supply = <| irs_next_inst := 4; irs_next_var := 0; irs_next_label := 0;
              irs_used_inst_ids := [0;1;2;3]; irs_used_vars := [];
              irs_used_labels := ["f";"entry";"dead"] |> ==>
  ?bb sk fn bb' sk' fn'.
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\
  ir_supply_covers_fn supply fn0 /\ 1 < LENGTH fn0.fn_blocks /\ 0 < 4 /\
  FOLDL (\(b,t) phase. case phase of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) t b
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m t b)
    (EL 1 fn0.fn_blocks,supply)
    (TAKE 0 [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb 1 fn0.fn_blocks /\
  (case EL 0 [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) sk bb
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m sk bb) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' 1 fn0.fn_blocks /\
  ~wf_ssa fn'
Proof
  strip_tac >> drule mm_local_dead_input >> strip_tac >>
  simp[] >>
  qexistsl [`<| bb_label := "dead"; bb_instructions :=
       [mk_inst 1 NOP [] [];
        mk_inst 4 CALLDATASIZE [] ["formal_var_0"];
        mk_inst 2 CALLDATACOPY [Lit 0w; Var "formal_var_0"; Lit 64w] [];
        mk_inst 3 STOP [] []] |>`,
   `<| irs_next_inst := 5; irs_next_var := 1; irs_next_label := 0;
      irs_used_inst_ids := [4;0;1;2;3]; irs_used_vars := ["formal_var_0"];
      irs_used_labels := ["f";"entry";"dead"] |>`] >>
  gvs[] >> mp_tac mm_local_dead_transform >>
  mp_tac mm_local_dead_not_ssa >>
  simp[venomInstTheory.mk_raw_function_def, listTheory.LUPDATE_DEF] >>
  rpt strip_tac >> gvs[]
QED

Theorem mm_local_trace_step_every[local]:
  reachability_closed Inv ctx ==>
  EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
    (trace_step [] d fuel ctx fn inst s)
Proof
  strip_tac >> drule (cj 1 mm_trace_root_inv) >>
  disch_then (qspecl_then [`[]`, `d`, `fuel`, `fn`, `inst`, `s`] mp_tac) >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

(* Arbitrary predicates: retain the exact execution guards on trace tails. *)
Theorem mm_local_trace_visit_every[local]:
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  (EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_block [] d fuel ctx fn bb s) <=>
   P fn inst s /\
   EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_step [] d fuel ctx fn inst s) /\
   (case step_inst fuel ctx inst s of
      OK u => is_terminator inst.inst_opcode \/
        EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
          (trace_block [] d fuel ctx fn bb
            (u with vs_inst_idx := SUC s.vs_inst_idx))
    | _ => T))
Proof
  strip_tac >> drule trace_block_visit >> disch_then (fn th => once_rewrite_tac[th]) >>
  simp[EVERY_APPEND] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
QED

Theorem mm_local_trace_visit_root_every[local]:
  reachability_closed Inv ctx /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  (EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_block [] d fuel ctx fn bb s) <=>
   P fn inst s /\
   (case step_inst fuel ctx inst s of
      OK u => is_terminator inst.inst_opcode \/
        EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
          (trace_block [] d fuel ctx fn bb
            (u with vs_inst_idx := SUC s.vs_inst_idx))
    | _ => T))
Proof
  strip_tac >>
  `EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_step [] d fuel ctx fn inst s)` by
    (irule mm_local_trace_step_every >> metis_tac[]) >>
  drule mm_local_trace_visit_every >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem mm_local_trace_enter_every[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp ==>
  (EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_blocks [] d (SUC fuel) ctx fn s) <=>
   EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_block [] (SUC d) fuel ctx fn bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
   (case exec_block fuel ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
      OK u => u.vs_halted \/
        EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
          (trace_blocks [] (SUC d) fuel ctx fn u)
    | _ => T))
Proof
  strip_tac >> drule_all trace_blocks_enter >> disch_then (fn th => once_rewrite_tac[th]) >>
  simp[EVERY_APPEND] >>
  Cases_on `exec_block fuel ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `OK u` >> Cases_on `u.vs_halted` >> simp[]
QED

Theorem mm_local_trace_function_every[local]:
  EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
    (trace_function fuel ctx fn s) <=>
  (case fn_entry_label fn of
     NONE => T
   | SOME lbl =>
     EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
       (trace_blocks [] 0 fuel ctx fn
         (s with <|vs_current_bb := lbl; vs_inst_idx := 0|>)))
Proof
  Cases_on `fn_entry_label fn` >> simp[trace_function_def]
QED

Theorem mm_local_stage_correct:
  !fn0 supply index k bb sk fn bb' sk' fn'.
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\ all_reachable fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k < 4 /\
  FOLDL (\(b,t) phase. case phase of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) t b
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m t b)
    (EL index fn0.fn_blocks,supply)
    (TAKE k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) = (bb,sk) /\
  fn = fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks /\
  (case EL k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem] of
      NONE => transform_block_memzero_supply (dfg_build_function fn0) sk bb
    | SOME m => transform_block_mode_supply (dfg_build_function fn0) m sk bb) = (bb',sk') /\
  fn' = fn0 with fn_blocks := LUPDATE bb' index fn0.fn_blocks ==>
  fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\ all_reachable fn' /\
  ir_supply_covers_fn sk' fn' /\
  fn_entry_label fn' = fn_entry_label fn0 /\
  (!fuel ctx eom s.
    fn_entry_state fn s /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    eom < dimword (:256) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn s) /\
    ~(?err. run_function fuel ctx fn s = Error err) ==>
    lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
      (run_function fuel ctx fn s) (run_function fuel ctx fn' s) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn' s))
Proof
  cheat
QED
