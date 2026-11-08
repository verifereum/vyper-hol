(* Each local merging phase with its actual original-DFG provenance. *)
Theory mmLocalScanProofs
Ancestors
  mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner
  venomWf stateEquiv rich_list mmTransform mmScan mmCopy list sorting
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
      (?st dst v li. MEM st xs /\ st.inst_opcode = MSTORE /\
        st.inst_operands = [Lit dst; Var v] /\ dfg_get_def dfg v = SOME li /\
        li.inst_id = id /\ MEM st.inst_id cg.cg_inst_ids)
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
  inst.inst_operands = [Lit dst; Var v] ==>
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
      (simp[Abbr `cg`] >> irule mm_local_store_group_roles >> simp[]) >>
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
  MEM inst xs /\ mm_local_scan_every (mm_local_group_roles dfg mode xs) ss ==>
  mm_local_scan_every (mm_local_group_roles dfg mode xs)
    (scan_inst dfg mode ss inst)
Proof
  strip_tac >> simp[scan_inst_def] >>
  rpt IF_CASES_TAC >>
  metis_tac[mm_local_load_every, mm_local_store_roles,
            mm_local_bulk_roles, mm_local_barrier_every]
QED

Theorem mm_local_fold_roles[local]:
  !is ss. EVERY (\i. MEM i xs) is /\
  mm_local_scan_every (mm_local_group_roles dfg mode xs) ss ==>
  mm_local_scan_every (mm_local_group_roles dfg mode xs)
    (FOLDL (scan_inst dfg mode) ss is)
Proof
  Induct_on `is` >> simp[] >> metis_tac[mm_local_inst_roles]
QED

Theorem mm_local_scan_group_roles[local]:
  MEM cg (scan_block dfg mode bb).ss_flushed ==>
  mm_local_group_roles dfg mode bb.bb_instructions cg
Proof
  `mm_local_scan_every (mm_local_group_roles dfg mode bb.bb_instructions)
    (scan_block dfg mode bb)` by
    (simp[scan_block_def] >> irule mm_local_barrier_every >>
     irule mm_local_fold_roles >>
     simp[EVERY_MEM, mm_local_scan_every_def, empty_scan_state_def]) >>
  gvs[mm_local_scan_every_def, EVERY_MEM]
QED

Theorem mm_local_scan_group_roles_elim[local]:
  MEM cg (scan_block dfg mode bb).ss_flushed /\ MEM id cg.cg_inst_ids ==>
  (?st dst v. MEM st bb.bb_instructions /\ st.inst_id = id /\
    st.inst_opcode = MSTORE /\ st.inst_operands = [Lit dst; Var v]) \/
  (?cp dst src len. MEM cp bb.bb_instructions /\ cp.inst_id = id /\
    cp.inst_opcode = mode_copy_opcode mode /\
    cp.inst_operands = [Lit dst; Lit src; Lit len]) \/
  (?st dst v li. MEM st bb.bb_instructions /\ st.inst_opcode = MSTORE /\
    st.inst_operands = [Lit dst; Var v] /\ dfg_get_def dfg v = SOME li /\
    li.inst_id = id /\ MEM st.inst_id cg.cg_inst_ids)
Proof
  strip_tac >> drule mm_local_scan_group_roles >>
  simp[mm_local_group_roles_def]
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

Theorem mm_local_memzero_list_load_origin[local]:
  !xs s ys t i other.
  mm_flat_map_supply (apply_memzero_inst_supply ns rm) s xs = (ys,t) /\
  MEM i ys /\ i.inst_opcode = mode_load_opcode other ==> MEM i xs
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >>
  simp[Once mm_flat_map_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[MEM_APPEND] >- (
    qpat_x_assum `apply_memzero_inst_supply _ _ _ _ = _` mp_tac >>
    simp[apply_memzero_inst_supply_def, AllCaseEqs()] >> strip_tac >>
    Cases_on `other` >>
    gvs[mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def,
        mode_load_opcode_def]) >>
  metis_tac[]
QED

Theorem mm_local_mode_list_load_origin[local]:
  !xs s ys t i other.
  mm_flat_map_supply (apply_groups_inst_supply mode ns rm) s xs = (ys,t) /\
  other <> mode /\ MEM i ys /\ i.inst_opcode = mode_load_opcode other ==>
  MEM i xs
Proof
  Induct_on `xs` >- simp[mm_flat_map_supply_def] >>
  rpt gen_tac >>
  simp[Once mm_flat_map_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[MEM_APPEND] >- (
    qpat_x_assum `apply_groups_inst_supply _ _ _ _ _ = _` mp_tac >>
    simp[apply_groups_inst_supply_def, AllCaseEqs()] >> strip_tac >>
    Cases_on `mode` >> Cases_on `other` >>
    gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
        mk_mstore_from_load_def, mode_load_opcode_def, mode_copy_opcode_def]) >>
  metis_tac[]
QED

Theorem mm_local_phase_other_load_origin[local]:
  mm_local_phase dfg phase (bb,s) = (cc,t) /\ phase <> SOME other /\
  MEM i cc.bb_instructions /\ i.inst_opcode = mode_load_opcode other ==>
  MEM i bb.bb_instructions
Proof
  Cases_on `phase` >>
  simp[mm_local_phase_def, transform_block_memzero_supply_def,
       transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[mm_local_memzero_list_load_origin, mm_local_mode_list_load_origin]
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
        mk_memzero_calldatacopy_def, venomInstTheory.inst_uses_def,
        venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
    `j = 0 \/ j = 1` by decide_tac >>
    gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
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
        venomInstTheory.inst_uses_def, venomInstTheory.operand_vars_def,
        venomInstTheory.operand_var_def] >>
    `j = 0 \/ j = 1` by decide_tac >>
    gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
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

Theorem mm_local_stage_correct:
  !fn0 supply index k bb sk fn bb' sk' fn'.
  fn_inst_wf fn0 /\ wf_function fn0 /\ wf_ssa fn0 /\
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
  fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\
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
