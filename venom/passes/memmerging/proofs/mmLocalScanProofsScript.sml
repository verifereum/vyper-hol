(* Each local merging phase with its actual original-DFG provenance. *)
Theory mmLocalScanProofs
Ancestors
  mmSupplyWfProofs mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner allocaRemapSSA o1MakeSsaCfg makeSsaCurrentWfSsa
  cfgWf venomWf stateEquiv rich_list mmTransform mmScan mmCopy list sorting
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
  strip_tac >>
  `!cg. MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed ==>
    ~MEM q.inst_id cg.cg_inst_ids` by
    metis_tac[mm_local_prefix_nonselected_group_absent] >>
  `~MEM q.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)` by
    (strip_tac >> gvs[nop_ids_of_groups_def, MEM_FLAT, MEM_MAP] >>
     rename1 `MEM cg (scan_block (dfg_build_function fn0) mode bb).ss_flushed` >>
     qpat_x_assum `MEM _ (nop_ids_of_group _ _ _ _)` mp_tac >>
     simp[nop_ids_of_group_def] >>
     Cases_on `REVERSE (sort_ids_by_block bb.bb_instructions cg.cg_inst_ids)` >>
     simp[MEM_FILTER] >> disj2_tac >> strip_tac >>
     `MEM q.inst_id (REVERSE (sort_ids_by_block bb.bb_instructions cg.cg_inst_ids))`
       by (pure_asm_rewrite_tac[MEM] >> simp[]) >>
     gvs[MEM_REVERSE, sort_ids_by_block_def, MEM_FILTER] >> metis_tac[]) >>
  `ALOOKUP (rep_map_of_groups bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed) q.inst_id = NONE` by
    (simp[alistTheory.ALOOKUP_NONE, rep_map_of_groups_def, MEM_MAP, MEM_FILTER] >>
     rpt strip_tac >> spose_not_then strip_assume_tac >>
     rename1 `MEM group (scan_block (dfg_build_function fn0) mode bb).ss_flushed` >>
     Cases_on `rep_of_group bb.bb_instructions group` >> gvs[] >>
     rename1 `rep_of_group bb.bb_instructions group = SOME result` >>
     PairCases_on `result` >> gvs[] >> drule mm_local_rep_member >> strip_tac >>
     metis_tac[]) >>
  simp[apply_groups_inst_supply_def]
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
