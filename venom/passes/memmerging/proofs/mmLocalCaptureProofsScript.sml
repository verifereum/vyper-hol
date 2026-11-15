(* Local memmerging phase: captured bytes and pending-copy histories. *)
Theory mmLocalCaptureProofs
Ancestors
  venomFnInstsProofs venomInst memoryReadRel
  mmSupplyWfProofs mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner allocaRemapSSA o1MakeSsaCfg makeSsaCurrentWfSsa
  cfgWf venomWf stateEquiv rich_list mmTransform mmScan mmCopy list sorting
  simplifyCfgPhiSemantics simplifyCfgFixupStatic basePtrProofs mmTraceProofs frameViewMemory dftCommutation
  regularMemorySim rangeAnalysisProofs dftIndexedExec removeUnusedProofs analysisSimProofsBase
  mmLocalStructureProofs
  venomTransformStructureProps venomWriteReplayProps venomExecutionReplayProps irSupplyFreshProps
Libs
  wordsLib finite_mapLib stepInstBaseLib

Definition mm_local_copy_ancestor_def:
  mm_local_copy_ancestor h g <=>
    (!id. MEM id h.cg_inst_ids ==> MEM id g.cg_inst_ids) /\
    g.cg_dst <= h.cg_dst /\
    h.cg_dst + h.cg_length <= g.cg_dst + g.cg_length /\
    h.cg_src + g.cg_dst = h.cg_dst + g.cg_src
End

Theorem mm_local_copy_ancestor_refl:
  mm_local_copy_ancestor h h
Proof
  simp[mm_local_copy_ancestor_def]
QED

Theorem mm_local_copy_ancestor_trans:
  mm_local_copy_ancestor h g /\ mm_local_copy_ancestor g f ==>
  mm_local_copy_ancestor h f
Proof
  rw[mm_local_copy_ancestor_def]
QED

Theorem mm_local_copy_merge_ancestors:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  mm_local_copy_ancestor c1 (copy_merge c1 c2) /\
  mm_local_copy_ancestor c2 (copy_merge c1 c2)
Proof
  simp[mm_local_copy_ancestor_def, copy_merge_def, copy_can_merge_def,
       MEM_APPEND] >>
  rpt strip_tac >>
  simp[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem mm_local_insert_sorted_mem:
  !cs c h. MEM h (insert_sorted cs c) <=> h = c \/ MEM h cs
Proof
  Induct >> simp[insert_sorted_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem mm_local_insert_sorted_order:
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

Theorem mm_local_add_copy_order:
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

Theorem mm_local_hazards_order:
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

Theorem mm_local_inst_order:
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

Theorem mm_local_fold_order:
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

Theorem mm_local_hazards_flushed_extension:
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

Theorem mm_local_fold_flushed_extension:
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

Theorem mm_local_prefix_final_fragment:
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

Theorem mm_local_store_new_fragment:
  SORTED (\a b. a.cg_dst <= b.cg_dst) ss.ss_copies /\
  inst.inst_operands = [dst_op; val_op] /\
  operand_var val_op = SOME var /\
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

Theorem mm_local_bulk_new_fragment:
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

Theorem mm_local_prefix_cached_def_before_cut:
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

Theorem mm_local_prefix_fragment_ids_before_cut:
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

Theorem mm_local_prefix_rep_write:
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

Theorem mm_local_prefix_write_origin:
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

Theorem mm_local_prefix_write_not_def:
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
    (irule venomFnInstsProofsTheory.MEM_fn_insts >>
     qexists_tac `EL index fn0.fn_blocks` >> simp[EL_MEM]) >>
  `inst_wf u` by
    (gvs[fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  `u.inst_outputs = []` by gvs[inst_wf_def] >>
  strip_tac >> `li = u` by
    (irule venomFnInstsProofsTheory.fn_insts_id_unique >>
     conj_tac >- simp[] >>
     qexists_tac `fn0` >> gvs[wf_function_def]) >> gvs[]
QED

Theorem mm_local_prefix_write_group_owner:
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

Theorem mm_local_cut_selected_ancestor:
  bb.bb_instructions = pre ++ post /\
  ss = FOLDL (scan_inst dfg mode) empty_scan_state pre /\
  (!a b. MEM a (scan_block dfg mode bb).ss_flushed /\
         MEM b (scan_block dfg mode bb).ss_flushed /\
         MEM id a.cg_inst_ids /\ MEM id b.cg_inst_ids ==> a = b) /\
  MEM h (ss.ss_copies ++ ss.ss_flushed) /\ MEM id h.cg_inst_ids /\
  MEM g (scan_block dfg mode bb).ss_flushed /\ MEM id g.cg_inst_ids ==>
  mm_local_copy_ancestor h g
Proof
  strip_tac >>
  `?a. MEM a (scan_block dfg mode bb).ss_flushed /\
       mm_local_copy_ancestor h a` by
    (irule mm_local_prefix_final_fragment >> metis_tac[]) >>
  `MEM id a.cg_inst_ids` by gvs[mm_local_copy_ancestor_def] >>
  metis_tac[]
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
  `mm_local_copy_ancestor h g` by
    (irule mm_local_cut_selected_ancestor >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `?tail. (FOLDL (scan_inst dfg mode) ss post).ss_flushed = ss.ss_flushed ++ tail`
    by metis_tac[mm_local_fold_flushed_extension] >>
  `MEM h ss.ss_flushed ==> MEM h (scan_block dfg mode bb).ss_flushed` by
    (simp[scan_block_def, FOLDL_APPEND, hard_barrier_def] >>
     metis_tac[MEM_APPEND]) >>
  drule mm_local_rep_member >> strip_tac >>
  gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem mm_local_prefix_write_pending_ancestor:
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

Definition mm_local_write_compatible_def:
  mm_local_write_compatible d bs a cs <=>
    !x. d <= x /\ x < d + LENGTH bs /\ a <= x /\ x < a + LENGTH cs ==>
      EL (x-d) bs = EL (x-a) cs
End

Theorem mm_local_write_compatible_sym:
  mm_local_write_compatible d bs a cs <=> mm_local_write_compatible a cs d bs
Proof
  metis_tac[mm_local_write_compatible_def]
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
  simp[expand_replace, venomWriteReplayPropsTheory.expand_mem_max,
       venomStateTheory.venom_state_component_equality] >>
  simp[arithmeticTheory.MAX_COMM] >>
  irule mm_local_replace_compatible_commute >> simp[] >>
  simp[arithmeticTheory.MAX_DEF]
QED

Theorem mm_local_write_log_compatible_commute:
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

Theorem mm_local_load_pending_disjoint:
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

Theorem mm_local_flush_hazards_survivor:
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

Theorem mm_local_flush_hazards_read:
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

Theorem mm_local_live_cut_fresh:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME mode) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  j < LENGTH bb.bb_instructions /\
  FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) mode)
    empty_scan_state (TAKE j bb.bb_instructions)).ss_loads v = SOME src ==>
  ~MEM v (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >> drule mm_local_scan_lookup_origin >> strip_tac >>
  `MEM q bb.bb_instructions` by metis_tac[MEM_TAKE] >>
  `MEM q (EL index fn0.fn_blocks).bb_instructions` by
    (irule mm_local_pending_load_origin >> metis_tac[]) >>
  `MEM q (fn_insts fn0)` by
    (irule venomFnInstsProofsTheory.MEM_fn_insts >>
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

Theorem mm_local_live_load_step:
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
           gvs[hard_barrier_def, operand_var_def, operand_lit_val_def,
               mode_allows_overlap_def]) >>
      rename1 `inst.inst_operands = [dst_op; val_op]` >>
      Cases_on `dst_op` >> Cases_on `val_op` >>
      gvs[operand_lit_val_def, operand_var_def] >>
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

Theorem mm_local_scan_phi_prefix:
  !xs ss. FOLDL (scan_inst dfg mode) ss
    (TAKE (phi_prefix_length xs) xs) = ss
Proof
  Cases_on `mode` >> Induct_on `xs` >> simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rpt gen_tac >> IF_CASES_TAC >>
  simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def,
       is_volatile_memory_def, venomEffectsTheory.read_effects_def,
       venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def,
       venomEffectsTheory.empty_effects_def]
QED

Theorem mm_local_live_load_cut:
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

Theorem mm_local_live_load_post_phis:
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

Theorem mm_local_event_rep_position:
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

Theorem mm_local_prefix_selected_rep:
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

Theorem mm_local_zero_inst_ids[local]:
  MEM id (mm_local_group_ids (scan_inst_memzero dfg mz i).mz_flushed ++
          mm_local_group_ids (scan_inst_memzero dfg mz i).mz_copies) <=>
  MEM id (mm_local_group_ids mz.mz_flushed ++ mm_local_group_ids mz.mz_copies) \/
  (id = i.inst_id /\ (is_zero_store i \/ is_calldatasize_copy dfg i))
Proof
  `!cs cg. MEM id (mm_local_group_ids (add_copy cs cg)) =
    MEM id (cg.cg_inst_ids ++ mm_local_group_ids cs)` by
    metis_tac[mm_local_add_ids_perm, PERM_MEM_EQ] >>
  Cases_on `i.inst_operands`
  >- (simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
      IF_CASES_TAC >> simp[memzero_barrier_def, mm_local_group_ids_append,
        mm_local_group_ids_def]) >>
  rename1 `i.inst_operands = dst::ops` >> Cases_on `ops`
  >- (simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
      IF_CASES_TAC >> simp[memzero_barrier_def, mm_local_group_ids_append,
        mm_local_group_ids_def]) >>
  rename1 `i.inst_operands = dst::src::ops` >> Cases_on `ops`
  >- (simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
      Cases_on `operand_lit_val dst` >> simp[] >>
      rpt IF_CASES_TAC >> gvs[memzero_barrier_def, mm_local_group_ids_append,
        copy_memzero_def, mm_local_group_ids_def] >> metis_tac[]) >>
  rename1 `i.inst_operands = dst::src::len::ops` >> Cases_on `ops` >>
  simp[scan_inst_memzero_def, is_zero_store_def, is_calldatasize_copy_def] >>
  Cases_on `operand_lit_val dst` >> Cases_on `operand_lit_val len` >> simp[] >>
  rpt IF_CASES_TAC >> gvs[memzero_barrier_def, mm_local_group_ids_append,
    copy_memzero_def, mm_local_group_ids_def] >> metis_tac[]
QED

Theorem mm_local_zero_fold_ids[local]:
  !xs mz. MEM id
    (mm_local_group_ids (FOLDL (scan_inst_memzero dfg) mz xs).mz_flushed ++
     mm_local_group_ids (FOLDL (scan_inst_memzero dfg) mz xs).mz_copies) <=>
    MEM id (mm_local_group_ids mz.mz_flushed ++ mm_local_group_ids mz.mz_copies) \/
    ?i. MEM i xs /\ id = i.inst_id /\
      (is_zero_store i \/ is_calldatasize_copy dfg i)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  pure_rewrite_tac[FOLDL] >>
  first_x_assum (qspec_then `scan_inst_memzero dfg mz h` SUBST1_TAC) >>
  pure_rewrite_tac[mm_local_zero_inst_ids] >> simp[] >> metis_tac[]
QED

Theorem mm_local_zero_selected_member:
  MEM i bb.bb_instructions /\
  (is_zero_store i \/ is_calldatasize_copy dfg i) ==>
  ?g. MEM g (scan_block_memzero dfg bb).mz_flushed /\ MEM i.inst_id g.cg_inst_ids
Proof
  strip_tac >>
  `MEM i.inst_id (mm_local_group_ids (scan_block_memzero dfg bb).mz_flushed)` by
    (mp_tac (Q.SPECL [`bb.bb_instructions`,`empty_memzero_state`]
       (Q.INST [`id` |-> `i.inst_id`] mm_local_zero_fold_ids)) >>
     simp[scan_block_memzero_def, memzero_barrier_def, mm_local_group_ids_append,
       empty_memzero_state_def, mm_local_group_ids_def] >> metis_tac[]) >>
  gvs[mm_local_group_ids_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
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

Theorem mm_local_zero_scan_unique:
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

Theorem mm_local_zero_selected_rep:
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

Theorem mm_local_write_capture_past:
  j < n /\ n <= m ==>
  mm_local_write_capture is H n j = mm_local_write_capture is H m j
Proof
  simp[mm_local_write_capture_def]
QED

Theorem mm_local_write_capture_future:
  n <= j ==> mm_local_write_capture is H n j = NONE
Proof
  simp[mm_local_write_capture_def]
QED

Theorem mm_local_write_capture_sound:
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

Theorem mm_local_write_capture_copy_bounds:
  j < n /\ j < LENGTH is /\
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

Theorem mm_local_write_capture_copy:
  j < n /\ mm_local_history is H n /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] ==>
  mm_local_write_capture is H n j =
    SOME (w2n dst,read_memory (w2n src) (w2n len) (H j)) /\
  LENGTH (read_memory (w2n src) (w2n len) (H j)) = w2n len
Proof
  strip_tac >> irule mm_local_write_capture_copy_bounds >>
  gvs[mm_local_history_def]
QED

Theorem mm_local_write_capture_store_bounds:
  j < n /\ j < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\ lookup_var v (H j) = SOME value ==>
  mm_local_write_capture is H n j = SOME (w2n dst,word_to_bytes value T) /\
  LENGTH (word_to_bytes value T) = 32
Proof
  simp[mm_local_history_def, mm_local_write_capture_def,
       venomStateTheory.eval_operand_def] >> rpt strip_tac >> simp[]
QED

Theorem mm_local_write_capture_store:
  j < n /\ mm_local_history is H n /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\ lookup_var v (H j) = SOME value ==>
  mm_local_write_capture is H n j = SOME (w2n dst,word_to_bytes value T) /\
  LENGTH (word_to_bytes value T) = 32
Proof
  strip_tac >> irule mm_local_write_capture_store_bounds >>
  gvs[mm_local_history_def]
QED

Theorem mm_local_history_noncapture_frame[local]:
  mm_local_history is H n /\ q < n /\
  ((EL q is).inst_opcode = MSTORE \/ (EL q is).inst_opcode = MCOPY \/
   ~(Eff_MEMORY IN write_effects (EL q is).inst_opcode)) /\
  mm_local_write_capture is H n q = NONE ==>
  (H (SUC q)).vs_memory = (H q).vs_memory
Proof
  strip_tac >>
  `q < LENGTH is /\ step_inst_base (EL q is) (H q) = OK (H (SUC q))` by
    gvs[mm_local_history_def] >>
  all_tac
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[venomExecSemanticsTheory.step_inst_base_def,
           venomExecSemanticsTheory.exec_write2_def] >>
      rpt (BasicProvers.PURE_CASE_TAC >> simp[]) >>
      gvs[mm_local_write_capture_def])
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[venomExecSemanticsTheory.step_inst_base_def,
           venomExecSemanticsTheory.mcopy_def] >>
      rpt (BasicProvers.PURE_CASE_TAC >> simp[]) >>
      gvs[mm_local_write_capture_def]) >>
  Cases_on `is_alloca_op (EL q is).inst_opcode`
  >- (irule venomMemPropsTheory.step_inst_alloca_preserves_memory >>
      qexistsl [`ARB`, `0`, `EL q is`] >>
      Cases_on `(EL q is).inst_opcode` >>
      gvs[venomInstTheory.is_alloca_op_def,
          venomExecSemanticsTheory.step_inst_def]) >>
  Cases_on `is_terminator (EL q is).inst_opcode`
  >- (Cases_on `(EL q is).inst_opcode` >>
      gvs[venomInstTheory.is_terminator_def,
          venomEffectsTheory.write_effects_def, venomEffectsTheory.empty_effects_def] >>
      qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      with_opcode_clause (fn ths =>
        simp (ths @ [venomStateTheory.jump_to_def, venomStateTheory.halt_state_def,
           venomStateTheory.revert_state_def, venomStateTheory.set_returndata_def])) >>
      rpt (BasicProvers.PURE_CASE_TAC >>
           simp[venomStateTheory.jump_to_def, venomStateTheory.halt_state_def,
                venomStateTheory.revert_state_def, venomStateTheory.set_returndata_def]) >>
      disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  irule venomInstProofs3Theory.step_inst_base_preserves_memory >> metis_tac[]
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

Theorem mm_local_pending_empty:
  mm_local_pending cap [] s t <=> s.vs_memory = t.vs_memory
Proof
  simp[mm_local_pending_def]
QED

Theorem mm_local_pending_log:
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

Theorem mm_local_pending_create:
  mm_local_pending cap js s t /\ cap n = SOME (d,bs) /\
  s'.vs_memory = (write_memory_with_expansion d bs s).vs_memory ==>
  mm_local_pending cap (js ++ [n]) s' t
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >>
  qexists `ws ++ [(d,bs)]` >>
  simp[LIST_REL_APPEND, FOLDL_APPEND, write_as_replace]
QED

Theorem mm_local_snapshot_copy[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [Lit dst; Lit src; Lit len] /\
  step_inst fuel ctx inst s = OK t /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
          cg_inst_ids := [inst.inst_id] |> /\
  MEM g (flush_hazards Mem2Mem ss c).ss_copies ==>
  read_memory g.cg_src g.cg_length t = read_memory g.cg_src g.cg_length s
Proof
  strip_tac >> drule_all venomWriteReplayPropsTheory.capture_copy >> strip_tac >>
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
  strip_tac >> drule_all venomWriteReplayPropsTheory.capture_store >> strip_tac >>
  drule mm_local_flush_hazards_read >>
  disch_then (qspecl_then [`s`, `read_memory src 32 s`] mp_tac) >>
  gvs[venomStateTheory.read_memory_def, LENGTH_TAKE, LENGTH_DROP]
QED

Theorem mm_local_snapshot_copy_base:
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

Theorem mm_local_snapshot_store_base:
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

Definition mm_local_bytes_def:
  mm_local_bytes (B:num -> word8) a n = GENLIST (\i. B (a+i)) n
End

Theorem mm_local_bytes_length[simp]:
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

Theorem mm_local_bytes_write_merge:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  write_memory_with_expansion c2.cg_dst (mm_local_bytes B c2.cg_src c2.cg_length)
    (write_memory_with_expansion c1.cg_dst (mm_local_bytes B c1.cg_src c1.cg_length) s) =
  write_memory_with_expansion (copy_merge c1 c2).cg_dst
    (mm_local_bytes B (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length) s
Proof
  strip_tac >> drule_all mm_local_bytes_merge_compat >>
  disch_then (qspec_then `B` strip_assume_tac) >>
  simpLib.SIMP_TAC (srw_ss()) [copy_merge_def] >>
  irule venomWriteReplayPropsTheory.payload_write_merge >>
  pure_rewrite_tac[mm_local_bytes_length] >> gvs[copy_merge_def]
QED

Theorem mm_local_bytes_write_merge_reverse:
  c1.cg_dst <= c2.cg_dst /\ copy_can_merge c1 c2 ==>
  write_memory_with_expansion c1.cg_dst (mm_local_bytes B c1.cg_src c1.cg_length)
    (write_memory_with_expansion c2.cg_dst (mm_local_bytes B c2.cg_src c2.cg_length) s) =
  write_memory_with_expansion (copy_merge c1 c2).cg_dst
    (mm_local_bytes B (copy_merge c1 c2).cg_src (copy_merge c1 c2).cg_length) s
Proof
  strip_tac >> drule_all mm_local_bytes_merge_compat >>
  disch_then (qspec_then `B` strip_assume_tac) >>
  simpLib.SIMP_TAC (srw_ss()) [copy_merge_def] >>
  irule venomWriteReplayPropsTheory.payload_write_merge_reverse >>
  pure_rewrite_tac[mm_local_bytes_length] >> gvs[copy_merge_def]
QED

Theorem mm_local_read_memory_bytes:
  read_memory a n s =
  mm_local_bytes (\i. if i < LENGTH s.vs_memory then EL i s.vs_memory else 0w) a n
Proof
  simp[venomStateTheory.read_memory_def, mm_local_bytes_def,
       memoryReadRelTheory.venom_returndata_read_byte, codegenRelTheory.read_byte_def]
QED

Theorem mm_local_write_log_compatible_partition:
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

Theorem mm_local_pending_compatible_partition[local]:
  mm_local_pending cap js s t /\
  (!pre j mid k post d bs a cs.
    js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k /\
    cap j = SOME (d,bs) /\ cap k = SOME (a,cs) ==>
    mm_local_write_compatible d bs a cs) ==>
  mm_local_pending cap (FILTER P js ++ FILTER (\j. ~P j) js) s t
Proof
  simp[mm_local_pending_def] >> rpt strip_tac >>
  drule venomWriteReplayPropsTheory.capture_log_canonical >> strip_tac >> gvs[] >>
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
  metis_tac[venomWriteReplayPropsTheory.write_log_memory_cong]
QED

Theorem mm_local_pending_compatible_discharge_filter:
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
     drule_all venomWriteReplayPropsTheory.read_write_log_memory >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[mm_local_read_memory_bytes] >>
  irule mm_local_pending_create >> metis_tac[]
QED

Definition mm_local_group_captures_def:
  mm_local_group_captures is cap B g <=>
    !j d bs. j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
      cap j = SOME (d,bs) ==>
      g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
      bs = mm_local_bytes B (g.cg_src + (d-g.cg_dst)) (LENGTH bs)
End

Theorem mm_local_group_captures_birth:
  j < LENGTH is /\ ALL_DISTINCT (MAP (\i. i.inst_id) is) /\
  g.cg_inst_ids = [(EL j is).inst_id] /\
  cap j = SOME (g.cg_dst, mm_local_bytes B g.cg_src g.cg_length) ==>
  mm_local_group_captures is cap B g
Proof
  simp[mm_local_group_captures_def] >> rpt strip_tac >>
  `j' = j` by
    (metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx]) >> gvs[]
QED

Theorem mm_local_group_captures_merge:
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

Theorem mm_local_group_captures_rebase:
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

Theorem mm_local_add_copy_captures:
  SORTED (\a b. a.cg_dst <= b.cg_dst) cs /\
  EVERY (mm_local_group_captures is cap B) cs /\ mm_local_group_captures is cap B c ==>
  EVERY (mm_local_group_captures is cap B) (add_copy cs c)
Proof
  strip_tac >> simp[add_copy_def] >> irule mm_local_merge_adjacent_captures >>
  metis_tac[mm_local_insert_sorted_order, mm_local_insert_every]
QED

Theorem mm_local_bulk_capture_birth:
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
  >- (irule venomWriteReplayPropsTheory.capture_copy >>
      qexistsl [`ARB`, `0`, `i`] >>
      gvs[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  conj_tac >- simp[] >>
  irule mm_local_group_captures_birth >> conj_tac >- simp[] >>
  qexists `j` >> gvs[]
QED

Theorem mm_local_store_capture_birth:
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
         operand_var_def] >>
  conj_tac
  >- (irule venomWriteReplayPropsTheory.capture_store >> qexistsl [`ARB`, `0`, `i`, `v`] >>
      gvs[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  conj_tac >- simp[] >>
  pure_rewrite_tac[mm_local_group_captures_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `j' = j` >- gvs[] >>
  `~((EL j' is).inst_id = i.inst_id)` by
    metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
  gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem mm_local_group_captures_extend:
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
  MEM h (flush_hazards mode ss c).ss_copies \/
  MEM h (flush_hazards mode ss c).ss_flushed
Proof
  simp[flush_hazards_def, mode_allows_overlap_def] >>
  rpt IF_CASES_TAC >>
  gvs[flush_copies_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem mm_local_hazards_source_exclusion:
  MEM h (flush_hazards Mem2Mem ss c).ss_copies ==>
  ~copy_overwrites h (copy_src_interval c)
Proof
  simp[flush_hazards_def, mode_allows_overlap_def] >>
  rpt IF_CASES_TAC >>
  gvs[flush_copies_def, raw_hazards_def, copies_that_overwrite_def, MEM_FILTER] >>
  rpt strip_tac >> gvs[FILTER_EQ_NIL, EVERY_MEM, MEM_FILTER]
QED

Theorem mm_local_prefix_future_survivor[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  bb.bb_instructions = pre ++ i::post /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state pre /\
  hs = flush_hazards mode (invalidate_loads ss iv) c /\
  (scan_inst (dfg_build_function fn0) mode ss i).ss_flushed = hs.ss_flushed /\
  MEM w pre /\ w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM h ss.ss_copies /\ MEM w.inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM w.inst_id g.cg_inst_ids /\ rep_of_group bb.bb_instructions g = SOME (r,g) /\
  ~MEM r (MAP (\i. i.inst_id) pre) ==>
  MEM h hs.ss_copies
Proof
  strip_tac >>
  `MEM h hs.ss_copies \/ MEM h hs.ss_flushed` by
    (gvs[] >> irule mm_local_hazards_partition >> simp[invalidate_loads_def]) >>
  spose_not_then assume_tac >> fs[] >>
  `MEM h (scan_block (dfg_build_function fn0) mode bb).ss_flushed` by
    (qspecl_then [`post`, `scan_inst (dfg_build_function fn0) mode ss i`]
       strip_assume_tac (Q.INST [`dfg` |-> `dfg_build_function fn0`]
         mm_local_fold_flushed_extension) >>
     gvs[scan_block_def, FOLDL_APPEND, hard_barrier_def, MEM_APPEND]) >>
  `h = g` by
    (irule mm_local_prefix_write_group_owner >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM_APPEND]) >>
  `MEM r h.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `MEM r (MAP (\i. i.inst_id) pre)` by
    (irule mm_local_prefix_fragment_ids_before_cut >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[APPEND_ASSOC]) >>
  metis_tac[]
QED

Theorem mm_local_prefix_wf_id_distinct:
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

Theorem mm_local_indexed_future_survivor:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n < LENGTH is /\ j < n /\
  n <= r /\ r < LENGTH is /\ i = EL n is /\ w = EL j is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE n is) /\
  hs = flush_hazards mode (invalidate_loads ss iv) c /\
  (scan_inst (dfg_build_function fn0) mode ss i).ss_flushed = hs.ss_flushed /\
  w.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM h ss.ss_copies /\ MEM w.inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM w.inst_id g.cg_inst_ids /\ rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  MEM h hs.ss_copies
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `MEM w (TAKE n is)` by
    (pure_rewrite_tac[MEM_EL] >> qexists_tac `j` >> gvs[EL_TAKE, LENGTH_TAKE]) >>
  `~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule venomTransformStructurePropsTheory.future_id_not_prefix >> simp[]) >>
  `bb.bb_instructions = TAKE n is ++ i::DROP (SUC n) is` by
    (qspec_then `n` (qspec_then `is` mp_tac) rich_listTheory.TAKE_DROP_SUC >> simp[]) >>
  `rep_of_group bb.bb_instructions g = SOME ((EL r is).inst_id,g)` by metis_tac[] >>
  drule_all mm_local_prefix_future_survivor >> simp[]
QED

Theorem mm_local_indexed_future_hazard:
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
  `MEM h hs.ss_copies` by (drule_all mm_local_indexed_future_survivor >> simp[]) >>
  simp[] >> gvs[] >> metis_tac[mm_local_hazards_source_exclusion]
QED

Theorem mm_local_capture_source_exclusion:
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

Theorem mm_local_scan_step_war_exclusion:
  q < n /\ q < LENGTH is /\ i = EL q is /\
  MEM h ss.ss_copies /\ ~MEM h (scan_inst dfg Mem2Mem ss i).ss_flushed /\
  mm_local_write_capture is H n q = SOME (d,bs) ==>
  h.cg_length = 0 \/ LENGTH bs = 0 \/
  h.cg_src + h.cg_length <= d \/ d + LENGTH bs <= h.cg_src
Proof
  strip_tac >>
  qpat_x_assum `mm_local_write_capture _ _ _ _ = _` mp_tac >>
  simp[mm_local_write_capture_def] >>
  Cases_on `i.inst_opcode = MSTORE`
  >- (gvs[] >> simp[AllCaseEqs()] >> strip_tac >>
      qpat_x_assum `~MEM h _` mp_tac >>
      simp[scan_inst_def, mode_load_opcode_def, scan_store_def] >>
      rpt BasicProvers.TOP_CASE_TAC >>
      gvs[hard_barrier_def, MEM_APPEND, mode_allows_overlap_def] >>
      strip_tac >> Cases_on `a` >>
      gvs[operand_lit_val_def, venomStateTheory.eval_operand_def] >>
      qmatch_asmsub_abbrev_tac `~MEM h hs.ss_flushed` >>
      `MEM h hs.ss_copies` by
        (simp[Abbr `hs`] >>
         metis_tac[mm_local_hazards_partition, invalidate_loads_def,
                   scan_state_accfupds]) >>
      pop_assum mp_tac >> simp[Abbr `hs`] >>
      disch_then (mp_tac o MATCH_MP mm_local_flush_hazards_survivor) >>
      simp[copy_overwrites_def, copy_dst_interval_def, copy_src_interval_def,
           mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
           mmIntervalTheory.interval_end_def,
           arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
      rpt strip_tac >> gvs[] >> decide_tac) >>
  Cases_on `i.inst_opcode = MCOPY` >> gvs[] >>
  simp[AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `~MEM h _` mp_tac >>
  simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def, scan_bulk_copy_def] >>
  rpt BasicProvers.TOP_CASE_TAC >>
  gvs[hard_barrier_def, MEM_APPEND, mode_allows_overlap_def] >>
  strip_tac >> map_every Cases_on [`a`, `b`, `c`] >>
  gvs[operand_lit_val_def, venomStateTheory.eval_operand_def,
      venomStateTheory.read_memory_def] >>
  qmatch_asmsub_abbrev_tac `~MEM h hs.ss_flushed` >>
  `MEM h hs.ss_copies` by
    (simp[Abbr `hs`] >>
     metis_tac[mm_local_hazards_partition, invalidate_loads_def,
               scan_state_accfupds]) >>
  pop_assum mp_tac >> simp[Abbr `hs`] >>
  disch_then (mp_tac o MATCH_MP mm_local_flush_hazards_survivor) >>
  simp[copy_overwrites_def, copy_dst_interval_def, copy_src_interval_def,
       mmIntervalTheory.interval_overlaps_def, mmIntervalTheory.mk_interval_def,
       mmIntervalTheory.interval_end_def,
       arithmeticTheory.MAX_DEF, arithmeticTheory.MIN_DEF] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem mm_local_surviving_write_opcode:
  MEM h ss.ss_copies /\ ~MEM h (scan_inst dfg Mem2Mem ss i).ss_flushed ==>
  i.inst_opcode = MSTORE \/ i.inst_opcode = MCOPY \/
  ~(Eff_MEMORY IN write_effects i.inst_opcode)
Proof
  strip_tac >>
  Cases_on `i.inst_opcode = MSTORE` >- simp[] >>
  Cases_on `i.inst_opcode = MCOPY` >- simp[] >>
  Cases_on `i.inst_opcode = MLOAD`
  >- simp[venomEffectsTheory.write_effects_def, venomEffectsTheory.empty_effects_def] >>
  gvs[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  Cases_on `is_volatile_memory i` >>
  gvs[hard_barrier_def, MEM_APPEND, is_volatile_memory_def]
QED

Theorem mm_local_surviving_history_frame:
  mm_local_history is H n /\ q < n /\ MEM h ss.ss_copies /\
  ~MEM h (scan_inst dfg Mem2Mem ss (EL q is)).ss_flushed /\
  mm_local_write_capture is H n q = NONE ==>
  (H (SUC q)).vs_memory = (H q).vs_memory
Proof
  strip_tac >> irule mm_local_history_noncapture_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[mm_local_surviving_write_opcode]
QED

Theorem mm_local_surviving_source_read_recurrence:
  q < n /\ q < LENGTH is /\
  (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H n q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory /\
  MEM h ss.ss_copies /\
  ~MEM h (scan_inst dfg Mem2Mem ss (EL q is)).ss_flushed /\
  h.cg_src <= a /\ a + len <= h.cg_src + h.cg_length ==>
  read_memory a len (H (SUC q)) = read_memory a len (H q)
Proof
  strip_tac >> Cases_on `mm_local_write_capture is H n q`
  >- gvs[venomStateTheory.read_memory_def] >>
  PairCases_on `x` >> gvs[] >>
  `h.cg_length = 0 \/ LENGTH x1 = 0 \/
   h.cg_src + h.cg_length <= x0 \/ x0 + LENGTH x1 <= h.cg_src` by
    (metis_tac[mm_local_scan_step_war_exclusion]) >>
  simp[venomStateTheory.read_memory_def] >>
  irule frameViewMemoryTheory.padded_memory_read_cong >> rpt strip_tac >>
  irule frameViewMemoryTheory.write_memory_byte_outside >> decide_tac
QED

Theorem mm_local_bulk_cut_fragment:
  j < n /\ n <= LENGTH is /\
  (EL j is).inst_opcode = mode_copy_opcode mode /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  ss = FOLDL (scan_inst dfg mode) empty_scan_state (TAKE n is) /\
  c = <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id] |> ==>
  ?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor c h
Proof
  strip_tac >>
  qabbrev_tac `s0 = FOLDL (scan_inst dfg mode) empty_scan_state (TAKE j is)` >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst) s0.ss_copies` by
    (simp[Abbr `s0`] >> irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  `?a. MEM a (scan_bulk_copy mode s0 (EL j is)).ss_copies /\
    mm_local_copy_ancestor c a` by
    (irule mm_local_bulk_new_fragment >> simp[operand_lit_val_def] >> metis_tac[]) >>
  `scan_inst dfg mode s0 (EL j is) = scan_bulk_copy mode s0 (EL j is)` by
    (Cases_on `mode` >> gvs[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def]) >>
  `TAKE n is = (TAKE j is ++ [EL j is]) ++ TAKE (n-SUC j) (DROP (SUC j) is)` by
    (qspec_then `n` (qspec_then `SUC j` (qspec_then `is` mp_tac))
       rich_listTheory.take_drop_partition >>
     simp[rich_listTheory.TAKE_SUC, rich_listTheory.DROP_EL_CONS]) >>
  `ss = FOLDL (scan_inst dfg mode)
    (scan_inst dfg mode s0 (EL j is)) (TAKE (n-SUC j) (DROP (SUC j) is))` by
    simp[Abbr `s0`, FOLDL_APPEND] >>
  `?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor a h` by
    (qpat_assum `ss = _` SUBST1_TAC >> irule mm_local_fold_fragment >>
     simp[MEM_APPEND] >> metis_tac[mm_local_inst_order]) >>
  metis_tac[mm_local_copy_ancestor_trans]
QED

Theorem mm_local_store_cut_fragment:
  j < n /\ n <= LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  s0 = FOLDL (scan_inst dfg mode) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads v = SOME src /\
  ss = FOLDL (scan_inst dfg mode) empty_scan_state (TAKE n is) /\
  c = <| cg_dst := w2n dst; cg_src := src; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def dfg v of NONE => [] | SOME li => [li.inst_id]) |> ==>
  ?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor c h
Proof
  strip_tac >>
  `SORTED (\a b. a.cg_dst <= b.cg_dst) s0.ss_copies` by
    (simp[] >> irule mm_local_fold_order >> simp[empty_scan_state_def]) >>
  `?a. MEM a (scan_store dfg mode s0 (EL j is)).ss_copies /\
    mm_local_copy_ancestor c a` by
    (irule mm_local_store_new_fragment >> simp[operand_lit_val_def, operand_var_def] >>
     metis_tac[]) >>
  `scan_inst dfg mode s0 (EL j is) = scan_store dfg mode s0 (EL j is)` by
    (Cases_on `mode` >> gvs[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def]) >>
  `TAKE n is = (TAKE j is ++ [EL j is]) ++ TAKE (n-SUC j) (DROP (SUC j) is)` by
    (qspec_then `n` (qspec_then `SUC j` (qspec_then `is` mp_tac))
       rich_listTheory.take_drop_partition >>
     simp[rich_listTheory.TAKE_SUC, rich_listTheory.DROP_EL_CONS]) >>
  `ss = FOLDL (scan_inst dfg mode)
    (scan_inst dfg mode s0 (EL j is)) (TAKE (n-SUC j) (DROP (SUC j) is))` by
    (simp[FOLDL_APPEND] >> gvs[]) >>
  `?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\ mm_local_copy_ancestor a h` by
    (qpat_assum `ss = _` SUBST1_TAC >> irule mm_local_fold_fragment >>
     simp[MEM_APPEND] >> metis_tac[mm_local_inst_order]) >>
  metis_tac[mm_local_copy_ancestor_trans]
QED

Theorem mm_local_indexed_bulk_owner:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE n is) /\
  j < n /\ n <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = mode_copy_opcode mode /\
  (EL j is).inst_operands = [Lit dst; Lit src; Lit len] /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ?h. MEM h ss.ss_copies /\ MEM (EL j is).inst_id h.cg_inst_ids /\
    h.cg_dst <= w2n dst /\ w2n dst + w2n len <= h.cg_dst + h.cg_length /\
    mm_local_copy_ancestor
      <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id] |> h
Proof
  strip_tac >>
  `?h. MEM h (ss.ss_copies ++ ss.ss_flushed) /\
    mm_local_copy_ancestor
      <| cg_dst := w2n dst; cg_src := w2n src; cg_length := w2n len;
         cg_inst_ids := [(EL j is).inst_id] |> h` by
    (irule mm_local_bulk_cut_fragment >> simp[] >>
     qexistsl [`dfg_build_function fn0`, `is`, `j`, `mode`, `n`] >> simp[] >> gvs[]) >>
  `MEM (EL j is).inst_id h.cg_inst_ids /\ h.cg_dst <= w2n dst /\
    w2n dst + w2n len <= h.cg_dst + h.cg_length` by
    gvs[mm_local_copy_ancestor_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule venomTransformStructurePropsTheory.future_id_not_prefix >> simp[]) >>
  `bb.bb_instructions = TAKE n is ++ DROP n is` by simp[] >>
  `MEM (EL j is) bb.bb_instructions` by
    (gvs[] >> irule EL_MEM >> decide_tac) >>
  `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (Cases_on `mode` >> gvs[mode_copy_opcode_def]) >>
  `rep_of_group bb.bb_instructions g = SOME ((EL r is).inst_id,g)` by metis_tac[] >>
  `MEM h ss.ss_copies` by
    (drule_all (REWRITE_RULE [] (Q.INST [`w` |-> `EL j is`]
       (SPEC_ALL mm_local_prefix_write_pending_ancestor))) >>
     disch_then (assume_tac o CONJUNCT1) >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem mm_local_indexed_future_not_flushed:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ n <= r /\ r < LENGTH is /\ j < LENGTH is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE n is) /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM (EL j is).inst_id h.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  ~MEM h ss.ss_flushed
Proof
  strip_tac >> strip_tac >>
  `bb.bb_instructions = TAKE n is ++ DROP n is` by simp[] >>
  `MEM h (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by
    (qspecl_then [`DROP n is`, `ss`] strip_assume_tac
       (Q.INST [`dfg` |-> `dfg_build_function fn0`, `mode` |-> `Mem2Mem`]
          mm_local_fold_flushed_extension) >>
     gvs[scan_block_def, GSYM FOLDL_APPEND, hard_barrier_def, MEM_APPEND]) >>
  `h = g` by
    (irule mm_local_prefix_write_group_owner >>
     goal_assum (drule_at Any) >> metis_tac[MEM_EL]) >>
  `MEM (EL r is).inst_id h.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule mm_local_prefix_fragment_ids_before_cut >>
     goal_assum (drule_at Any) >> metis_tac[MEM_APPEND]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >> drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  metis_tac[venomTransformStructurePropsTheory.future_id_not_prefix]
QED


Theorem mm_local_indexed_store_owner:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE n is) /\
  j < n /\ n <= r /\ r < LENGTH is /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dst; Var v] /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE j is) /\
  FLOOKUP s0.ss_loads v = SOME src /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
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
    (SPEC_ALL (Q.INST [`mode` |-> `mode`] mm_local_store_cut_fragment)))) >> strip_tac >>
  `MEM (EL j is).inst_id h.cg_inst_ids /\ h.cg_dst <= w2n dst /\
    w2n dst + 32 <= h.cg_dst + h.cg_length` by
    (gvs[mm_local_copy_ancestor_def] >> metis_tac[MEM_APPEND, MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (qpat_assum `is = _` SUBST1_TAC >>
     drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))` by
    (irule venomTransformStructurePropsTheory.future_id_not_prefix >> simp[]) >>
  `bb.bb_instructions = TAKE n is ++ DROP n is` by simp[] >>
  `MEM (EL j is) bb.bb_instructions` by
    (gvs[] >> irule EL_MEM >> decide_tac) >>
  `(EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by simp[] >>
  `rep_of_group bb.bb_instructions g = SOME ((EL r is).inst_id,g)` by metis_tac[] >>
  drule_all (REWRITE_RULE [] (Q.INST [`w` |-> `EL j is`]
    (SPEC_ALL mm_local_prefix_write_pending_ancestor))) >> strip_tac >>
  metis_tac[]
QED

Theorem mm_local_history_store_value:
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

Theorem mm_local_indexed_store_history_owner:
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

Theorem mm_local_indexed_bulk_history_owner:
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
  drule_all (REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_bulk_owner)) >> strip_tac >>
  `j < N` by decide_tac >>
  drule_all mm_local_write_capture_copy >> strip_tac >>
  qexistsl [`h`, `w2n dst`, `read_memory (w2n src) (w2n len) (H j)`] >>
  asm_rewrite_tac[]
QED

Theorem mm_local_indexed_bulk_pending_birth:
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
      scan_store_def, operand_lit_val_def, operand_var_def,
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
     drule_all mm_local_write_capture_store >> simp[venomWriteReplayPropsTheory.mload_bytes]) >>
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
    (irule venomWriteReplayPropsTheory.read_write_log_memory >> qexists `ws` >> simp[]) >>
  irule mm_local_pending_create >>
  qexistsl [`read_memory src 32 (H n)`, `w2n dst`, `H n`] >>
  simp[]
QED

Theorem mm_local_indexed_store_pending_post_phis:
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

