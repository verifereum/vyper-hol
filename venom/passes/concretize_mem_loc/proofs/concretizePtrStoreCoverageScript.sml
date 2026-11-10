Theory concretizePtrStoreCoverage
Ancestors
  concretizeMemLocDefs

Theorem ptr_smerge_member[local]:
  MEM addr (smerge inst_addr_to [x] cur) <=> addr = x \/ MEM addr cur
Proof
  `!x y. apto inst_addr_to x y = EQUAL <=> x = y` by
    (qspec_then `inst_addr_to` mp_tac totoTheory.TotOrd_apto >>
     simp[totoTheory.TotOrd]) >>
  Induct_on `cur` >> simp[enumeralTheory.smerge] >>
  gen_tac >>
  Cases_on `apto inst_addr_to x h` >>
  fs[enumeralTheory.smerge, enumeralTheory.smerge_nil] >> metis_tac[]
QED

Definition ptr_store_insert_def:
  ptr_store_insert addr m alloc =
    m |+ (alloc, smerge inst_addr_to [addr]
      (case FLOOKUP m alloc of SOME s => s | NONE => []))
End

Theorem ptr_store_insert_preserves[local]:
  FLOOKUP m a = SOME addrs /\ MEM p addrs ==>
  ?addrs'. FLOOKUP (ptr_store_insert addr m alloc) a = SOME addrs' /\
            MEM p addrs'
Proof
  rpt strip_tac >> Cases_on `a = alloc` >>
  simp[ptr_store_insert_def, finite_mapTheory.FLOOKUP_UPDATE, ptr_smerge_member] >>
  gvs[]
QED

Theorem ptr_store_insert_covers[local]:
  ?addrs. FLOOKUP (ptr_store_insert addr m a) a = SOME addrs /\ MEM addr addrs
Proof
  simp[ptr_store_insert_def, finite_mapTheory.FLOOKUP_UPDATE, ptr_smerge_member]
QED

Theorem ptr_store_fold_preserves:
  !m. FLOOKUP m a = SOME addrs /\ MEM p addrs ==>
  ?addrs'. FLOOKUP (FOLDL (ptr_store_insert addr) m keys) a = SOME addrs' /\
            MEM p addrs'
Proof
  qid_spec_tac `addrs` >> Induct_on `keys` >> simp[] >>
  metis_tac[ptr_store_insert_preserves]
QED

Theorem ptr_store_fold_covers:
  !m. MEM a keys ==>
  ?addrs. FLOOKUP (FOLDL (ptr_store_insert addr) m keys) a = SOME addrs /\
          MEM addr addrs
Proof
  Induct_on `keys` >> simp[] >> rpt strip_tac >> gvs[]
  >- metis_tac[ptr_store_insert_covers, ptr_store_fold_preserves]
  >> first_x_assum irule >> simp[]
QED

Theorem ptr_store_insts_preserves[local]:
  !ls addrs. FLOOKUP ls a = SOME addrs /\ MEM p addrs ==>
  ?addrs'. FLOOKUP (ml_mark_stores_insts bpr label ls insts) a = SOME addrs' /\
            MEM p addrs'
Proof
  Induct_on `insts` >> simp[ml_mark_stores_insts_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[ml_mark_stores_insts_def, GSYM ptr_store_insert_def, SF ETA_ss] >>
  rpt strip_tac >> first_x_assum irule >>
  irule ptr_store_fold_preserves >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ptr_store_insts_covers[local]:
  !ls. MEM (idx,inst) insts /\
  MEM a (find_base_allocas_opt bpr (inst_write_op inst)) ==>
  ?addrs. FLOOKUP (ml_mark_stores_insts bpr label ls insts) a = SOME addrs /\
          MEM (label,idx) addrs
Proof
  Induct_on `insts` >> simp[ml_mark_stores_insts_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[ml_mark_stores_insts_def, GSYM ptr_store_insert_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[]
  >- (irule ptr_store_insts_preserves >>
      irule ptr_store_fold_covers >> simp[])
  >> first_x_assum irule >> simp[]
QED

Theorem ptr_store_blocks_preserves[local]:
  !ls addrs. FLOOKUP ls a = SOME addrs /\ MEM p addrs ==>
  ?addrs'. FLOOKUP
    (FOLDL (\m bb. ml_mark_stores_insts bpr bb.bb_label m
      (MAPi (\i inst. (i,inst)) bb.bb_instructions)) ls blocks) a = SOME addrs' /\
    MEM p addrs'
Proof
  Induct_on `blocks` >> simp[] >>
  metis_tac[ptr_store_insts_preserves]
QED

Theorem ptr_mark_stores_preserves:
  FLOOKUP ls a = SOME addrs /\ MEM addr addrs ==>
  ?addrs'. FLOOKUP (ml_mark_stores_live bpr fn ls) a = SOME addrs' /\
            MEM addr addrs'
Proof
  simp[ml_mark_stores_live_def, ptr_store_blocks_preserves]
QED

Theorem ptr_store_blocks_covers[local]:
  !ls. MEM bb blocks /\
  MEM (idx,inst) (MAPi (\i inst. (i,inst)) bb.bb_instructions) /\
  MEM a (find_base_allocas_opt bpr (inst_write_op inst)) ==>
  ?addrs. FLOOKUP
    (FOLDL (\m bb. ml_mark_stores_insts bpr bb.bb_label m
      (MAPi (\i inst. (i,inst)) bb.bb_instructions)) ls blocks) a = SOME addrs /\
    MEM (bb.bb_label,idx) addrs
Proof
  Induct_on `blocks` >> simp[] >> rpt strip_tac >> gvs[]
  >- metis_tac[ptr_store_insts_covers, ptr_store_blocks_preserves]
  >> first_x_assum irule >> simp[]
QED

Theorem ptr_mark_stores_covers_write:
  MEM bb fn.fn_blocks /\
  MEM (idx,inst) (MAPi (\i inst. (i,inst)) bb.bb_instructions) /\
  MEM a (find_base_allocas_opt bpr (inst_write_op inst)) ==>
  ?addrs. FLOOKUP (ml_mark_stores_live bpr fn ls) a = SOME addrs /\
          MEM (bb.bb_label,idx) addrs
Proof
  rewrite_tac[ml_mark_stores_live_def] >>
  rpt strip_tac >> irule ptr_store_blocks_covers >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem ptr_fuel_liveness_covers_write:
  MEM bb fn.fn_blocks /\
  MEM (idx,inst) (MAPi (\i inst. (i,inst)) bb.bb_instructions) /\
  MEM a (find_base_allocas_opt bpr (inst_write_op inst)) ==>
  ?addrs. FLOOKUP
    (mem_liveness_analyze_fuel fuel bpr mems_used alloca_sizes live_pallocas cfg fn) a
    = SOME addrs /\ MEM (bb.bb_label,idx) addrs
Proof
  rpt strip_tac >> simp[mem_liveness_analyze_fuel_def] >>
  pairarg_tac >> simp[] >> irule ptr_mark_stores_covers_write >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
