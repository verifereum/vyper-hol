Theory fnPlanLineageDistinct
Ancestors
  list finite_map dfHelperDefs dfAnalyzeDefs

Theorem list_union_all_distinct:
  ALL_DISTINCT xs /\ ALL_DISTINCT ys ==>
  ALL_DISTINCT (list_union xs ys)
Proof
  simp[list_union_def, ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT,
       MEM_FILTER] >> metis_tac[]
QED

Theorem foldl_list_union_all_distinct:
  !xss acc. ALL_DISTINCT acc /\ EVERY ALL_DISTINCT xss ==>
    ALL_DISTINCT (FOLDL list_union acc xss)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[list_union_all_distinct]
QED

Definition lineage_map_values_def:
  lineage_map_values P m <=>
    !k v. FLOOKUP m k = SOME v ==> P v
End

Theorem lineage_map_values_empty[simp]:
  lineage_map_values P FEMPTY
Proof
  simp[lineage_map_values_def]
QED

Theorem lineage_map_values_update:
  lineage_map_values P m /\ P v ==>
  lineage_map_values P (m |+ (k,v))
Proof
  rw[lineage_map_values_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem lineage_map_values_union:
  lineage_map_values P m /\ lineage_map_values P n ==>
  lineage_map_values P (FUNION m n)
Proof
  rw[lineage_map_values_def, FLOOKUP_FUNION] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem df_fold_backward_map_values:
  !insts idx acc m entry m'.
    (!inst v. P v ==> P (transfer inst v)) /\
    P acc /\ lineage_map_values P m /\
    df_fold_backward transfer lbl insts idx acc m = (entry,m') ==>
    P entry /\ lineage_map_values P m'
Proof
  Induct >> rpt gen_tac
  >- (simp[df_fold_backward_def] >> rpt strip_tac >>
      gvs[] >> irule lineage_map_values_update >> simp[]) >>
  strip_tac >>
  Cases_on `df_fold_backward transfer lbl insts (idx + 1) acc m` >>
  gvs[df_fold_backward_def] >>
  qpat_x_assum `!idx' acc' m'' entry' m3. _` drule_all >> strip_tac >>
  `P (transfer h q)` by metis_tac[] >>
  simp[] >> irule lineage_map_values_update >> simp[]
QED

Theorem df_fold_block_backward_map_values:
  (!inst v. P v ==> P (transfer inst v)) /\ P acc /\
  df_fold_block Backward transfer lbl insts acc = (entry,m) ==>
  P entry /\ lineage_map_values P m
Proof
  simp[df_fold_block_def] >> strip_tac >>
  irule df_fold_backward_map_values >>
  simp[] >>
  goal_assum (drule_at (Pat `df_fold_backward _ _ _ _ _ _ = _`)) >> simp[]
QED
