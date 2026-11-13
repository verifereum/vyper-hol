Theory loadElimJoinProps
Ancestors
  loadElimDefs finite_map pred_set

Theorem load_join_empty_left[simp]:
  load_join (SOME FEMPTY) (SOME m) = SOME FEMPTY
Proof
  simp[load_join_def, load_join_raw_def, FUN_FMAP_EMPTY]
QED

Theorem load_join_empty_right[simp]:
  load_join (SOME m) (SOME FEMPTY) = SOME FEMPTY
Proof
  simp[load_join_def, load_join_raw_def, FUN_FMAP_EMPTY]
QED

Theorem load_join_singleton_same[simp]:
  load_join (SOME (FEMPTY |+ (k,xs))) (SOME (FEMPTY |+ (k,ys))) =
  SOME (FEMPTY |+ (k,operand_list_union xs ys))
Proof
  simp[load_join_def, load_join_raw_def] >>
  simp[fmap_EXT, FUN_FMAP_DEF, FLOOKUP_DEF]
QED

Theorem load_join_singleton_distinct:
  k <> j ==>
  load_join (SOME (FEMPTY |+ (k,xs))) (SOME (FEMPTY |+ (j,ys))) =
  SOME FEMPTY
Proof
  strip_tac >>
  `({k} INTER {j}) = {}` by (simp[EXTENSION] >> metis_tac[]) >>
  simp[load_join_def, load_join_raw_def, FUN_FMAP_EMPTY]
QED
