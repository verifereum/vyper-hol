Theory concretizePtrOrdering
Ancestors
  concretizeMemLocDefs enumeral

Theorem ptr_incr_sbuild_ordered[local]:
  !xs. OL_sublists cmp (incr_sbuild cmp xs)
Proof
  Induct >> simp[incr_sbuild, OL_sublists] >>
  gen_tac >> irule incr_smerge_OL >> simp[OL]
QED

Theorem ptr_smerge_out_ordered[local]:
  !xss xs. OL_sublists cmp xss /\ OL cmp xs ==>
  OL cmp (smerge_out cmp xs xss)
Proof
  Induct >> simp[smerge_out, OL_sublists] >>
  Cases_on `h` >> simp[smerge_out, OL_sublists] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[smerge_OL]
QED

Theorem ptr_incr_ssort_ordered:
  OL cmp (incr_ssort cmp xs)
Proof
  simp[incr_ssort] >> irule ptr_smerge_out_ordered >>
  simp[ptr_incr_sbuild_ordered, OL]
QED

Theorem ptr_base_allocas_ordered:
  OL alloc_to (find_base_allocas bpr op)
Proof
  Cases_on `op` >> simp[find_base_allocas_def, ptr_incr_ssort_ordered, OL]
QED

Theorem ptr_base_allocas_opt_ordered:
  OL alloc_to (find_base_allocas_opt bpr op)
Proof
  Cases_on `op` >> simp[find_base_allocas_opt_def, ptr_base_allocas_ordered, OL]
QED

Definition ptr_ml_ordered_def:
  ptr_ml_ordered st <=> !addr. OL alloc_to (ml_lookup st addr)
End

Theorem ptr_ml_ordered_empty[simp]:
  ptr_ml_ordered FEMPTY
Proof
  simp[ptr_ml_ordered_def, ml_lookup_def, OL]
QED

Theorem ptr_ml_ordered_update:
  ptr_ml_ordered st /\ OL alloc_to xs ==>
  ptr_ml_ordered (st |+ (addr,xs))
Proof
  simp[ptr_ml_ordered_def, ml_lookup_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem ptr_ordered_merge_fold:
  !xs. OL cmp xs /\ EVERY (OL cmp) xss ==>
  OL cmp (FOLDL (smerge cmp) xs xss)
Proof
  Induct_on `xss` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[smerge_OL]
QED

Theorem ptr_kill_write_ordered[local]:
  OL alloc_to live ==>
  OL alloc_to (ml_kill_write sizes reads wsz live a)
Proof
  strip_tac >> simp[ml_kill_write_def] >>
  Cases_on `sizes a` >> simp[] >>
  rpt IF_CASES_TAC >> simp[]
  >- (drule OL_DIFF_IMP >> disch_then (qspec_then `[a]` mp_tac) >> simp[OL]) >>
  irule smerge_OL >> simp[OL]
QED

Theorem ptr_operand_allocas_fold_ordered[local]:
  OL alloc_to (FOLDL (smerge alloc_to) []
    (MAP (find_base_allocas bpr) ops))
Proof
  irule ptr_ordered_merge_fold >>
  simp[OL, listTheory.EVERY_MAP, listTheory.EVERY_MEM, ptr_base_allocas_ordered]
QED

