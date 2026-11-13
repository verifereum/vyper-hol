Theory concretizePtrPrefixCoverage
Ancestors
  concretizePtrReadCoverage concretizeMemLocDefs finite_map

Theorem ptr_liveat_prefix_preserves:
  !xs live la. MEM a live /\
    EVERY (\p. ~ptr_ml_can_kill a bpr sizes (SND p)) xs ==>
    MEM a (FST (ml_liveat_insts_rev bpr mems sizes label live la xs))
Proof
  Induct_on `xs` >- simp[ml_liveat_insts_rev_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  simp[ml_liveat_insts_rev_def] >>
  Cases_on `ml_liveat_insts_rev bpr mems sizes label live la xs` >>
  gvs[] >> irule ptr_liveat_preserves >>
  gvs[] >> metis_tac[pairTheory.FST]
QED

Theorem ptr_liveat_prefix_records:
  !xs live la. MEM a live /\
    EVERY (\p. ~ptr_ml_can_kill a bpr sizes (SND p)) xs /\
    ALL_DISTINCT (MAP FST xs) /\ MEM (idx,inst) xs ==>
    MEM a (ml_lookup
      (SND (ml_liveat_insts_rev bpr mems sizes label live la xs)) (label,idx))
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[ml_liveat_insts_rev_def] >>
  strip_tac >>
  Cases_on `ml_liveat_insts_rev bpr mems sizes label live la xs` >>
  gvs[]
  >- (irule ptr_liveat_records >> disj1_tac >>
      drule_all ptr_liveat_prefix_preserves >>
      disch_then (qspecl_then [`mems`,`label`,`la`] mp_tac) >> simp[]) >>
  `h0 <> idx` by
    (strip_tac >> gvs[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  simp[ml_liveat_inst_def, ml_lookup_def, FLOOKUP_UPDATE] >>
  metis_tac[pairTheory.SND, ml_lookup_def]
QED

Theorem ptr_liveat_prefix_append:
  !xs live la.
  ml_liveat_insts_rev bpr mems sizes label live la (xs ++ ys) =
  ml_liveat_insts_rev bpr mems sizes label
    (FST (ml_liveat_insts_rev bpr mems sizes label live la ys))
    (SND (ml_liveat_insts_rev bpr mems sizes label live la ys)) xs
Proof
  Induct_on `xs` >> simp[ml_liveat_insts_rev_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[ml_liveat_insts_rev_def] >>
  Cases_on `ml_liveat_insts_rev bpr mems sizes label live la ys` >> simp[]
QED
