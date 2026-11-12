(* Spatial authorization only: provenance does not itself certify execution. *)
Theory bodyIntCallWriteAuthorization
Ancestors
  bodyIntCallResourceSpans intCallCallee compileEnv loweringStateRelDefs

Theorem provenance_protected_regions:
  (!a k. P a k ==> a + k <= lo) /\
  (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
  (!name p n. R name p n ==>
    lo <= p \/ ?b z. staged b z /\ b <= p /\ p + n <= b + z) ==>
  !name p n. R name p n ==>
    !a k. P a k ==> regions_disjoint a k p n
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum drule >> strip_tac
  >- (rpt strip_tac >> simp[regions_disjoint_def] >>
      first_x_assum drule >> decide_tac) >>
  rpt strip_tac >>
  `regions_disjoint a k b z` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem materialization_protected_regions:
  (!a k. P a k ==> a + k <= lo) /\
  (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
  mat_inv func ce env st s lo mr /\
  (!name p n. mr name = SOME (p,n) ==>
    ?b z. staged b z /\ b <= p /\ p + n <= b + z) ==>
  !name p n. local_region ce [env] s name p n ==>
    !a k. P a k ==> regions_disjoint a k p n
Proof
  strip_tac >> ho_match_mp_tac provenance_protected_regions >>
  simp[] >> fs[mat_inv_def] >> metis_tac[]
QED
