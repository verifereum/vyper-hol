(* Returning to a suspended caller retains the allocation keys of every
   remaining suffix, even though the resumed row can lose H bindings. *)
Theory gasFocusLowerDloadSuffixPop
Ancestors
  lowerDloadSafetyRelation lowerDloadReturnInvokePop
  venomState finite_map pred_set list rich_list arithmetic

Theorem ld_focus_suffix_pop:
  (!k a. k < LENGTH (child::f::fs) /\
    (a IN FRANGE (EL k (child::f::fs)).lf_H \/
     MEM (SOME a) (EL k (child::f::fs)).lf_Q) ==>
    a IN ld_slots A (DROP k (child::f::fs))) /\
  B = DRESTRICT A (ld_slots A (f::fs)) /\
  g.lf_serial = f.lf_serial /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas /\
  FRANGE g.lf_H SUBSET FRANGE f.lf_H /\ g.lf_Q = f.lf_Q ==>
  (!k a. k < LENGTH (g::fs) /\
    (a IN FRANGE (EL k (g::fs)).lf_H \/
     MEM (SOME a) (EL k (g::fs)).lf_Q) ==>
    a IN ld_slots B (DROP k (g::fs))) /\
  FDOM B = ld_slots B (g::fs)
Proof
  strip_tac >>
  reverse conj_tac
  >- (drule_all ld_slots_head_cong >> strip_tac >>
      simp[ld_slots_restrict_domain]) >>
  rpt gen_tac >> Cases_on `k` >> simp[rich_listTheory.DROP] >> disch_tac
  >- (`a IN ld_slots A (f::fs)` by
        (first_x_assum (qspecl_then [`SUC 0`, `a`] mp_tac) >>
         simp[rich_listTheory.DROP] >> metis_tac[SUBSET_DEF]) >>
      drule_all ld_slots_head_cong >> strip_tac >> simp[ld_slots_restrict]) >>
  `a IN ld_slots A (DROP n fs)` by
    (first_x_assum (qspecl_then [`SUC (SUC n)`, `a`] mp_tac) >>
     simp[rich_listTheory.DROP]) >>
  `a IN ld_slots A (f::fs)` by
    (qpat_x_assum `a IN ld_slots A (DROP n fs)` mp_tac >>
     simp[ld_slots_def] >> metis_tac[MEM_DROP_IMP]) >>
  simp[ld_slots_restrict]
QED
