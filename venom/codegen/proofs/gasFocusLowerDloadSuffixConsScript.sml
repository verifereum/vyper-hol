(* Allocation-key confinement for the retained suffix of a LowerDload stack. *)
Theory gasFocusLowerDloadSuffixCons
Ancestors
  lowerDloadReturnInvokeStack lowerDloadSafetyRelation
  list rich_list arithmetic finite_map pred_set

Theorem ld_focus_slots_drop[local]:
  a IN ld_slots A (DROP k xs) ==> a IN ld_slots A xs
Proof
  simp[ld_slots_def] >> metis_tac[MEM_DROP_IMP]
QED

Theorem ld_focus_suffix_cons:
  xs = DROP m old /\ m <= LENGTH old /\
  (!k a. k < LENGTH old /\
    (a IN FRANGE (EL k old).lf_H \/ MEM (SOME a) (EL k old).lf_Q) ==>
    a IN ld_slots A (DROP k old)) /\
  (!a. a IN ld_slots A xs ==> FLOOKUP B a = FLOOKUP A a) /\
  ld_global lo B (g::xs) /\ FDOM B = ld_slots B (g::xs) ==>
  !k a. k < LENGTH (g::xs) /\
    (a IN FRANGE (EL k (g::xs)).lf_H \/ MEM (SOME a) (EL k (g::xs)).lf_Q) ==>
    a IN ld_slots B (DROP k (g::xs))
Proof
  strip_tac >> qx_gen_tac `k` >> qx_gen_tac `a` >> Cases_on `k`
  >- (simp[] >> metis_tac[ld_global_selected, MEM]) >>
  rename1 `SUC j` >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `j + m < LENGTH old` by fs[] >>
  `a IN ld_slots A (DROP j xs)` by
    (qpat_x_assum `xs = _` SUBST_ALL_TAC >> simp[DROP_DROP_T] >>
     qpat_x_assum `!k a. _ ==> _ IN ld_slots A (DROP k old)`
       (qspecl_then [`j + m`, `a`] irule) >>
     fs[EL_DROP]) >>
  `ld_slots A (DROP j xs) SUBSET ld_slots B (DROP j xs)` by
    (irule ld_slots_agree_subset >> metis_tac[ld_focus_slots_drop]) >>
  metis_tac[SUBSET_DEF]
QED

Theorem ld_focus_suffix_saved:
  (!k a. k < LENGTH (g::xs) /\
    (a IN FRANGE (EL k (g::xs)).lf_H \/ MEM (SOME a) (EL k (g::xs)).lf_Q) ==>
    a IN ld_slots A (DROP k (g::xs))) ==>
  !h a. MEM h xs /\ (a IN FRANGE h.lf_H \/ MEM (SOME a) h.lf_Q) ==>
    a IN ld_slots A xs
Proof
  strip_tac >> rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  qpat_x_assum `MEM h xs` mp_tac >> simp[MEM_EL] >> strip_tac >>
  rename1 `j < LENGTH xs` >>
  irule ld_focus_slots_drop >> qexists_tac `j` >>
  qpat_x_assum `!k a. _ ==> _ IN ld_slots A (DROP k (g::xs))`
    (qspecl_then [`SUC j`, `a`] mp_tac) >>
  gvs[]
QED
