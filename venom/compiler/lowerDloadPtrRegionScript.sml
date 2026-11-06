Theory lowerDloadPtrRegion
Ancestors
  lowerDloadPtrRel lowerDloadPtrAffine ptrDiscipline arithmetic words

Theorem dload_value_contained_region:
  dload_live_layout lo sf tf fs /\
  dload_value_word fs {} p q x y /\
  ((lo < w2n x + len \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n x /\ w2n x + len <= b+n) ==>
  (w2n x = w2n y /\ w2n x + len <= lo) \/
  (?owner id b c n d. dload_live_site fs owner id b c n /\
    w2n x = b+d /\ w2n y = c+d /\ d+len <= n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `p`
  >- (Cases_on `q` >>
      gvs[dload_value_word_def, word_agree_except_bits] >>
      disj1_tac >> simp[fcpTheory.CART_EQ] >> metis_tac[]) >>
  PairCases_on `x'` >>
  qpat_x_assum `(_ \/ _) ==> _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[dload_value_word_def] >>
  PairCases_on `x'` >> gvs[dload_pointer_word_def] >>
  `dload_pointer_word fs (b,n) (x'0,n) x
     (x - n2w b + n2w x'0)` by
    (simp[dload_pointer_word_def] >> metis_tac[]) >>
  `w2n x <= b+n` by decide_tac >>
  drule_all dload_pointer_word_interval >> strip_tac >>
  disj2_tac >> qexistsl [`owner`,`id`,`b`,`x'0`,`n`,`w2n x-b`] >>
  simp[] >> decide_tac
QED
