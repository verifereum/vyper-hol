Theory lowerDloadPtrCompare
Ancestors
  lowerDloadPtrRel ptrDiscipline words

(* Inclusive endpoint comparisons use positive site identity, not equality
   of numeric provenance alone. *)
Theorem dload_pointer_word_comparisons:
  dload_live_layout lo sf tf fs /\ 0 < n /\
  dload_pointer_word fs (b,n) (c,m) x x' /\
  dload_pointer_word fs (b,n) (d,k) y y' /\
  b <= w2n x /\ w2n x <= b+n /\
  b <= w2n y /\ w2n y <= b+n ==>
  c = d /\ m = n /\ k = n /\
  c <= w2n x' /\ w2n x' <= c+n /\
  c <= w2n y' /\ w2n y' <= c+n /\
  (x = y <=> x' = y') /\
  (w2n x < w2n y <=> w2n x' < w2n y') /\
  (w2n y < w2n x <=> w2n y' < w2n x')
Proof
  strip_tac >>
  qpat_assum `dload_pointer_word fs (b,n) (c,m) x x'`
    (strip_assume_tac o MATCH_MP dload_pointer_word_resolves) >>
  qpat_assum `dload_pointer_word fs (b,n) (d,k) y y'`
    (strip_assume_tac o MATCH_MP dload_pointer_word_resolves) >>
  `c = d` by metis_tac[dload_live_site_positive_identity,
                         dload_live_site_target_unique] >>
  gvs[] >>
  `w2n (x - n2w b + n2w c) = c + (w2n x - b)` by
    (irule dload_pointer_word_interval >> metis_tac[]) >>
  `w2n (y - n2w b + n2w c) = c + (w2n y - b)` by
    (irule dload_pointer_word_interval >> metis_tac[]) >>
  simp[GSYM w2n_11] >> decide_tac
QED

Theorem dload_value_word_pointer_comparisons:
  dload_live_layout lo sf tf fs /\ tf <= fl /\ 0 < n /\
  dload_value_word fl fs {} (SOME (b,n)) (SOME (c,m)) x x' /\
  dload_value_word fl fs {} (SOME (b,n)) (SOME (d,k)) y y' /\
  b <= w2n x /\ w2n x <= b+n /\
  b <= w2n y /\ w2n y <= b+n ==>
  c = d /\ m = n /\ k = n /\
  c <= w2n x' /\ w2n x' <= c+n /\
  c <= w2n y' /\ w2n y' <= c+n /\
  (x = y <=> x' = y') /\
  (w2n x < w2n y <=> w2n x' < w2n y') /\
  (w2n y < w2n x <=> w2n y' < w2n x')
Proof
  strip_tac >>
  `!q z z'. dload_value_word fl fs {} (SOME (b,n)) q z z' ==>
     (?c. q = SOME (c,n) /\ dload_pointer_word fs (b,n) (c,n) z z' /\
          b + n <= fl) \/
     (q = SOME (b,n) /\ fl <= b /\ z = z')` by
    (rpt strip_tac >>
     drule_at (Pos last) dload_value_word_site_cases >>
     disch_then drule_all >> strip_tac >> gvs[] >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  Cases_on `fl <= b`
  >- (`~(b + n <= fl)` by decide_tac >>
      `SOME (c,m) = SOME (b,n) /\ x = x' /\ SOME (d,k) = SOME (b,n) /\ y = y'` by
        metis_tac[] >>
      gvs[]) >>
  `?c'. SOME (c,m) = SOME (c',n) /\ dload_pointer_word fs (b,n) (c',n) x x'` by
    metis_tac[] >>
  `?d'. SOME (d,k) = SOME (d',n) /\ dload_pointer_word fs (b,n) (d',n) y y'` by
    metis_tac[] >>
  gvs[] >> metis_tac[dload_pointer_word_comparisons]
QED
