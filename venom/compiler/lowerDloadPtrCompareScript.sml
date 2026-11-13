Theory lowerDloadPtrCompare
Ancestors
  lowerDloadPtrRel words

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
  dload_live_layout lo sf tf fs /\ 0 < n /\
  dload_value_word fs mask (SOME (b,n)) (SOME (c,m)) x x' /\
  dload_value_word fs mask' (SOME (b,n)) (SOME (d,k)) y y' /\
  b <= w2n x /\ w2n x <= b+n /\
  b <= w2n y /\ w2n y <= b+n ==>
  c = d /\ m = n /\ k = n /\
  c <= w2n x' /\ w2n x' <= c+n /\
  c <= w2n y' /\ w2n y' <= c+n /\
  (x = y <=> x' = y') /\
  (w2n x < w2n y <=> w2n x' < w2n y') /\
  (w2n y < w2n x <=> w2n y' < w2n x')
Proof
  simp[dload_value_word_def] >>
  metis_tac[dload_pointer_word_comparisons]
QED
