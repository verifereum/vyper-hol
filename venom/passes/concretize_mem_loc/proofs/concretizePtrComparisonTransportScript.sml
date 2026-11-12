Theory concretizePtrComparisonTransport
Ancestors concretizePtrValueTransport words arithmetic

Theorem ptr_comparison_eq_transport:
  (x':bytes32) = x - n2w b + n2w p /\
  (y':bytes32) = y - n2w b + n2w p ==>
  (x' = y' <=> x = y)
Proof
  strip_tac >> gvs[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ptr_closed_relocation_value:
  (x':bytes32) = x - n2w b + n2w p /\
  b <= w2n x /\ w2n x <= b + sz /\
  p + sz < dimword(:256) ==>
  w2n x' = p + (w2n x - b)
Proof
  strip_tac >>
  `b < dimword(:256)` by metis_tac[w2n_lt, LESS_EQ_LESS_TRANS] >>
  `w2n (n2w b:bytes32) = b` by simp[] >>
  `n2w b <=+ x` by simp[WORD_LS] >>
  `w2n (x - n2w b) = w2n x - b` by
    metis_tac[word_sub_w2n] >>
  `p + (w2n x - b) < dimword(:256)` by decide_tac >>
  gvs[word_add_def, w2n_n2w] >> simp[LESS_MOD, ADD_COMM]
QED

Theorem ptr_comparison_lt_transport:
  (x':bytes32) = x - n2w b + n2w p /\
  (y':bytes32) = y - n2w b + n2w p /\
  b <= w2n x /\ w2n x <= b + sz /\
  b <= w2n y /\ w2n y <= b + sz /\
  p + sz < dimword(:256) ==>
  (w2n x' < w2n y' <=> w2n x < w2n y)
Proof
  strip_tac >>
  `w2n x' = p + (w2n x - b)` by
    (irule ptr_closed_relocation_value >> metis_tac[]) >>
  `w2n y' = p + (w2n y - b)` by
    (irule ptr_closed_relocation_value >> metis_tac[]) >>
  decide_tac
QED

Theorem ptr_comparison_gt_transport:
  (x':bytes32) = x - n2w b + n2w p /\
  (y':bytes32) = y - n2w b + n2w p /\
  b <= w2n x /\ w2n x <= b + sz /\
  b <= w2n y /\ w2n y <= b + sz /\
  p + sz < dimword(:256) ==>
  (w2n x' > w2n y' <=> w2n x > w2n y)
Proof
  rewrite_tac[GREATER_DEF] >>
  strip_tac >> irule ptr_comparison_lt_transport >> metis_tac[]
QED
