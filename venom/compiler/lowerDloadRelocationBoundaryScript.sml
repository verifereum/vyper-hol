(* Arithmetic interface probes for allocation-relative pointer transport.
   No state relation is defined by this diagnostic. *)
Theory lowerDloadRelocationBoundary
Ancestors
  arithmetic words

Theorem site_translation_comparisons:
  !b c sz x y:num.
    b <= x /\ x <= b + sz /\ b <= y /\ y <= b + sz ==>
    ((c + (x - b) = c + (y - b)) <=> (x = y)) /\
    ((c + (x - b) < c + (y - b)) <=> (x < y)) /\
    c <= c + (x - b) /\ c + (x - b) <= c + sz
Proof
  rpt strip_tac >> decide_tac
QED

Theorem site_translation_word_value:
  !b c sz x:num.
    b <= x /\ x <= b + sz /\ c + sz < dimword (:256) ==>
    w2n (n2w (c + (x - b)) : 256 word) = c + (x - b)
Proof
  rpt strip_tac >> simp[] >>
  `c + (x - b) < dimword (:256)` by decide_tac >>
  simp[LESS_MOD]
QED
