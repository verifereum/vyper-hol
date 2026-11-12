(* Whole-stride containment, distinct from live-footprint containment. *)
Theory bodyPtrSubscriptCoverage
Ancestors
  arithmetic

Theorem array_buffer_child_interval:
  !b a h n z sz i:num.
    b <= a /\ a + h + n * z <= b + sz /\ i < n ==>
    b <= a + h + i * z /\ (a + h + i * z) + z <= b + sz
Proof
  rpt gen_tac >> strip_tac >>
  `SUC i <= n` by decide_tac >>
  `SUC i * z <= n * z` by simp[] >>
  pop_assum mp_tac >> pure_rewrite_tac[MULT_CLAUSES] >> decide_tac
QED
