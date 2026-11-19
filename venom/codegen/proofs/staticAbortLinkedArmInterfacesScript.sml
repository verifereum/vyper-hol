(* Successor interfaces are preserved by exit redirection and rooted restriction. *)
Theory staticAbortLinkedArmInterfaces
Ancestors
  pred_set arithmetic

Theorem linked_reachable_arm_interfaces:
  ! (V:(num#num)->bool) X e (R:(num#num)->(num#num)->bool) link
    (I:(num#num)->'a).
  !A. A = V DIFF X ==>
  !E. E = (\x y. x IN A /\ ?z. R x z /\ y = (if z IN X then link z else z)) ==>
  !W. W = {x | x IN A /\ ?n (path:num->num#num). path 0 = e /\ path n = x /\
      (!k. k < n ==> E (path k) (path (SUC k)))} ==>
  (!x z. R x z ==> x IN A /\ z IN V) /\
  (!z. z IN X ==> link z IN A /\ I (link z) = I z) ==>
  !x v. x IN W ==>
    ((?z. R x z /\ I z = v) <=> (?y. y IN W /\ E x y /\ I y = v))
Proof
  ntac 5 gen_tac >> qx_gen_tac `iface` >>
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  gen_tac >> disch_then (mp_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qabbrev_tac `dest = \z. if z IN X then link z else z` >>
  disch_tac >> gen_tac >> disch_then SUBST1_TAC >>
  qabbrev_tac `reach = \x. ?n (path:num->num#num).
    path 0 = e /\ path n = x /\ !k. k < n ==> E (path k) (path(SUC k))` >>
  strip_tac >>
  `!z. z IN V ==> dest z IN A /\ iface (dest z) = iface z` by
    (gen_tac >> strip_tac >> Cases_on `z IN X`
     >- (simp[Abbr `dest`] >> metis_tac[]) >>
     simp[Abbr `dest`, Abbr `A`]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  eq_tac >> strip_tac
  >- (`dest z IN A /\ iface (dest z) = iface z` by metis_tac[] >>
      `E x (dest z)` by (simp[Abbr `E`] >> metis_tac[]) >>
      qexists `dest z` >> simp[] >>
      qpat_x_assum `reach x` mp_tac >> simp[Abbr `reach`] >> strip_tac >>
      qexistsl [`SUC n`, `\k. if k <= n then path k else dest z`] >>
      simp[] >> rpt strip_tac >> Cases_on `k < n`
      >- (`SUC k <= n` by decide_tac >> simp[]) >>
      `k = n` by decide_tac >> simp[]) >>
  qpat_x_assum `E x y` mp_tac >> simp[Abbr `E`] >> metis_tac[]
QED
