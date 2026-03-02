(*
 * Dataflow Iterate — Convergence Proofs
 *)

Theory dfIterateProofs
Ancestors
  dfIterateDefs

open arithmeticTheory WhileTheory

(* Orbit-bounded fixpoint: P is an invariant on the orbit of x under f.
   The measure m strictly increases (under P) when f changes something,
   and is bounded by b under P. *)
Theorem df_iterate_fixpoint_orbit:
  !(f : 'a -> 'a) (m : 'a -> num) b (P : 'a -> bool) x.
    (!y. P y /\ f y <> y ==> m (f y) > m y) /\
    P x /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  rpt strip_tac >>
  simp[df_iterate_def] >>
  `?n. ~(\y. f y <> y) (FUNPOW f n x)` by (
    completeInduct_on `b - m x` >> rpt strip_tac >>
    Cases_on `f x = x`
    >- (qexists_tac `0` >> simp[]) >>
    `m (f x) > m x` by metis_tac[] >>
    `P (f x)` by metis_tac[] >>
    `m (f x) <= b` by metis_tac[] >>
    `b - m (f x) < v` by simp[] >>
    qpat_x_assum `!m'. m' < v ==> _` drule >>
    disch_then (qspecl_then [`b`, `m`, `f x`] mp_tac) >>
    simp[] >>
    strip_tac >>
    qexists_tac `SUC n` >> simp[FUNPOW]
  ) >>
  `?r. OWHILE (\y. f y <> y) f x = SOME r` by (
    Cases_on `OWHILE (\y. f y <> y) f x` >>
    fs[OWHILE_EQ_NONE] >> metis_tac[]
  ) >>
  imp_res_tac OWHILE_ENDCOND >>
  imp_res_tac OWHILE_WHILE >>
  fs[]
QED

(* Orbit-bounded invariant preservation: P holds for df_iterate result. *)
Theorem df_iterate_invariant:
  !(f : 'a -> 'a) (m : 'a -> num) b (P : 'a -> bool) x.
    (!y. P y /\ f y <> y ==> m (f y) > m y) /\
    P x /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    P (df_iterate f x)
Proof
  rpt strip_tac >>
  simp[df_iterate_def] >>
  (* Reuse termination proof from fixpoint_orbit *)
  `?n. ~(\y. f y <> y) (FUNPOW f n x)` by (
    completeInduct_on `b - m x` >> rpt strip_tac >>
    Cases_on `f x = x`
    >- (qexists_tac `0` >> simp[]) >>
    `m (f x) > m x` by metis_tac[] >>
    `P (f x)` by metis_tac[] >>
    `m (f x) <= b` by metis_tac[] >>
    `b - m (f x) < v` by simp[] >>
    qpat_x_assum `!m'. m' < v ==> _` drule >>
    disch_then (qspecl_then [`b`, `m`, `f x`] mp_tac) >>
    simp[] >>
    strip_tac >>
    qexists_tac `SUC n` >> simp[FUNPOW]
  ) >>
  `?r. OWHILE (\y. f y <> y) f x = SOME r` by (
    Cases_on `OWHILE (\y. f y <> y) f x` >>
    fs[OWHILE_EQ_NONE] >> metis_tac[]
  ) >>
  imp_res_tac OWHILE_WHILE >> gvs[] >>
  qspecl_then [`\y. f y <> y`, `f`, `x`] mp_tac OWHILE_INV_IND >>
  simp[]
QED

(* Original interface: bound holds globally (P = K T). *)
Theorem df_iterate_fixpoint_proof:
  !(f : 'a -> 'a) (m : 'a -> num) b x.
    (!y. f y <> y ==> m (f y) > m y) /\
    (!y. m y <= b) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  rpt strip_tac >>
  irule df_iterate_fixpoint_orbit >>
  qexistsl_tac [`K T`, `b`, `m`] >>
  simp[]
QED

(* Corollary of df_iterate_fixpoint_orbit: inflationary + strict measure ⟹ fixpoint. *)
Theorem df_iterate_inflationary_fixpoint_proof:
  !(f : 'a -> 'a) (leq : 'a -> 'a -> bool) (m : 'a -> num) b
   (P : 'a -> bool) x.
    (!y. P y ==> leq y (f y)) /\
    (!y z. leq y z /\ y <> z ==> m y < m z) /\
    P x /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  rpt strip_tac >>
  irule df_iterate_fixpoint_orbit >>
  qexistsl_tac [`P`, `b`, `m`] >>
  rw[] >> `leq y (f y)` by res_tac >>
  `y <> f y` by metis_tac[] >>
  `m y < m (f y)` by res_tac >>
  simp[]
QED

(* Corollary of df_iterate_invariant: same bridge. *)
Theorem df_iterate_inflationary_invariant_proof:
  !(f : 'a -> 'a) (leq : 'a -> 'a -> bool) (m : 'a -> num) b
   (P : 'a -> bool) x.
    (!y. P y ==> leq y (f y)) /\
    (!y z. leq y z /\ y <> z ==> m y < m z) /\
    P x /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    P (df_iterate f x)
Proof
  rpt strip_tac >>
  qspecl_then [`f`, `m`, `b`, `P`, `x`] mp_tac df_iterate_invariant >>
  impl_tac >- (
    rw[] >> `leq y (f y)` by res_tac >>
    `y <> f y` by metis_tac[] >>
    `m y < m (f y)` by res_tac >>
    simp[]) >>
  simp[]
QED

(* WHILE step: df_iterate f x = df_iterate f (f x) when f x ≠ x *)
Theorem df_iterate_step_proof:
  ∀(f : 'a -> 'a) x. f x ≠ x ==> df_iterate f x = df_iterate f (f x)
Proof
  rw[df_iterate_def, Once WHILE]
QED

(* Like fixpoint_orbit, but P holds at f x (not x).
   Useful when init doesn't satisfy P but the first application does. *)
Theorem df_iterate_fixpoint_step:
  !(f : 'a -> 'a) (m : 'a -> num) b (P : 'a -> bool) x.
    (!y. P y /\ f y <> y ==> m (f y) > m y) /\
    P (f x) /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    f (df_iterate f x) = df_iterate f x
Proof
  rpt strip_tac >>
  `f x = x \/ f x <> x` by metis_tac[]
  >- (gvs[df_iterate_def, Once WHILE] >> ONCE_REWRITE_TAC[WHILE] >> gvs[])
  >> `df_iterate f x = df_iterate f (f x)` by
       (irule df_iterate_step_proof >> simp[]) >>
     simp[] >>
     irule df_iterate_fixpoint_orbit >>
     qexistsl_tac [`P`, `b`, `m`] >> simp[]
QED

(* Like invariant, but P holds at f x (not x). *)
Theorem df_iterate_invariant_step:
  !(f : 'a -> 'a) (m : 'a -> num) b (P : 'a -> bool) x.
    (!y. P y /\ f y <> y ==> m (f y) > m y) /\
    P (f x) /\
    (!y. P y ==> m y <= b) /\
    (!y. P y ==> P (f y)) ==>
    P (df_iterate f x)
Proof
  rpt strip_tac >>
  Cases_on `f x = x`
  >- (`df_iterate f x = x` by simp[df_iterate_def, Once WHILE] >>
      gvs[])
  >> `df_iterate f x = df_iterate f (f x)` by
       (irule df_iterate_step_proof >> simp[]) >>
     simp[] >>
     qspecl_then [`f`, `m`, `b`, `P`, `f x`] mp_tac df_iterate_invariant >>
     simp[]
QED
