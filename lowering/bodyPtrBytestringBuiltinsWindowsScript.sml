(* Positional windows retain records and linkage, unlike set membership. *)
Theory bodyPtrBytestringBuiltinsWindows
Ancestors list

Theorem four_window_append_forward[local]:
  !xs ys a b c d.
  (?p q. xs ++ ys = p ++ [a;b;c;d] ++ q) ==>
  (?p q. xs = p ++ [a;b;c;d] ++ q) \/
  (?p q. ys = p ++ [a;b;c;d] ++ q) \/
  (?p q. xs = p ++ [a] /\ ys = [b;c;d] ++ q) \/
  (?p q. xs = p ++ [a;b] /\ ys = [c;d] ++ q) \/
  (?p q. xs = p ++ [a;b;c] /\ ys = [d] ++ q)
Proof
  Induct_on `xs`
  >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `p` >> gvs[]
  >- (Cases_on `xs`
      >- (gvs[] >> ntac 2 disj2_tac >> disj1_tac >>
          qexists_tac `[]` >> simp[]) >>
      gvs[] >> rename1 `b::t` >> Cases_on `t`
      >- (gvs[] >> ntac 3 disj2_tac >> disj1_tac >>
          qexists_tac `[]` >> simp[]) >>
      gvs[] >> rename1 `c::t` >> Cases_on `t`
      >- (gvs[] >> ntac 4 disj2_tac >>
          qexists_tac `[]` >> simp[]) >>
      gvs[] >> disj1_tac >> qexists_tac `[]` >> simp[]) >>
  first_x_assum (qspec_then `ys` mp_tac) >>
  disch_then (qspecl_then [`a`, `b`, `c`, `d`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> gvs[] >> metis_tac[APPEND]
QED

Theorem four_window_append:
  !xs ys a b c d.
  (?p q. xs ++ ys = p ++ [a;b;c;d] ++ q) <=>
  (?p q. xs = p ++ [a;b;c;d] ++ q) \/
  (?p q. ys = p ++ [a;b;c;d] ++ q) \/
  (?p q. xs = p ++ [a] /\ ys = [b;c;d] ++ q) \/
  (?p q. xs = p ++ [a;b] /\ ys = [c;d] ++ q) \/
  (?p q. xs = p ++ [a;b;c] /\ ys = [d] ++ q)
Proof
  rpt gen_tac >> eq_tac >- metis_tac[four_window_append_forward] >>
  strip_tac >> gvs[] >> metis_tac[APPEND_ASSOC]
QED
