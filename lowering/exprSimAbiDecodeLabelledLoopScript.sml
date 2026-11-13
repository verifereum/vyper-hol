(* Finite iteration retaining a fixed source rejection proposition. *)
Theory exprSimAbiDecodeLabelledLoop
Ancestors
  abiDecoderFiniteControl venomState arithmetic

Theorem decoder_labelled_outcome_prefix:
  Dreach ctx fn s entry /\
  ((?u. Dabort ctx fn entry Revert_abort u /\ Bad) \/
   (?v. Dreach ctx fn entry v /\ Q v)) ==>
  ((?u. Dabort ctx fn s Revert_abort u /\ Bad) \/
   (?v. Dreach ctx fn s v /\ Q v))
Proof
  metis_tac[Dreach_trans, Dreach_abort]
QED

Theorem decoder_finite_loop_labelled:
  (!j s. R j s ==> j <= n) /\
  (!j s. R j s ==> Dreach ctx fn s (H j s) /\ (j = n ==> Q (H j s))) /\
  (!j s. R j s /\ j < n ==>
    ((?u. Dabort ctx fn (H j s) Revert_abort u /\ Bad) \/
     (?v. Dreach ctx fn (H j s) v /\ R (SUC j) v))) ==>
  !j s. R j s ==>
    ((?u. Dabort ctx fn s Revert_abort u /\ Bad) \/
     (?u. Dreach ctx fn s u /\ Q u))
Proof
  strip_tac >>
  `!k j s. n-j = k /\ R j s ==>
    ((?u. Dabort ctx fn s Revert_abort u /\ Bad) \/
     (?u. Dreach ctx fn s u /\ Q u))` suffices_by metis_tac[] >>
  completeInduct_on `k` >> rpt gen_tac >> strip_tac >>
  `j <= n` by metis_tac[] >>
  `Dreach ctx fn s (H j s) /\ (j = n ==> Q (H j s))` by metis_tac[] >>
  Cases_on `j = n` >- metis_tac[] >>
  `j < n` by decide_tac >>
  `(?u. Dabort ctx fn (H j s) Revert_abort u /\ Bad) \/
   (?v. Dreach ctx fn (H j s) v /\ R (SUC j) v)` by metis_tac[]
  >- metis_tac[Dreach_abort] >>
  `n - SUC j < k` by decide_tac >>
  first_x_assum (qspec_then `n - SUC j` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`SUC j`, `v`] mp_tac) >> simp[] >>
  metis_tac[Dreach_trans, Dreach_abort]
QED
