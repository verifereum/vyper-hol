(* Representation-independent agreement on temporally demanded observations.
 * Producers may read the pre-state, so simultaneous/overlapping copies
 * need not be decomposed into sequential updates. *)
Theory frameRelocationDemand
Ancestors
  bool

Definition demand_agree_def:
  demand_agree R m t <=> !a b. R a b ==> m a = t b
End

Theorem demand_agree_identity:
  (!a b. R a b ==> a = b) ==> demand_agree R m m
Proof
  simp[demand_agree_def] >> metis_tac[]
QED

Theorem demand_agree_restrict:
  demand_agree R m t /\ (!a b. next a b ==> R a b) ==>
  demand_agree next m t
Proof
  simp[demand_agree_def] >> metis_tac[]
QED

Theorem demand_agree_update:
  demand_agree R m t /\
  (!a b. next a b /\ writes a ==> V a = t' b) /\
  (!a b. next a b /\ ~writes a ==> R a b /\ ~writesT b) /\
  (!a. m' a = if writes a then V a else m a) /\
  (!b. ~writesT b ==> t' b = t b) ==>
  demand_agree next m' t'
Proof
  rw[demand_agree_def] >> Cases_on `writes a` >> metis_tac[]
QED

Theorem demand_agree_producer_update:
  demand_agree R m t /\
  (!a b. next a b /\ writes a ==> writesT b /\ V a = VT b) /\
  (!a b. next a b /\ ~writes a ==> R a b /\ ~writesT b) /\
  (!a. m' a = if writes a then V a else m a) /\
  (!b. writesT b ==> t' b = VT b) /\
  (!b. ~writesT b ==> t' b = t b) ==>
  demand_agree next m' t'
Proof
  strip_tac >> irule demand_agree_update >>
  qexistsl [`R`, `V`, `m`, `t`, `writes`, `writesT`] >>
  metis_tac[]
QED
