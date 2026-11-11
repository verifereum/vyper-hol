Theory finiteByteDemand
Ancestors arithmetic pred_set

(* Indexed read observations precede the writes of the same edge.
   No execution relation or choice of operational projections is imposed. *)
Definition finite_byte_demand_def:
  finite_byte_demand R writes n N byte <=>
    ?j. n <= j /\ j <= N /\ byte IN R j /\
        (!k. n <= k /\ k < j ==> byte NOTIN writes k)
End

Theorem finite_byte_demand_endpoint:
  finite_byte_demand R writes N N byte <=> byte IN R N
Proof
  simp[finite_byte_demand_def] >> eq_tac
  >- (strip_tac >> `j = N` by decide_tac >> gvs[]) >>
  strip_tac >> qexists_tac `N` >> simp[]
QED

Theorem finite_byte_demand_unfold:
  n < N ==>
  (finite_byte_demand R writes n N byte <=>
   byte IN R n \/ (byte NOTIN writes n /\ finite_byte_demand R writes (SUC n) N byte))
Proof
  strip_tac >> simp[finite_byte_demand_def] >> eq_tac
  >- (strip_tac >> Cases_on `j = n` >- gvs[] >>
      disj2_tac >> conj_tac >- (first_x_assum irule >> simp[]) >>
      qexists_tac `j` >>
      `SUC n <= j` by decide_tac >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  strip_tac
  >- (qexists_tac `n` >> simp[]) >>
  qexists_tac `j` >> simp[] >>
  rpt strip_tac >> Cases_on `k = n` >- gvs[] >>
  qpat_x_assum `!k. SUC n <= k /\ k < j ==> _`
    (qspec_then `k` mp_tac) >> simp[]
QED

Theorem finite_byte_demand_extend:
  finite_byte_demand R writes n N byte /\ N <= M ==>
  finite_byte_demand R writes n M byte
Proof
  simp[finite_byte_demand_def] >> rpt strip_tac >>
  qexists_tac `j` >> simp[] >> decide_tac
QED

Theorem finite_byte_demand_witness_protected:
  n < j /\ (!k. n <= k /\ k < j ==> byte NOTIN writes k) ==>
  byte NOTIN writes n
Proof
  rpt strip_tac >> first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED
