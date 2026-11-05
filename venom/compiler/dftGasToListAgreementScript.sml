Theory dftGasToListAgreement
Ancestors
  dftGasToListTrace list rich_list arithmetic

Definition padded_reading_def:
  padded_reading (ws:bytes32 list) i =
    if i < LENGTH ws then EL i ws else 0w
End

Definition agrees_def:
  agrees (orc:gas_event -> bytes32) ws es <=>
    !i. i < LENGTH es ==> padded_reading ws i = orc (EL i es)
End

Theorem padded_reading_nil[simp]:
  padded_reading [] i = 0w
Proof
  simp[padded_reading_def]
QED

Theorem padded_reading_cons[simp]:
  padded_reading (w::ws) 0 = w /\
  padded_reading (w::ws) (SUC i) = padded_reading ws i
Proof
  simp[padded_reading_def]
QED

Theorem padded_reading_drop:
  !n ws i. padded_reading (DROP n ws) i = padded_reading ws (n+i)
Proof
  Induct >> simp[] >> Cases_on `ws` >>
  simp[ADD_CLAUSES]
QED

Theorem agrees_nil[simp]:
  agrees orc ws []
Proof
  simp[agrees_def]
QED

Theorem agrees_cons:
  agrees orc ws (e::es) <=>
  padded_reading ws 0 = orc e /\ agrees orc (DROP 1 ws) es
Proof
  simp[agrees_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
      simp[padded_reading_drop, ADD1]) >>
  rpt strip_tac >> Cases_on `i` >> gvs[padded_reading_drop, ADD1]
QED

Theorem agrees_append:
  !xs ws ys. agrees orc ws (xs ++ ys) <=>
    agrees orc ws xs /\ agrees orc (DROP (LENGTH xs) ws) ys
Proof
  Induct >> simp[agrees_cons, DROP_DROP_T, ADD_COMM, ADD1] >>
  metis_tac[]
QED

Theorem agrees_map:
  !es. agrees orc (MAP orc es) es
Proof
  Induct >> simp[agrees_cons]
QED

Theorem agrees_zero_tail:
  agrees orc [] es <=> !e. MEM e es ==> orc e = 0w
Proof
  Induct_on `es` >> simp[agrees_cons] >> metis_tac[]
QED
