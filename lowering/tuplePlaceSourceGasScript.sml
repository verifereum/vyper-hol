(* Arbitrary-place writes neither consume nor inspect gas observations. *)
Theory tuplePlaceSourceGas
Ancestors
  vyperState stmtSimAssignStorage stmtSimAugAssignPlaceMemory
  bodyImmutableAugAssignExec

Theorem tuple_place_write_gas_obs:
  write_place cx p v es = (res,ee) ==>
  write_place cx p v (es with gas_obs := gs) =
    (res,ee with gas_obs := gs)
Proof
  Cases_on `p`
  >- simp[write_place_def, write_storage_slot_gas_obs]
  >- metis_tac[aug_place_memory_write_gas_obs]
  >> metis_tac[immutable_write_place_gas_obs]
QED

Theorem tuple_place_write_preserves_gas_obs:
  write_place cx p v es = (res,ee) ==> ee.gas_obs = es.gas_obs
Proof
  strip_tac >>
  drule tuple_place_write_gas_obs >>
  disch_then (qspec_then `es.gas_obs` mp_tac) >>
  simp[] >> strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM `\s. s.gas_obs`) >> simp[]
QED
