(* TOP-LEVEL: exact scratch-request profiles for concrete mixed fields.
   Profiles permit sufficiently large cached records and ignore allocations
   belonging to code outside the current ABI traversal. *)
Theory abiFieldRequests
Ancestors
  abiFieldDefs abiFlatIdCost abiAllocationFresh abiAllocationFrame compileEnv venomState list pair arithmetic

Definition abi_field_id_cost_def:
  abi_field_id_cost (AbiFieldFlat row) = abi_flat_id_cost row /\
  abi_field_id_cost (AbiFieldDynBytes ty tv capacity vs bss) = 54
End

Definition abi_field_requests_def:
  abi_field_requests next_id [] = [] /\
  abi_field_requests next_id (AbiFieldFlat row::rest) =
    abi_field_requests (next_id + abi_flat_id_cost row) rest /\
  abi_field_requests next_id (AbiFieldDynBytes ty tv capacity vs bss::rest) =
    [(next_id + 4,32);(next_id + 8,32);(next_id + 10,32)] ++ abi_field_requests (next_id + 54) rest
End

Theorem abi_field_requests_sizes:
  !rows next_id. EVERY (\request. SND request = 32) (abi_field_requests next_id rows)
Proof
  Induct_on `rows` >- simp[abi_field_requests_def] >> qx_gen_tac `row` >> Cases_on `row` >> simp[abi_field_requests_def]
QED

Theorem abi_field_requests_cons:
  !row rest next_id.
    abi_field_requests next_id (row::rest) =
      abi_field_requests next_id [row] ++
      abi_field_requests (next_id + abi_field_id_cost row) rest
Proof
  Cases_on `row` >> simp[abi_field_requests_def, abi_field_id_cost_def]
QED

Theorem abi_field_requests_ids:
  !rows next_id lower_id. lower_id <= next_id ==>
    EVERY (\request. lower_id <= FST request) (abi_field_requests next_id rows)
Proof
  Induct_on `rows` >- simp[abi_field_requests_def] >> qx_gen_tac `row` >> Cases_on `row` >> rpt gen_tac >> DISCH_TAC >>
  simp_tac (srw_ss()) [abi_field_requests_def] >> rpt conj_tac >>
  FIRST [decide_tac, first_x_assum irule >> decide_tac]
QED

Theorem abi_field_requests_fresh:
  !rows next_id ss. abi_allocation_fresh next_id ss ==>
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) ss) (abi_field_requests next_id rows)
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`rows`, `next_id`, `next_id`] abi_field_requests_ids) >> simp[] >> DISCH_TAC >>
  simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `request` >> DISCH_TAC >>
  `next_id <= FST request` by fs[EVERY_MEM] >>
  mp_tac (Q.SPECL [`next_id`, `ss`, `FST (request:num # num)`, `SND (request:num # num)`] abi_allocation_fresh_request) >> simp[]
QED
