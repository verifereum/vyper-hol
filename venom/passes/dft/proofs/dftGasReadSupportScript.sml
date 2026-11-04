Theory dftGasReadSupport
Ancestors
  dftGasEventTrace dftTransportAccounting dftOccurrenceGasEdit
  dftOccurrenceMachine dftOpenMachine dftOccurrenceOrdinaryClosure venomInst list

Theorem dft_gas_root_read_support:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id ==>
  dft_transport_read_support w C (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n))
Proof
  strip_tac >> simp[dft_transport_read_support_def] >>
  rpt strip_tac >>
  `?k. dft_occ_gas_event inst addr
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) k
      (dft_occ_init (DftOpen
        (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n)))` by
    (irule dft_gas_orbit_event_forward >> metis_tac[dft_ordinary_sync_init]) >>
  metis_tac[]
QED
