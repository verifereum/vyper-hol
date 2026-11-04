Theory dftOrdinaryReadSupport
Ancestors
  dftOrdinaryEventTrace dftTransportAccounting dftOriginalOrbit
  dftOriginalRuntime dftOccurrenceMachine dftOpenMachine
  dftOccurrenceGasEdit

(* Ordinary edits match every GAS instruction and address, independently of
   the value assigned by the fixed occurrence oracle. *)
Theorem dft_original_ordinary_root_read_support:
  dft_original_ordinary_environment Corig C s.vs_labels q pre x y post /\
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions ==>
  dft_transport_read_support w C (dft_gas_edit_ctx q pre x y post C)
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))
Proof
  strip_tac >> drule_all dft_original_ordinary_root_gas_support >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  simp[dft_transport_read_support_def] >> metis_tac[]
QED
