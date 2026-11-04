Theory dftRecursiveCallObserve
Ancestors
  dftRecursiveCallResidual dftOccurrenceReplay dftOccurrenceResidual
  dftOccurrenceMachine dftOpenMachine unitMemInv contextCodegenRel codegenRel
  venomExecSemantics venomState venomInst list

Theorem dft_cut_data_eval_operand:
  eval_operand op (dft_cut_data s) = eval_operand op s
Proof
  Cases_on `op` >> simp[dft_cut_data_def, eval_operand_def, lookup_var_def]
QED

Theorem dft_cut_data_ranges:
  inst_mem_ranges i (dft_cut_data s) = inst_mem_ranges i s
Proof
  `(dft_cut_data s).vs_call_entry_fmp = s.vs_call_entry_fmp` by
    simp[dft_cut_data_def] >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       fixed_source_write_range_def, sized_source_write_range_def,
       dret_memory_read_ranges_def, dft_cut_data_eval_operand,
       dft_cut_data_eval_operands]
QED

Theorem dft_recursive_active_data:
  dft_cut_data s = dft_cut_data t ==>
  (!op. eval_operand op s = eval_operand op t) /\
  eval_operands ops s = eval_operands ops t /\
  inst_mem_ranges i s = inst_mem_ranges i t /\
  s.vs_memory = t.vs_memory
Proof
  strip_tac >>
  `s.vs_memory = t.vs_memory` by
    (fs[dft_cut_data_def, venom_state_component_equality]) >>
  metis_tac[dft_cut_data_eval_operand, dft_cut_data_eval_operands,
            dft_cut_data_ranges]
QED

Theorem dft_recursive_active_observe:
  get_instruction bb s.vs_inst_idx = SOME i /\
  get_instruction (bm bb) t.vs_inst_idx = SOME i ==>
  dft_open_observe f i s (DftOpen (DftAt f 0 bb s) stackL nL) /\
  dft_open_observe (fm f) i t
    (DftOpen (DftAt (fm f) 0 (bm bb) t) stackR nR)
Proof
  simp[dft_open_observe_def]
QED

Theorem dft_recursive_active_address:
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) stackL nL /\
  r.dft_occ_core = DftOpen (DftAt (fm f) 0 (bm bb) t) stackR nR /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  get_instruction (bm bb) t.vs_inst_idx = SOME j /\
  i.inst_id = j.inst_id /\
  l.dft_occ_path = r.dft_occ_path /\
  l.dft_occ_visit = r.dft_occ_visit ==>
  dft_occ_address l = dft_occ_address r
Proof
  simp[dft_occ_address_def]
QED
