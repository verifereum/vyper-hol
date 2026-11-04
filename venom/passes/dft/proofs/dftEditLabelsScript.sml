Theory dftEditLabels
Ancestors
  dftOccurrenceGasEdit dftRunRel o1PassContract venomInst list

Theorem dft_gas_edit_block_insts_mem:
  q.bb_instructions = pre ++ [x;y] ++ post ==>
  (MEM i (dft_gas_edit_block q pre x y post b).bb_instructions <=>
   MEM i b.bb_instructions)
Proof
  strip_tac >> Cases_on `b = q` >> gvs[dft_gas_edit_block_def] >>
  metis_tac[]
QED

Theorem dft_gas_edit_fn_insts_mem:
  q.bb_instructions = pre ++ [x;y] ++ post ==>
  (MEM i (fn_insts (dft_gas_edit_fn q pre x y post fn)) <=>
   MEM i (fn_insts fn))
Proof
  strip_tac >> simp[fn_insts_def, fn_insts_blocks_MEM,
    dft_gas_edit_fn_def, MEM_MAP] >>
  metis_tac[dft_gas_edit_block_insts_mem]
QED

Theorem dft_gas_edit_ctx_labels_bound:
  q.bb_instructions = pre ++ [x;y] ++ post /\ ctx_labels_bound C L ==>
  ctx_labels_bound (dft_gas_edit_ctx q pre x y post C) L
Proof
  simp[ctx_labels_bound_def, dft_gas_edit_ctx_def, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[dft_gas_edit_fn_insts_mem]
QED
