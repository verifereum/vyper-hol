Theory dftGasInvContractBoundary
Ancestors
  dftRunRel ctxLookupAgreeHelpers dftGasInvAllocationProbe venomInst list

Theorem inv_dft_fn_rel_block_no_alloca:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions` by
    (irule EVERY_fn_block >> qexists_tac `fn` >>
     gvs[dft_fn_rel_def]) >>
  fs[EVERY_MEM] >> rw[EVERY_MEM] >>
  `i.inst_opcode <> ALLOCA` by metis_tac[] >>
  Cases_on `i.inst_opcode` >> gvs[is_alloca_op_def]
QED

Theorem inv_alloc_probe_outside_contract:
  ~dft_fn_rel inv_alloc_probe_fn fn'
Proof
  simp[dft_fn_rel_def, inv_alloc_probe_fn_def, inv_alloc_use_probe_def,
       mk_raw_function_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def]
QED
