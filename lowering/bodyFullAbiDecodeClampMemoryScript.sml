Theory bodyFullAbiDecodeClampMemory
Ancestors
  bodyPtrBopScalarSeq fragExecMem unitTransformDefs contextCodegenRel
  memSafeRun codegenRel emitHelper venomInst list

Theorem abi_decode_scalar_seq_mem_ok:
  !code R A B s. bop_scalar_seq R A code B ==> run_inst_seq_mem_ok code s
Proof
  qsuff_tac `!code R A B. bop_scalar_seq R A code B ==>
    EVERY (\i. !t. inst_mem_below_frontier i t /\ inst_dload_in_section i t) code`
  >- metis_tac[run_inst_seq_mem_ok_every] >>
  Induct >- simp[] >>
  rpt gen_tac >> pure_once_rewrite_tac[bop_scalar_seq_def] >> strip_tac >>
  rewrite_tac[EVERY_DEF] >> BETA_TAC >>
  (reverse conj_tac >- metis_tac[]) >>
  gen_tac >> gvs[MEM, mk_inst_def] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def]
QED
