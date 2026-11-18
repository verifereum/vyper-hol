Theory bodyFullAbiDecodeScalarNoAlloca
Ancestors
  bodyPtrBopScalarSeq venomInst list

Theorem abi_decode_scalar_seq_no_alloca:
  !code R A B. bop_scalar_seq R A code B ==>
    EVERY (\i. i.inst_opcode <> ALLOCA) code
Proof
  Induct >- simp[] >>
  rpt gen_tac >> pure_once_rewrite_tac[bop_scalar_seq_def] >> strip_tac >>
  rewrite_tac[EVERY_DEF] >> BETA_TAC >>
  (reverse conj_tac >- metis_tac[]) >>
  gvs[MEM, mk_inst_def]
QED
