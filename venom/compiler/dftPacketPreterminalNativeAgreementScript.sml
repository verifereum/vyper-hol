Theory dftPacketPreterminalNativeAgreement
Ancestors
  dftPacketPreterminalAgreement dftPacketPreterminalGeometry
  dftPacketPreterminalRows dftPacketSuccessfulPrefixTrace
  dftPacketPreterminalOracle dftPacketRetainedOracle
  dftPacketNativeSupplierReplay dftPacketNativePrefixBoundary
  dftGasFromListTraceNames dftStructural dftDefs venomEffects passSharedDefs
  dftGasFromListReadings dftIndexedExec finite_map list rich_list sorting arithmetic

Theorem preterminal_gas_representative[local]:
  from_block [i] y /\ i.inst_opcode = GAS ==> y = i
Proof
  strip_tac >> gvs[from_block_def, is_flippable_def,
    is_commutative_def, is_comparator_def]
QED

Theorem preterminal_source_gas_observed[local]:
  !q.
  xs = ordered ++ [term] /\ ys = executed ++ [term] /\
  LENGTH ordered = LENGTH executed /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) schedule ys /\
  (!r. r < LENGTH ordered ==> MEM r (TAKE (LENGTH executed) schedule)) /\
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_terminator i.inst_opcode) executed /\
  FOLDR (dft_exec_cons fuel C) OK executed be = OK st /\
  EVERY (\kw. MEM kw obs) (trace_gas (trace_block a e fuel C tf
    (bt with bb_instructions := TAKE (LENGTH ps + LENGTH executed) bt.bb_instructions) be)) /\
  q < LENGTH ordered /\ (EL q xs).inst_opcode = GAS ==>
  ?w. MEM ((a,e,(EL q xs).inst_id),w) obs
Proof
  rpt gen_tac >> strip_tac >>
  `MEM q (TAKE (LENGTH executed) schedule)` by metis_tac[] >>
  `?k. k < LENGTH executed /\ k < LENGTH schedule /\ EL k schedule = q` by
    (qpat_x_assum `MEM q (TAKE _ _)`
       (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     `n < LENGTH executed /\ n < LENGTH schedule` by
       (Cases_on `LENGTH executed <= LENGTH schedule` >> fs[LENGTH_TAKE_EQ] >> decide_tac) >>
     qexists_tac `n` >> gvs[EL_TAKE]) >>
  `EL k ys = EL q xs` by
    (qpat_x_assum `LIST_REL _ _ _` (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
     metis_tac[preterminal_gas_representative]) >>
  `MEM (EL q xs) executed` by
    (simp[MEM_EL] >> qexists_tac `k` >>
     qpat_x_assum `EL k ys = _` mp_tac >> simp[EL_APPEND1]) >>
  `?w. MEM ((a,e,(EL q xs).inst_id),w)
    (trace_gas (trace_block a e fuel C tf
      (bt with bb_instructions := TAKE (LENGTH ps + LENGTH executed) bt.bb_instructions) be))` by
    (qpat_assum `be.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
     irule dft_packet_successful_prefix_gas_keys >>
     simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED
