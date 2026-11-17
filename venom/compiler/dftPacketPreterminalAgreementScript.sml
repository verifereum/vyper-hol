Theory dftPacketPreterminalAgreement
Ancestors
  dftPacketPreterminalOracle dftPacketRetainedOracle
  dftPacketNativeSupplierReplay dftPacketNativePrefixBoundary
  dftPacketNativeContinuation dftPacketNativeSlice dftGasFromListTracePrefix
  dftGasFromListReadings dftIndexedExec rich_list list arithmetic

Theorem dft_packet_preterminal_prefix_observations:
  !R N C root_tf root_entry j hbe p d first fn be inst st bt count.
  R = trace_blocks [] 0 N C root_tf root_entry /\
  ALL_DISTINCT (MAP FST R) /\ j < LENGTH R /\ hbe <= j /\
  EL hbe R = ((p,d,first.inst_id),fn,first,be) /\
  EL j R = ((p,d,inst.inst_id),fn,inst,st) /\
  lookup_block be.vs_current_bb fn.fn_blocks = SOME bt /\
  get_instruction bt st.vs_inst_idx = SOME inst /\
  be.vs_inst_idx + count <= LENGTH bt.bb_instructions /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE count (DROP be.vs_inst_idx bt.bb_instructions)) /\
  FOLDR (dft_exec_cons (N-d) C) OK
    (TAKE count (DROP be.vs_inst_idx bt.bb_instructions)) be = OK st ==>
  EVERY (\kw. MEM kw (trace_gas (TAKE j R)))
    (trace_gas (trace_block p d (N-d) C fn
      (bt with bb_instructions := TAKE (be.vs_inst_idx + count) bt.bb_instructions) be))
Proof
  rpt gen_tac >> strip_tac >>
  `hbe < LENGTH R` by decide_tac >>
  `?rest. R = TAKE hbe R ++ trace_block p d (N-d) C fn bt be ++ rest` by
    (qpat_assum `hbe < LENGTH R` mp_tac >>
     qpat_assum `EL hbe R = _` mp_tac >>
     qpat_assum `lookup_block be.vs_current_bb fn.fn_blocks = SOME bt` mp_tac >>
     qpat_assum `R = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
     drule_all native_trace_blocks_continuation >> strip_tac >> gvs[] >>
     metis_tac[TAKE_DROP, APPEND_ASSOC]) >>
  `hbe <= LENGTH R` by decide_tac >>
  drule_all native_trace_embedded_prefix_cut >> strip_tac >>
  gvs[trace_gas_append, EVERY_MEM]
QED
