Theory dftPacketCallFreshCaller
Ancestors
  dftPacketPreterminalAgreement dftPacketPreterminalRows dftPacketRetainedOracle
  dftGasFromListTraceNames dftContractGas dftWf dftGasInvCallerExtract
  dftRunRel venomWf list rich_list finite_map arithmetic

(* The entire visit-name distinctness required by the embedding lemma comes
   from context well-formedness, not from distinctness of GAS observations. *)
Theorem dft_packet_call_target_prefix_covered:
  !N C root_tf root_entry j hbe p d fn be inst s bt ps ys cnt obs.
  o1_ctx_shape C /\ MEM root_tf C.ctx_functions /\
  j < LENGTH (trace_blocks [] 0 N C root_tf root_entry) /\ hbe <= j /\
  EL hbe (trace_blocks [] 0 N C root_tf root_entry) =
    ((p,d,(HD ys).inst_id),fn,HD ys,be) /\
  EL j (trace_blocks [] 0 N C root_tf root_entry) =
    ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C root_tf root_entry)) /\
  lookup_block be.vs_current_bb fn.fn_blocks = SOME bt /\
  get_instruction bt s.vs_inst_idx = SOME inst /\
  bt.bb_instructions = ps ++ ys /\ bb_well_formed bt /\
  be.vs_inst_idx = LENGTH ps /\ cnt < LENGTH ys /\
  FOLDR (dft_exec_cons (N-d) C) OK (TAKE cnt ys) be = OK s ==>
  EVERY (\kw. MEM kw obs)
    (trace_gas (trace_block p d (N-d) C fn
      (bt with bb_instructions := TAKE (LENGTH ps + cnt) bt.bb_instructions) be))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by metis_tac[o1_ctx_shape_wf_functions] >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
      f.fn_blocks) C.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) root_tf.fn_blocks` by
    (gvs[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C root_tf root_entry))` by
    (irule (cj 3 trace_names_distinct) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE cnt ys)` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `cnt < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[bb_well_formed_def] >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  qpat_x_assum `obs = _` SUBST1_TAC >>
  qpat_assum `be.vs_inst_idx = LENGTH ps`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule dft_packet_preterminal_prefix_observations >>
  simp[DROP_APPEND] >> metis_tac[]
QED
