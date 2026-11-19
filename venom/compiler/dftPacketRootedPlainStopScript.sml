Theory dftPacketRootedPlainStop
Ancestors
  dftPacketInvokePrefixStop
  dftPacketOperationalPrefix dftIndexedExec gasEvents
  venomExecSemantics venomInst venomState opcodeClass list arithmetic

Theorem dft_packet_rooted_plain_prefix_stop:
  !F C root_fn root_entry sf bb e u E K k r.
    run_blocks F C root_fn root_entry =
      SND (K (exec_block (F-e) C bb u)) /\
    gas_events_blocks F C root_fn root_entry =
      E ++ gas_events_block (F-e) C sf.fn_name bb u ++
        FST (K (exec_block (F-e) C bb u)) /\
    (!v. K (Halt v) = ([],Halt v)) /\
    (!a v. K (Abort a v) = ([],Abort a v)) /\
    (!msg. K (Error msg) = ([],Error msg)) /\
    u.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (TAKE k (DROP u.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons (F-e) C) OK
      (TAKE k (DROP u.vs_inst_idx bb.bb_instructions)) u = r /\
    ~(?v. r = OK v) ==>
    run_blocks F C root_fn root_entry = r /\
    gas_events_blocks F C root_fn root_entry =
      E ++ gas_events_block (F-e) C sf.fn_name
        (bb with bb_instructions := TAKE (u.vs_inst_idx + k) bb.bb_instructions) u
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP u.vs_inst_idx bb.bb_instructions))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all dft_packet_block_prefix_operational >>
  disch_then (qspecl_then [`F'-e`,`C`,`sf.fn_name`] mp_tac) >>
  simp[] >> strip_tac >>
  drule dft_packet_nonterminator_prefix_no_intret >>
  disch_then (qspecl_then [`F'-e`,`C`,`u`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `r` >> gvs[]
QED
