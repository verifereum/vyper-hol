Theory dftPacketInvokePrefixStop
Ancestors
  dftPacketOperationalPrefix dftRunRel
  dftIndexedExec gasEvents venomExecSemantics venomInst venomState
  opcodeClass list arithmetic

Theorem dft_packet_nonterminator_prefix_no_intret:
  !xs f C s.
    EVERY (\i. ~is_terminator i.inst_opcode) xs ==>
    !ir t. FOLDR (dft_exec_cons f C) OK xs s <> IntRet ir t
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  simp[dft_exec_cons_def] >>
  `!ir t. step_inst f C h s <> IntRet ir t` by
    metis_tac[dft_swap_nonterminator_no_intret] >>
  Cases_on `step_inst f C h s` >> simp[]
QED

Theorem dft_packet_invoke_prefix_stop:
  !f C root_fn root_entry sf bb e u E K k r.
    run_blocks f C root_fn root_entry = SND (K (exec_block (f-e) C bb u)) /\
    gas_events_blocks f C root_fn root_entry =
      E ++ gas_events_block (f-e) C sf.fn_name bb u ++
        FST (K (exec_block (f-e) C bb u)) /\
    (!v. K (Halt v) = ([],Halt v)) /\
    (!a v. K (Abort a v) = ([],Abort a v)) /\
    (!msg. K (Error msg) = ([],Error msg)) /\
    u.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP u.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons (f-e) C) OK
      (TAKE k (DROP u.vs_inst_idx bb.bb_instructions)) u = r /\
    ~(?v. r = OK v) ==>
    run_blocks f C root_fn root_entry = r /\
    gas_events_blocks f C root_fn root_entry =
      E ++ gas_events_block (f-e) C sf.fn_name
        (bb with bb_instructions := TAKE (u.vs_inst_idx+k) bb.bb_instructions) u
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_block_prefix_operational >>
  disch_then (qspecl_then [`f-e`,`C`,`sf.fn_name`] mp_tac) >>
  simp[] >> strip_tac >>
  `!ir t. r <> IntRet ir t` by
    metis_tac[dft_packet_nonterminator_prefix_no_intret] >>
  Cases_on `r` >> gvs[]
QED
