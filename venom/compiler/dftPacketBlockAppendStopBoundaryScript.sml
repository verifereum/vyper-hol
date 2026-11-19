Theory dftPacketBlockAppendStopBoundary
Ancestors
  dftPacketInvokePrefixStop
  dftPacketRootedOperational dftPacketRootedPlainStop dftPacketOperationalPrefix
  venomExecSemantics venomInst venomState dftIndexedExec gasEvents list arithmetic

Theorem dft_packet_block_body_error_stop:
  !fuel C root_fn root_input sf bb d u0 E0 K msg.
    run_blocks fuel C root_fn root_input =
      SND (K (exec_block (fuel-d) C bb u0)) /\
    gas_events_blocks fuel C root_fn root_input =
      E0 ++ gas_events_block (fuel-d) C sf.fn_name bb u0 ++
        FST (K (exec_block (fuel-d) C bb u0)) /\
    K (Error msg) = ([],Error msg) /\
    exec_block (fuel-d) C bb u0 = Error msg ==>
    run_blocks fuel C root_fn root_input = Error msg /\
    gas_events_blocks fuel C root_fn root_input =
      E0 ++ gas_events_block (fuel-d) C sf.fn_name bb u0
Proof
  rpt strip_tac >> gvs[]
QED

Theorem dft_packet_block_fresh_prefix_stop:
  !fuel C root_fn root_input sf d v E K bb1 sp1 s1 k r.
    d < fuel /\
    run_blocks fuel C root_fn root_input =
      SND (K (run_blocks (fuel-d) C sf v)) /\
    gas_events_blocks fuel C root_fn root_input =
      E ++ gas_events_blocks (fuel-d) C sf v ++
        FST (K (run_blocks (fuel-d) C sf v)) /\
    (!w. K (Halt w) = ([],Halt w)) /\
    (!a w. K (Abort a w) = ([],Abort a w)) /\
    (!msg. K (Error msg) = ([],Error msg)) /\
    lookup_block v.vs_current_bb sf.fn_blocks = SOME bb1 /\
    eval_phis v bb1.bb_instructions = OK sp1 /\
    s1 = sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions /\
    s1.vs_inst_idx + k < LENGTH bb1.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (TAKE k (DROP s1.vs_inst_idx bb1.bb_instructions)) /\
    FOLDR (dft_exec_cons (fuel-SUC d) C) OK
      (TAKE k (DROP s1.vs_inst_idx bb1.bb_instructions)) s1 = r /\
    ~(?w. r = OK w) ==>
    run_blocks fuel C root_fn root_input = r /\
    gas_events_blocks fuel C root_fn root_input =
      E ++ gas_events_block (fuel-SUC d) C sf.fn_name
        (bb1 with bb_instructions := TAKE (s1.vs_inst_idx + k) bb1.bb_instructions) s1
Proof
  rpt gen_tac >> strip_tac >>
  `fuel-d = SUC (fuel-SUC d)` by decide_tac >>
  `?J : exec_result -> (string # num) list # exec_result.
    run_blocks (SUC (fuel-SUC d)) C sf v =
      SND (J (exec_block (fuel-SUC d) C bb1 s1)) /\
    gas_events_blocks (SUC (fuel-SUC d)) C sf v =
      [] ++ gas_events_block (fuel-SUC d) C sf.fn_name bb1 s1 ++
        FST (J (exec_block (fuel-SUC d) C bb1 s1)) /\
    (!w. J (Halt w) = ([],Halt w)) /\
    (!a w. J (Abort a w) = ([],Abort a w)) /\
    (!msg. J (Error msg) = ([],Error msg))` by
    (irule dft_packet_run_block_context >> simp[]) >>
  `run_blocks (SUC (fuel-SUC d)) C sf v = r /\
   gas_events_blocks (SUC (fuel-SUC d)) C sf v =
     [] ++ gas_events_block (fuel-SUC d) C sf.fn_name
       (bb1 with bb_instructions := TAKE (s1.vs_inst_idx + k) bb1.bb_instructions) s1` by
    (irule (GEN_ALL (REWRITE_RULE [SUC_SUB1] (Q.INST [`e` |-> `1`]
      (SPEC_ALL (Q.SPEC `SUC (fuel-SUC d)` dft_packet_rooted_plain_prefix_stop))))) >>
     simp[] >> conj_tac >- metis_tac[] >>
     conj_tac >- (gvs[] >> decide_tac) >>
     qexists_tac `J` >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP s1.vs_inst_idx bb1.bb_instructions))` by
    fs[EVERY_CONJ] >>
  drule dft_packet_nonterminator_prefix_no_intret >>
  disch_then (qspecl_then [`fuel-SUC d`,`C`,`s1`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `r` >> gvs[]
QED
