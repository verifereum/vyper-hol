Theory dftPacketFreshChildStop
Ancestors
  dftPacketInvokePrefixStop
  dftPacketRootedOperational dftPacketOperationalPrefix
  dftIndexedExec gasEvents venomExecSemantics list rich_list arithmetic

Theorem dft_packet_fresh_child_root_stop:
  !fuel C root_sf root_entry sf bb u e E
    (K : exec_result -> (string # num) list # exec_result)
    c nm ops callee args child_entry cb sp k r.
    run_blocks fuel C root_sf root_entry = SND (K (exec_block (fuel-e) C bb u)) /\
    gas_events_blocks fuel C root_sf root_entry =
      E ++ gas_events_block (fuel-e) C sf.fn_name bb u ++
        FST (K (exec_block (fuel-e) C bb u)) /\
    (!v. K (Halt v) = ([],Halt v)) /\
    (!a v. K (Abort a v) = ([],Abort a v)) /\
    (!msg. K (Error msg) = ([],Error msg)) /\
    get_instruction bb u.vs_inst_idx = SOME c /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops u = SOME args /\ setup_callee callee args u = SOME child_entry /\
    lookup_block child_entry.vs_current_bb callee.fn_blocks = SOME cb /\
    eval_phis child_entry cb.bb_instructions = OK sp /\ e < fuel /\
    phi_prefix_length cb.bb_instructions + k <= LENGTH cb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (TAKE k (DROP (phi_prefix_length cb.bb_instructions) cb.bb_instructions)) /\
    FOLDR (dft_exec_cons (fuel-SUC e) C) OK
      (TAKE k (DROP (phi_prefix_length cb.bb_instructions) cb.bb_instructions))
      (sp with vs_inst_idx := phi_prefix_length cb.bb_instructions) = r /\
    ~(?t. r = OK t) ==>
    run_blocks fuel C root_sf root_entry = r /\
    gas_events_blocks fuel C root_sf root_entry = E ++
      gas_events_block (fuel-SUC e) C callee.fn_name
        (cb with bb_instructions := TAKE (phi_prefix_length cb.bb_instructions + k)
          cb.bb_instructions)
        (sp with vs_inst_idx := phi_prefix_length cb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  `fuel-e = SUC (fuel-SUC e)` by decide_tac >>
  drule_all dft_packet_invoke_context >>
  disch_then (qspecl_then [`fuel-e`,`sf.fn_name`]
    (qx_choose_then `J` strip_assume_tac)) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP (phi_prefix_length cb.bb_instructions) cb.bb_instructions))` by
    fs[EVERY_CONJ] >>
  `!ir t. r <> IntRet ir t` by
    (drule dft_packet_nonterminator_prefix_no_intret >> metis_tac[]) >>
  `exec_block (fuel-SUC e) C cb
      (sp with vs_inst_idx := phi_prefix_length cb.bb_instructions) = r /\
   gas_events_block (fuel-SUC e) C callee.fn_name cb
      (sp with vs_inst_idx := phi_prefix_length cb.bb_instructions) =
   gas_events_block (fuel-SUC e) C callee.fn_name
      (cb with bb_instructions := TAKE (phi_prefix_length cb.bb_instructions + k)
        cb.bb_instructions)
      (sp with vs_inst_idx := phi_prefix_length cb.bb_instructions)` by
    (qspecl_then [`(fuel:num)-SUC e`,`C`,`callee.fn_name`,`cb`,
       `sp with vs_inst_idx := phi_prefix_length cb.bb_instructions`,`k`]
       mp_tac dft_packet_block_prefix_operational >>
     simp[] >> metis_tac[]) >>
  `run_blocks (fuel-e) C callee child_entry = r /\
   gas_events_blocks (fuel-e) C callee child_entry =
     gas_events_block (fuel-SUC e) C callee.fn_name cb
       (sp with vs_inst_idx := phi_prefix_length cb.bb_instructions)` by
    (asm_rewrite_tac[] >>
     once_rewrite_tac[run_blocks_def,gas_events_blocks_def] >>
     simp[] >> Cases_on `r` >> gvs[]) >>
  Cases_on `r` >> gvs[]
QED
