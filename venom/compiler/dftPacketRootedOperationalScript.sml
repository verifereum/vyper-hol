Theory dftPacketRootedOperational
Ancestors
  dftPacketClosedRowNative dftPacketRootedCompose dftPacketRowAlignment
  dftAvailability gasEvents venomExecSemantics venomExecProofs
  dftIndexedExec venomInst list rich_list

Theorem dft_packet_run_block_context:
  !fuel C sf entry bb sp u E.
    lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
    eval_phis entry bb.bb_instructions = OK sp /\
    exec_block fuel C bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      exec_block fuel C bb u /\
    gas_events_block fuel C sf.fn_name bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      E ++ gas_events_block fuel C sf.fn_name bb u ==>
    ?K : exec_result -> (string # num) list # exec_result.
      run_blocks (SUC fuel) C sf entry = SND (K (exec_block fuel C bb u)) /\
      gas_events_blocks (SUC fuel) C sf entry =
        E ++ gas_events_block fuel C sf.fn_name bb u ++
          FST (K (exec_block fuel C bb u)) /\
      (!v. K (Halt v) = ([],Halt v)) /\
      (!a v. K (Abort a v) = ([],Abort a v)) /\
      (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[run_blocks_def,gas_events_blocks_def] >> simp[] >>
  qexists_tac `\r. case r of
    OK s => if s.vs_halted then ([],Halt s)
      else (gas_events_blocks fuel C sf s,run_blocks fuel C sf s)
  | other => ([],other)` >>
  simp[] >>
  Cases_on `exec_block fuel C bb u` >> simp[APPEND_ASSOC] >>
  Cases_on `v.vs_halted` >> simp[APPEND_ASSOC]
QED

Theorem dft_packet_invoke_context:
  !fuel C owner bb s c nm ops callee args cs.
    get_instruction bb s.vs_inst_idx = SOME c /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
    ?K : exec_result -> (string # num) list # exec_result.
      exec_block fuel C bb s = SND (K (run_blocks fuel C callee cs)) /\
      gas_events_block fuel C owner bb s =
        gas_events_blocks fuel C callee cs ++ FST (K (run_blocks fuel C callee cs)) /\
      (!v. K (Halt v) = ([],Halt v)) /\
      (!a v. K (Abort a v) = ([],Abort a v)) /\
      (!msg. K (Error msg) = ([],Error msg))
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[exec_block_def,gas_events_block_def] >> simp[] >>
  simp[step_inst_def,gas_events_step_def,is_terminator_def] >>
  qexists_tac `\r. case r of
    IntRet ret child =>
      (case bind_outputs c.inst_outputs ret.iret_values
          (adopt_return_fmp ret (merge_callee_state s child)) of
        NONE => ([],Error "invoke: return arity mismatch")
      | SOME caller =>
          (gas_events_block fuel C owner bb
             (caller with vs_inst_idx := SUC s.vs_inst_idx),
           exec_block fuel C bb
             (caller with vs_inst_idx := SUC s.vs_inst_idx)))
  | OK v => ([],Error "invoke: callee did not return")
  | other => ([],other)` >>
  simp[] >> Cases_on `run_blocks fuel C callee cs` >> simp[] >>
  Cases_on `bind_outputs c.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >> simp[]
QED
