(*
 * Straight-line fragments: a successful run, recovered through a SINK
 * observer block.
 *
 * TOP-LEVEL:
 *   frag_exec_straight_run
 *
 * Helpers: halt_state_injective_nonhalted, synthetic_sink_endpoint,
 *   step_inst_base_nonterminator_no_exit, drop_cons_instruction,
 *   exec_block_sink_converse, run_inst_seq_preserves_entry_control,
 *   exec_block_sink_not_ok.
 *)
Theory entrySinkExtraction
Ancestors
  fragExec abiDecodeStaticProps venomExecProofs venomInstProofs
  exprLoweringProps venomExecSemantics venomInst venomState list rich_list
  instIdxIndep

Theorem halt_state_injective_nonhalted:
  !s t. ~s.vs_halted /\ ~t.vs_halted /\ halt_state s = halt_state t ==>
    s = t
Proof
  cheat
QED

Theorem synthetic_sink_endpoint:
  !fuel ctx fn lbl pre id s.
    s.vs_current_bb = lbl /\ s.vs_inst_idx = LENGTH pre ==>
    run_from fuel ctx
      (fn with fn_blocks :=
        [<| bb_label := lbl;
            bb_instructions := pre ++ [mk_inst id SINK [] []] |>]) s =
    Halt (halt_state s)
Proof
  cheat
QED

Theorem step_inst_base_nonterminator_no_exit:
  !i s. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode ==>
    (!h. step_inst_base i s <> Halt h) /\
    (!v t. step_inst_base i s <> IntRet v t)
Proof
  cheat
QED

Theorem drop_cons_instruction[local]:
  !l n i rest. DROP n l = i::rest ==>
    n < LENGTH l /\ EL n l = i /\ DROP (SUC n) l = rest
Proof
  cheat
QED

Theorem exec_block_sink_converse:
  !is s bb fuel ctx id h.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    DROP s.vs_inst_idx bb.bb_instructions = is ++ [mk_inst id SINK [] []] /\
    exec_block fuel ctx bb s = Halt h ==>
    ?u. run_inst_seq is s = OK u /\
        h = halt_state (u with vs_inst_idx := s.vs_inst_idx + LENGTH is)
Proof
  cheat
QED

Theorem run_inst_seq_preserves_entry_control:
  !is s t.
    run_inst_seq is s = OK t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
    t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb
Proof
  cheat
QED

Theorem exec_block_sink_not_ok:
  !is s bb fuel ctx id v.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    DROP s.vs_inst_idx bb.bb_instructions = is ++ [mk_inst id SINK [] []] ==>
    exec_block fuel ctx bb s <> OK v
Proof
  cheat
QED

Theorem frag_exec_straight_run:
  !ctx st st' P Q s.
    dec_straight st st' /\ frag_exec ctx st st' P Q (\r. F) /\
    P s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?u. run_inst_seq (emitted_insts st st') s = OK u /\
        Q (u with vs_inst_idx := LENGTH st'.cs_current_insts) /\
        ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
        u.vs_prev_bb = s.vs_prev_bb
Proof
  cheat
QED
