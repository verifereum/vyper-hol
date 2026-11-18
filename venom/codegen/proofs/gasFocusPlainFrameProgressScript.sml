Theory gasFocusPlainFrameProgress
Ancestors
  fnFramePrefixDriver frameJointTrace frameJointTransition frameJointRevert
  asmSem contextCodegenRel venomState venomInst stackPlanGen words list arithmetic

(* Only the planner uses the entry-normalized base. The edge and its
   reachability are still those of the actual joint execution. *)
Theorem focus_plain_frame_progress:
  !rpolicy unit cpl prog vs0 es0 stk PG G tn fn inst s oms om hs h
    ast ev stk' PG' G' tn' fn' inst' t oms' om' hs' h'.
    joint_config_reachable vs0 unit.cu_context
      (JointConfig stk PG G tn fn inst s oms om hs h) /\
    normal_frame_plan rpolicy unit cpl prog
      (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                 vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
    ~in_revert_forward fn s /\
    (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
      source_memory_reads_disjoint cpl inst s /\
      context_source_memory_writes_disjoint cpl inst s) /\
    joint_transition unit.cu_context
      (JointConfig stk PG G tn fn inst s oms om hs h) ev
      (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ==>
    ?n ast'.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog n ast = AsmOK ast' /\
      normal_frame_plan rpolicy unit cpl prog
        (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                   vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
        (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast' /\
      (0 < n \/
       (n = 0 /\ inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
        stk' = stk /\ fn' = fn /\ t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = SUC s.vs_inst_idx /\
        ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
          LENGTH bb.bb_instructions - t.vs_inst_idx <
            LENGTH bb.bb_instructions - s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `v = vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                            vs_return_pc_token := 0w; vs_inst_idx := 0|>` >>
  `(s.vs_call_ctx, s.vs_tx_ctx, s.vs_block_ctx, s.vs_code, s.vs_prev_hashes) =
   (v.vs_call_ctx, v.vs_tx_ctx, v.vs_block_ctx, v.vs_code, v.vs_prev_hashes)` by
    (drule joint_config_readonly >> simp[Abbr `v`]) >>
  drule_all normal_frame_joint_progress_readonly >> disch_then ACCEPT_TAC
QED
