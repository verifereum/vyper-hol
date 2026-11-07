(* History, room and memory continuations for exact instruction sequences. *)
Theory entrySequenceMemResources
Ancestors
  intCallCallee allocaHistoryFragment fragExecMem exprLoweringProps list

Theorem entry_sequence_resources:
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  alloca_room ctx func s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = is ++ rest /\
  EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) is /\
  run_inst_seq is s = OK u /\ run_inst_seq_mem_ok is s ==>
  let t = u with vs_inst_idx := s.vs_inst_idx + LENGTH is in
    alloca_history func t /\ alloca_room ctx func t /\
    ((!fuel. mem_safe_run fuel ctx func t) ==>
     !fuel. mem_safe_run fuel ctx func s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  `EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE) is`
    by fs[EVERY_MEM] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is`
    by fs[EVERY_MEM] >>
  conj_tac
  >- (irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `u` >> simp[] >>
      drule_all run_inst_seq_alloca_room >> simp[]) >>
  strip_tac >> gen_tac >>
  `isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all mem_safe_run_inst_seq >> strip_tac >>
  first_x_assum (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qpat_x_assum `!s'. run_inst_seq _ _ = OK _ /\ _ ==> _` irule >>
  qexists_tac `u` >> simp[]
QED
