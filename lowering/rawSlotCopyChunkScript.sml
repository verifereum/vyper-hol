(* A concrete straight run and its taken branch, before imposing any exit cut. *)
Theory rawSlotCopyChunk
Ancestors
  fragExecMem exprLoweringProps ptrDiscipline unitTransformDefs venomState
  venomExecSemantics venomInst list rich_list arithmetic

Definition slot_copy_chunk_def:
  slot_copy_chunk loId hiId ctx f s r <=>
    ?bb code u t i lbl.
      ~s.vs_halted /\
      lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
      isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
      EVERY (\i. loId <= i.inst_id /\ i.inst_id < hiId /\
        i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
        ~is_terminator i.inst_opcode) code /\
      run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s /\
      (!pre j post v. code = pre ++ j::post /\ run_inst_seq pre s = OK v /\
        ctx_has_dalloca ctx ==> dalloca_no_wrap j v) /\
      t = u with vs_inst_idx := s.vs_inst_idx + LENGTH code /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      loId <= i.inst_id /\ i.inst_id < hiId /\
      (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
      step_inst_base i t = OK (jump_to lbl t) /\ r = jump_to lbl t
End

Theorem slot_copy_chunk_jump:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  loId <= i.inst_id /\ i.inst_id < hiId /\
  (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
  step_inst_base i s = OK (jump_to lbl s) ==>
  slot_copy_chunk loId hiId ctx f s (jump_to lbl s)
Proof
  strip_tac >> pure_rewrite_tac[slot_copy_chunk_def] >>
  qexistsl_tac [`bb`, `[]`, `s`, `s`, `i`, `lbl`] >>
  simp[run_inst_seq_def, run_inst_seq_mem_ok_def]
QED

Theorem slot_copy_chunk_mono:
  loId' <= loId /\ hiId <= hiId' /\ slot_copy_chunk loId hiId ctx f s r ==>
  slot_copy_chunk loId' hiId' ctx f s r
Proof
  pure_rewrite_tac[slot_copy_chunk_def] >> strip_tac >>
  qexistsl_tac [`bb`, `code`, `u`, `t`, `i`, `lbl`] >>
  simp[] >> gvs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED
