(* Observe concrete successful segments without importing an entry simulation. *)
Theory restoreSegmentLaws
Ancestors
  fragGasOrigin fragExec venomExecSemantics venomInst venomState
  arithmetic list rich_list pair

Definition restore_segment_laws_def:
  restore_segment_laws lo hi exit explicit ctx fn R <=>
    (!s. R s s) /\
    (!s u t. R s u /\ R u t ==> R s t) /\
    (!code s bb t.
      ~s.vs_halted /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
      EVERY (\i. lo <= i.inst_id /\ i.inst_id < hi /\
        i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
        ~is_terminator i.inst_opcode) code /\
      (!j. j < LENGTH code ==> (s.vs_current_bb,s.vs_inst_idx + j) <> exit) /\
      run_inst_seq code s = OK t ==>
      R s (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    (!s bb i t.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME i /\
      lo <= i.inst_id /\ i.inst_id < hi /\
      (s.vs_current_bb,s.vs_inst_idx) <> exit /\
      gas_origin_edge F explicit ctx fn s [] (OK t) ==>
      R s t)
End

Theorem restore_segment_laws_true:
  restore_segment_laws lo hi exit explicit ctx fn (\s t. T)
Proof
  simp[restore_segment_laws_def]
QED

Theorem restore_segment_laws_restrict_start:
  lo <= mid /\ restore_segment_laws lo hi exit explicit ctx fn R ==>
  restore_segment_laws mid hi exit explicit ctx fn R
Proof
  pure_rewrite_tac[restore_segment_laws_def] >> strip_tac >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!code s bb t. ~s.vs_halted /\ _ ==> _`
        (qspecl_then [`code`,`s`,`bb`,`t`] irule) >>
      asm_rewrite_tac[] >>
      fs[EVERY_MEM] >> gen_tac >> disch_tac >>
      qpat_assum `!j. MEM j code ==> _` (drule_then strip_assume_tac) >>
      asm_rewrite_tac[] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!s bb i t. lookup_block _ _ = SOME bb /\ _ ==> _`
    (qspecl_then [`s`,`bb`,`i`,`t`] irule) >>
  asm_rewrite_tac[] >> qexistsl_tac [`bb`,`i`] >>
  asm_rewrite_tac[] >> decide_tac
QED
