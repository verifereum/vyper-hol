(* Actual byte observations of the private CODECOPY scratch region. *)
Theory lowerDloadScratchBytes
Ancestors
  lowerDloadSafetyBytes venomExecSemantics regularCallEmitSim venomMemProps
  venomState list rich_list words byte

Theorem ld_read_memory_written:
  read_memory off (LENGTH bytes) (write_memory_with_expansion off bytes s) = bytes
Proof
  irule LIST_EQ >> simp[ld_read_memory_byte] >>
  rpt strip_tac >> simp[read_byte_write_memory_with_expansion]
QED

Theorem ld_codecopy_mload:
  inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dst; src; Lit 32w] /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  step_inst 0 C inst s = OK t ==>
  mload (w2n dw) t =
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n sw) s.vs_code ++ REPLICATE 32 0w))
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, eval_operand_def] >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[dimword_def] >>
  `!off s. mload off s = word_of_bytes T (0w:bytes32) (read_memory off 32 s)` by
    simp[mload_def, read_memory_def] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion off bytes s` >>
  `LENGTH bytes = 32` by simp[Abbr `bytes`] >>
  metis_tac[ld_read_memory_written]
QED

Theorem ld_codecopy_byte_outside:
  inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dst; src; sz] /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand sz s = SOME nw /\ step_inst 0 C inst s = OK t /\
  ~(w2n dw <= i /\ i < w2n dw + w2n nw) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def] >>
  irule write_memory_byte_frame >>
  qexists_tac `w2n nw` >> simp[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "scratch byte theorem has hypotheses")
  [ld_read_memory_written, ld_codecopy_mload, ld_codecopy_byte_outside];
