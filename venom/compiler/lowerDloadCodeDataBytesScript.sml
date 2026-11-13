(* Source data observations through the relocated code offset. *)
Theory lowerDloadCodeDataBytes
Ancestors
  lowerDloadScratchBytes lowerDloadDefs venomExecSemantics venomInst venomState list rich_list words
  finite_map byte arithmetic

Theorem ld_code_data_bytes:
  code_layout_valid s /\
  eval_operand (Label "code_end") s = SOME basew /\
  w2n off + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword (:256)
  ==>
  TAKE n (DROP (w2n (off + basew)) s.vs_code ++ REPLICATE n 0w) =
  TAKE n (DROP (w2n off) s.vs_data_section ++ REPLICATE n 0w)
Proof
  strip_tac >> gvs[code_layout_valid_def, eval_operand_def] >>
  `off = n2w (w2n off)` by simp[] >>
  once_asm_rewrite_tac[] >>
  simp[word_add_n2w, ADD_COMM, DROP_APPEND2]
QED

Theorem ld_codecopy_source_mload:
  code_layout_valid s /\
  eval_operand (Label "code_end") s = SOME basew /\
  w2n off + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword (:256) /\
  t.vs_code = s.vs_code /\
  inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dst; src; Lit 32w] /\
  eval_operand dst t = SOME dw /\
  eval_operand src t = SOME (off + basew) /\
  step_inst 0 C inst t = OK u
  ==>
  mload (w2n dw) u = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))
Proof
  strip_tac >> drule_all ld_codecopy_mload >>
  drule_all ld_code_data_bytes >> simp[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "code data theorem has hypotheses")
  [ld_code_data_bytes, ld_codecopy_source_mload];

(* Public destination may relocate; the payload is still exactly shared. *)
Theorem ld_dloadbytes_codecopy_payload:
  code_layout_valid s /\
  eval_operand (Label "code_end") s = SOME basew /\
  w2n off + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword (:256) /\
  t.vs_code = s.vs_code /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [d;r;n] /\
  ci.inst_opcode = CODECOPY /\ ci.inst_operands = [d';r';n'] /\
  eval_operand d s = SOME dst /\ eval_operand r s = SOME off /\
  eval_operand n s = SOME len /\
  eval_operand d' t = SOME dst' /\
  eval_operand r' t = SOME (off + basew) /\
  eval_operand n' t = SOME len /\
  step_inst_base ci t = OK u ==>
  ?bytes ss. LENGTH bytes = w2n len /\
    bytes = TAKE (w2n len)
      (DROP (w2n off) s.vs_data_section ++ REPLICATE (w2n len) 0w) /\
    step_inst_base inst s = OK ss /\
    ss = write_memory_with_expansion (w2n dst) bytes s /\
    u = write_memory_with_expansion (w2n dst') bytes t
Proof
  strip_tac >>
  `u = write_memory_with_expansion (w2n dst')
     (TAKE (w2n len) (DROP (w2n (off + basew)) t.vs_code ++
                      REPLICATE (w2n len) 0w)) t` by
    (qpat_x_assum `step_inst_base ci t = OK u` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >> simp[]) >>
  drule_all ld_code_data_bytes >>
  disch_then (qspec_then `w2n len` assume_tac) >>
  qexistsl [`TAKE (w2n len)
     (DROP (w2n off) s.vs_data_section ++ REPLICATE (w2n len) 0w)`,
    `write_memory_with_expansion (w2n dst)
     (TAKE (w2n len) (DROP (w2n off) s.vs_data_section ++
                     REPLICATE (w2n len) 0w)) s`] >>
  simp[LENGTH_TAKE] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> simp[]
QED

val _ = if null (hyp ld_dloadbytes_codecopy_payload) then ()
        else raise Fail "public copy payload has hypotheses";

