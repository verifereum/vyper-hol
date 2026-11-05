(* Source data observations through the relocated code offset. *)
Theory lowerDloadCodeDataBytes
Ancestors
  lowerDloadScratchBytes lowerDloadDefs venomState list rich_list words
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
