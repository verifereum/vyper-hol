(* An oversized CREATE fetch cannot have a successful outgoing caller edge. *)
Theory createCtorOversizedSink
Ancestors
  fragGasOrigin fragExec venomExecSemantics venomInst venomState vfmConstants

Theorem ctor_oversized_step_no_ok[local]:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value; off; sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value; off; sz; salt])) /\
  eval_operand sz s = SOME w /\ 2 * max_code_size < w2n w ==>
  step_inst fuel ctx i s <> OK t
Proof
  strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  IF_CASES_TAC >> simp[] >>
  rpt (CASE_TAC >> gvs[exec_create_def])
QED

Theorem ctor_oversized_no_ok:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value; off; sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value; off; sz; salt])) /\
  eval_operand sz s = SOME w /\ 2 * max_code_size < w2n w ==>
  !memory explicit ctx ms v. ~gas_origin_edge memory explicit ctx fn s ms (OK v)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  rw[gas_origin_edge_def, exit_result_def] >>
  metis_tac[ctor_oversized_step_no_ok]
QED
