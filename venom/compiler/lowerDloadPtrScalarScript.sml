Theory lowerDloadPtrScalar
Ancestors
  lowerDloadPtrOrdinary lowerDloadPtrBlockEntry lowerDloadPtrAggregate
  lowerDloadPtrPhi lowerDloadPtrRel venomExecSemantics venomState venomInst
  ptrDiscipline unitShapeDefs codegenRel memLocDefs pointerConfinedDefs
  finite_map list pred_set

Theorem scalar_operand_clean[local]:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  gvs[MEM, ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem scalar_operand_equal[local]:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> v IN V) /\
  op_prov G op = NONE /\ op_taint tn op = {} /\
  (eval_operand op s = NONE <=> eval_operand op t = NONE) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >> Cases_on `eval_operand op s` >- gvs[] >>
  Cases_on `eval_operand op t` >- gvs[] >>
  `dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) x x'` by
    (irule dload_matched_operand >> qexistsl [`V`,`s`,`t`,`un`] >> simp[]) >>
  Cases_on `op_prov H op` >>
  gvs[dload_value_word_def, word_agree_except_bits] >>
  simp[fcpTheory.CART_EQ] >> metis_tac[]
QED

Theorem scalar_step_transport[local]:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE] /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel Ct i t = OK t' ==>
  ?out z. i.inst_outputs = [out] /\ t' = update_var out z t /\
    step_inst fuel Cs i s = OK (update_var out z s)
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >> gvs[MEM] >> metis_tac[]
QED

Theorem out_taint_opcode_exclusion[local]:
  ~MEM i.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; SHL; SHR; SAR] ==>
  out_taint tn i s = {}
Proof
  simp[MEM] >> strip_tac >>
  namedCases_on `i.inst_operands` ["", "a ops"] >- simp[out_taint_def] >>
  namedCases_on `ops` ["", "b rest"]
  >- (simp[out_taint_def] >> Cases_on `eval_operand a s` >> simp[]) >>
  Cases_on `rest` >> simp[out_taint_def] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem written_taint_opcode_exclusion[local]:
  ~MEM i.inst_opcode [MSTORE; ISTORE; MCOPY] ==>
  written_taint tn i s = {}
Proof
  simp[MEM] >> strip_tac >>
  namedCases_on `i.inst_operands` ["", "a ops"] >- simp[written_taint_def] >>
  namedCases_on `ops` ["", "b rest"] >- simp[written_taint_def] >>
  namedCases_on `rest` ["", "c tail"] >- simp[written_taint_def] >>
  Cases_on `tail` >> simp[written_taint_def]
QED

Theorem scalar_ghost_updates[local]:
  MEM i.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE] /\
  i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out z s) = set_prov G [out] NONE /\
  step_taint i s (update_var out z s) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  `~MEM i.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; SHL; SHR; SAR] /\
   ~MEM i.inst_opcode [MSTORE; ISTORE; MCOPY]` by gvs[MEM] >>
  `out_taint tn i s = {} /\ written_taint tn i s = {}` by
    metis_tac[out_taint_opcode_exclusion, written_taint_opcode_exclusion] >>
  gvs[MEM] >>
  simp[step_prov_def, out_prov_def, step_taint_def] >>
  simp[mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def] >>
  simp[new_site_bytes_def, step_writes_def, range_bytes_def,
    source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED
