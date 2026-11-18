Theory bodyFullStoreSlotsRetired
Ancestors
  exprLoweringProps exprSimCopy context emitHelperProps compileEnv
  bodyPtrDefs ptrDiscipline venomState venomInst venomExecSemantics
  bodyPtrSignedConvertScalarTransfer bodyPtrBopScalarStep
  fragExec finite_map words list rich_list arithmetic

Theorem bop_suffix_placement:
  fn_has_code c2 cz func /\ same_blocks c2 cz /\
  cz.cs_current_insts = c2.cs_current_insts ++ code /\
  t.vs_current_bb = c2.cs_current_bb /\
  t.vs_inst_idx = LENGTH c2.cs_current_insts ==>
  ?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX code (DROP t.vs_inst_idx bb.bb_instructions)
Proof
  simp[fn_has_code_def, same_blocks_def] >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]
QED

Theorem ifexp_runtime_offset_covers:
  compile_lit_byte_offset (Var root) off sa = (dst,sb) /\
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off+n <= capacity /\ w2n a+off < dimword (:256) /\
  eval_operand dst t = SOME (a+n2w off) /\
  op_prov H dst = op_prov G (Var root) /\ op_taint tt dst = {} ==>
  ?q. dst = Var q /\ ptr_covers H tt q t n
Proof
  strip_tac >>
  `?q. dst = Var q` by
    (Cases_on `off = 0` >>
     gvs[compile_lit_byte_offset_def, comp_return_def] >>
     drule emitted_insts_emit_op >> simp[]) >>
  qexists_tac `q` >> simp[] >>
  `off < dimword (:256)` by decide_tac >>
  gvs[ptr_covers_def, eval_operand_def, op_prov_def] >>
  simp[ptr_covers_def, w2n_add_2, w2n_n2w, LESS_MOD] >>
  decide_tac
QED

Theorem scalar_forward_output_provenance_none:
  (!op. MEM op inst.inst_operands ==> op_prov G op = NONE) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
   inst.inst_opcode = ASSIGN) /\ MEM x inst.inst_outputs ==>
  FLOOKUP (step_prov PG G inst t) x = NONE
Proof
  strip_tac >> irule step_prov_output_none >> simp[] >>
  `first_prov G inst.inst_operands = NONE` by
    (irule first_prov_none >> simp[EVERY_MEM]) >>
  gvs[out_prov_def]
QED
