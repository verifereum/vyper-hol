Theory concretizePtrCurrentRangeTransport
Ancestors
  concretizePtrObservationInterface concretizePtrWritePurity
  concretizePtrOpaqueRetpc concretizePtrOwnershipErasure
  ptrDiscipline memLocDefs pointerConfinedDefs
  contextCodegenRel codegenRel venomInst venomState
  list finite_map pred_set

Theorem ptr_read_max_size_not_pointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_read_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop ==>
  !v. sizeop = Var v ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `fn_ptr_ok P fn` kall_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[mem_read_ops_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- metis_tac[MEM_REVERSE, MEM] >>
  `inst.inst_operands = REVERSE (Var v::Var v::v10::v11)` by
    metis_tac[REVERSE_REVERSE] >>
  gvs[FILTER_REVERSE, FILTER_APPEND_DISTRIB] >>
  qpat_x_assum `_ ++ _ = [_]` mp_tac >>
  disch_then (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[]
QED

Theorem ptr_read_max_size_untainted:
  taint_ok fn tn inst s /\ mem_read_ops inst = SOME ops /\
  ops.iao_max_size = SOME sizeop ==> op_taint tn sizeop = {}
Proof
  Cases_on `inst.inst_opcode` >>
  simp[mem_read_ops_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[taint_ok_def] >>
  simp[op_taint_def] >> metis_tac[op_taint_def, MEM_REVERSE, MEM]
QED

val load_tac =
  rpt strip_tac >>
  Cases_on `eval_operand src' tgt` >> gvs[] >>
  `?x. eval_operand src' src = SOME x` by
    metis_tac[optionTheory.IS_SOME_DEF, optionTheory.option_CASES] >>
  simp[];

val range_tac =
  rpt strip_tac >>
  gvs[memory_range_of_operands_def] >>
  qmatch_goalsub_rename_tac `eval_operand a src = SOME _` >>
  Cases_on `eval_operand a tgt` >> gvs[] >>
  `?x. eval_operand a src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand sz tgt` >> gvs[];

val copy_tac =
  rpt strip_tac >>
  Cases_on `eval_operand v2 tgt` >> gvs[] >>
  `?z. eval_operand v2 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand src' tgt` >> gvs[] >>
  `?x. eval_operand src' src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand sz tgt` >> gvs[];

val call_tac =
  rpt strip_tac >>
  gvs[memory_range_of_operands_def, sized_source_write_range_def] >>
  qpat_x_assum `inst.inst_operands = _` kall_tac >>
  rpt (qmatch_asmsub_rename_tac
         `MEM _ (case eval_operand gate tgt of NONE => [] | SOME v => _)` >>
       Cases_on `eval_operand gate tgt` >> gvs[] >>
       `?z. eval_operand gate src = SOME z` by
         metis_tac[optionTheory.IS_SOME_EXISTS] >> gvs[] >>
       qpat_x_assum `eval_operand gate tgt = SOME _` kall_tac >>
       qpat_x_assum `eval_operand gate src = SOME _` kall_tac) >>
  qmatch_goalsub_rename_tac `eval_operand a src = SOME _` >>
  rename1 `eval_operand szop src = eval_operand szop tgt` >>
  Cases_on `eval_operand a tgt` >> gvs[] >>
  `?x. eval_operand a src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand szop tgt` >> gvs[] >>
  Cases_on `eval_operand v10 tgt` >> gvs[] >>
  `?z. eval_operand v10 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >> simp[];

val fixed_tac =
  rpt strip_tac >>
  gvs[fixed_source_write_range_def] >>
  Cases_on `eval_operand dst tgt` >> gvs[] >>
  `?x. eval_operand dst src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand v6 tgt` >> gvs[] >>
  `?z. eval_operand v6 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >> simp[];

val sized_tac =
  rpt strip_tac >>
  gvs[sized_source_write_range_def] >>
  Cases_on `eval_operand dst tgt` >> gvs[] >>
  `?x. eval_operand dst src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand v6 tgt` >> gvs[] >>
  `?z. eval_operand v6 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand sz tgt` >> gvs[];

Theorem ptr_current_descriptor_range_reflection[local]:
  inst.inst_opcode <> DRET /\ inst.inst_opcode <> LOG /\
  ((mops = mem_read_ops inst /\
    ranges_s = source_memory_read_ranges inst src /\
    ranges_t = source_memory_read_ranges inst tgt) \/
   (mops = mem_write_ops inst /\
    ranges_s = source_memory_write_ranges inst src /\
    ranges_t = source_memory_write_ranges inst tgt)) /\
  (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) /\
  (!ops sizeop. mops = SOME ops /\ ops.iao_max_size = SOME sizeop ==>
    eval_operand sizeop src = eval_operand sizeop tgt) /\
  MEM (off,len) ranges_t ==>
  ?ops x y. mops = SOME ops /\
    eval_operand ops.iao_ofst src = SOME x /\
    eval_operand ops.iao_ofst tgt = SOME y /\
    off = w2n y /\ MEM (w2n x,len) ranges_s
Proof
  strip_tac >>
  qpat_x_assum `MEM _ ranges_t` mp_tac >>
  simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
       AllCaseEqs()] >>
  Cases_on `inst.inst_opcode` >> simp[] >> strip_tac >>
  gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
  all_tac
  >~ [`inst.inst_opcode = MLOAD`] >- load_tac
  >~ [`inst.inst_opcode = ILOAD`] >- load_tac
  >~ [`inst.inst_opcode = MCOPY`] >- copy_tac
  >~ [`inst.inst_opcode = RETURN`] >- range_tac
  >~ [`inst.inst_opcode = REVERT`] >- range_tac
  >~ [`inst.inst_opcode = SHA3`] >- range_tac
  >~ [`inst.inst_opcode = CALL`] >- call_tac
  >~ [`inst.inst_opcode = CALL`] >- call_tac
  >~ [`inst.inst_opcode = STATICCALL`] >- call_tac
  >~ [`inst.inst_opcode = STATICCALL`] >- call_tac
  >~ [`inst.inst_opcode = DELEGATECALL`] >- call_tac
  >~ [`inst.inst_opcode = DELEGATECALL`] >- call_tac
  >~ [`inst.inst_opcode = CREATE`] >- call_tac
  >~ [`inst.inst_opcode = CREATE2`] >- call_tac
  >~ [`inst.inst_opcode = EXTCODECOPY`] >- call_tac
  >~ [`inst.inst_opcode = MSTORE`] >- fixed_tac
  >~ [`inst.inst_opcode = ISTORE`] >- fixed_tac
  >~ [`inst.inst_opcode = MSTORE8`] >- fixed_tac
  >> sized_tac
QED
