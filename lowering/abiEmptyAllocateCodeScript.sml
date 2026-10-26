(* Structural decomposition of actual complex Empty allocation and initialization. *)
Theory abiEmptyAllocateCode
Ancestors
  abiEmptyCode abiBuiltinAllocation abiDecoderReentry abiTupleEncodeSlot
  exprLoweringProps emitHelperProps compileEnv builtinSimple emitHelper
  venomState venomInst words list arithmetic

Theorem abi_empty_complex_code:
  compile_builtin_empty_complex outsz length_only st =
    let (buf,allocated) = compile_alloc_buffer outsz st in
    let (_,final) = (if length_only then emit_void MSTORE [buf.buf_operand;Lit 0w]
      else compile_zero_words buf.buf_operand ((outsz+31) DIV 32)) allocated in
      (buf,final)
Proof
  simp[compile_builtin_empty_complex_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def, LET_THM, pairTheory.UNCURRY_DEF] >>
  pairarg_tac >> Cases_on `length_only` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> simp[]
QED

Theorem abi_empty_complex_parts:
  compile_builtin_empty_complex outsz length_only st = (buf,final) ==>
  ?allocated. compile_alloc_buffer outsz st = (buf,allocated) /\
    (if length_only then emit_void MSTORE [buf.buf_operand;Lit 0w]
      else compile_zero_words buf.buf_operand ((outsz+31) DIV 32)) allocated = ((),final)
Proof
  simp_tac bool_ss [abi_empty_complex_code, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer outsz st = (buf,allocated)` >>
  rename1 `_ allocated = (ignored:unit,final)` >>
  Cases_on `ignored:unit` >> gvs[] >> qexists_tac `allocated` >> simp[]
QED

Theorem abi_empty_alloc_buffer_shape:
  compile_alloc_buffer outsz st = (buf,allocated) ==>
  buf.buf_size = outsz /\ allocated.cs_next_var = st.cs_next_var+1 /\
  abi_decoder_operand_live allocated.cs_next_var buf.buf_operand /\
  inst_extends st allocated
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  drule inst_extends_emit_op >> simp[]
QED

Theorem abi_empty_initializer_shape:
  (if length_only then emit_void MSTORE [base_op;Lit 0w]
    else compile_zero_words base_op ((outsz+31) DIV 32)) allocated = ((),final) ==>
  allocated.cs_next_var <= final.cs_next_var /\ inst_extends allocated final
Proof
  Cases_on `length_only` >> simp[] >> strip_tac
  >- (drule emitted_insts_emit_void >> strip_tac >>
      drule inst_extends_emit_void >> simp[]) >>
  drule abi_empty_zero_words_shape >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_ALLOCATE_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty allocation code not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyAllocateCode");
