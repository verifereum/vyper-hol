(* Counted runtime immutable copies, with exact checked transfer effects. *)
Theory reasonCodeCopyPtr
Ancestors
  reasonCodeTransferPtr reasonCodeLoadPtr reasonCodeOffsetPtr
  immutableCopyExecution compilerChainCode exprLoweringProps
  context compileEnv emitHelper fragExec bodyPtrDefs ptrDiscipline
  venomState venomInst finite_map words fragGasPathPtr

Theorem code_copy_suc_parts:
  compile_imm_copy_to_memory F imm src dst (SUC n) off sa = ((),sb) ==>
  ?src_op value dst_op c1 c2 c3 c4.
    compile_lit_byte_offset src off sa = (src_op,c1) /\
    emit_op DLOAD [src_op] c1 = (value,c2) /\
    compile_lit_byte_offset dst off c2 = (dst_op,c3) /\
    emit_void MSTORE [dst_op;value] c3 = ((),c4) /\
    compile_imm_copy_to_memory F imm src dst n (off+32) c4 = ((),sb)
Proof
  simp[Once compile_imm_copy_to_memory_def, compile_imm_load_word_def,
       comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem code_offset_extends:
  compile_lit_byte_offset op off sa = (r,sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule immutable_byte_offset_extends >>
  simp[cs_extends_def, same_blocks_def] >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED

Theorem code_copy_suc_code:
  compile_lit_byte_offset src off sa = (src_op,c1) /\
  emit_op DLOAD [src_op] c1 = (value,c2) /\
  compile_lit_byte_offset dst off c2 = (dst_op,c3) /\
  emit_void MSTORE [dst_op;value] c3 = ((),c4) /\
  compile_imm_copy_to_memory F imm src dst n (off+32) c4 = ((),sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  fn_has_code c4 sb func
Proof
  strip_tac >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\
   cs_extends c3 c4 /\ cs_extends c4 sb` by
    (rpt conj_tac >- metis_tac[code_offset_extends]
     >- metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND]
     >- metis_tac[code_offset_extends]
     >- metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, ci_mono_def, pairTheory.SND]) >>
  qspecl_then [`[c1;c2;c3;c4;sb]`, `sa`, `func`] mp_tac compiler_chain_has_code >>
  simp[]
QED
