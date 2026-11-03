(* Concrete diagnostics for a nonvoid return containing a zero-sized NoneT. *)
Theory extCallZeroReturnProbe
Ancestors
  exprLowering compileEnv valueEncoding vyperTypeSystem vyperABI vyperValue words finite_map
  abiEncoder exprLoweringProps vyperCompiler venomState emitHelper builtinSimple

Theorem nested_none_type_probe:
  evaluate_type FEMPTY (TupleT [NoneT]) = SOME (TupleTV [NoneTV])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem nested_none_source_probe:
  evaluate_abi_decode_return FEMPTY (TupleT [NoneT]) [] =
    INL (ArrayV (TupleV [NoneV]))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem nested_none_descriptor_probe:
  type_to_abi_dec_info FEMPTY (ce with ce_struct_fields := FEMPTY)
    (TupleT [TupleT [NoneT]]) =
    DecComplex F [(DecComplex F [(DecPrimWord NoClamp,0,0)],0,0)]
Proof
  simp[type_to_abi_dec_info_def, type_to_abi_clamp_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       type_memory_bytes_def, type_memory_size_def]
QED

(* Execute the actual generated return preamble and wrapped decoder.
   Contrary to the candidate suspicion, the zero-sized leaf does not abort:
   the enclosing complex guards check a zero extent, and NoClamp has no guard. *)
Theorem nested_none_return_run_probe:
  let (hi,st) = compile_return_value_decode (Lit 32w) 0 0
                  (initial_compile_state "entry") in
  let (_,final) = compile_abi_decode_to_buf (Lit 64w) (Lit 32w) MLOAD hi
    (type_to_abi_dec_info FEMPTY (ce with ce_struct_fields := FEMPTY)
      (TupleT [TupleT [NoneT]])) st in
  case run_inst_seq final.cs_current_insts (init_venom_state "entry") of
    OK t => ~t.vs_halted
  | _ => F
Proof
  simp[nested_none_descriptor_probe, compile_return_value_decode_def,
       compile_select_def, compile_abi_decode_to_buf_def,
       compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       compile_getelemptr_abi_def, dec_info_needs_offset_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, initial_compile_state_def] >>
  EVAL_TAC >>
  simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def,
       wordsTheory.dimword_def] >> EVAL_TAC >>
  simp[venomExecSemanticsTheory.bool_to_word_def, wordsTheory.WORD_ADD_0,
       wordsTheory.WORD_MULT_CLAUSES, wordsTheory.WORD_XOR_CLAUSES,
       wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >>
  simp[venomExecSemanticsTheory.bool_to_word_def] >> EVAL_TAC
QED

(* The zero nominal extent does not describe the decoder's actual write.
   Allocation ids here witness interval admissibility only, not caller reachability. *)
Theorem nested_none_return_write_probe:
  let s0 = (init_venom_state "entry") with
    <| vs_memory := REPLICATE 64 (0w:word8) ++ REPLICATE 32 1w;
       vs_allocas := FEMPTY |+ (1,(64,32)) |+ (100,(64,0));
       vs_alloca_next := 96 |> in
  alloca_inv s0 /\
  type_memory_bytes (ce with ce_struct_fields := FEMPTY)
    (TupleT [TupleT [NoneT]]) = 0 /\
  let (hi,st) = compile_return_value_decode (Lit 32w) 0 0
                  (initial_compile_state "entry") in
  let (_,final) = compile_abi_decode_to_buf (Lit 64w) (Lit 32w) MLOAD hi
    (type_to_abi_dec_info FEMPTY (ce with ce_struct_fields := FEMPTY)
      (TupleT [TupleT [NoneT]])) st in
  case run_inst_seq final.cs_current_insts s0 of
    OK t => ~t.vs_halted /\
      mem_bytes_at 64 32 s0.vs_memory = REPLICATE 32 1w /\
      mem_bytes_at 64 32 t.vs_memory = REPLICATE 32 0w /\
      mem_bytes_at 64 32 t.vs_memory <> mem_bytes_at 64 32 s0.vs_memory
  | _ => F
Proof
  simp_tac (srw_ss()) [LET_THM] >>
  conj_tac
  >- (simp[venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.allocas_non_overlapping_def,
           venomMemDefsTheory.alloca_next_valid_def, FLOOKUP_UPDATE] >>
      rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >> decide_tac) >>
  simp[type_memory_bytes_def, type_memory_size_def] >>
  simp[nested_none_descriptor_probe, compile_return_value_decode_def,
       compile_select_def, compile_abi_decode_to_buf_def,
       compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       compile_getelemptr_abi_def, dec_info_needs_offset_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, initial_compile_state_def] >>
  EVAL_TAC >>
  simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def,
       wordsTheory.dimword_def] >> EVAL_TAC >>
  simp[venomExecSemanticsTheory.bool_to_word_def, wordsTheory.WORD_ADD_0,
       wordsTheory.WORD_MULT_CLAUSES, wordsTheory.WORD_XOR_CLAUSES,
       wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >>
  simp[venomExecSemanticsTheory.bool_to_word_def] >> EVAL_TAC
QED
