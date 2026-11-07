(* Local probes: emitted allocation size versus tuple-field copy access.
   These are not counterexamples to a source-program theorem. *)
Theory normalizationOverflowPtr
Ancestors normalizationTupleBytesPtr supportedTypes

Theorem tuple_bytes_normalization_overflow_layout:
  !cenv.
  type_memory_bytes cenv
    (TupleT [BaseT (BytesT (Dynamic (dimword(:256)-32)))]) = dimword(:256) /\
  (n2w (type_memory_bytes cenv
    (TupleT [BaseT (BytesT (Dynamic (dimword(:256)-32)))])) : 256 word) = 0w /\
  arg_type_fits (TupleT [BaseT (BytesT (Dynamic 1))])
    (TupleT [BaseT (BytesT (Dynamic (dimword(:256)-32)))])
Proof
  gen_tac >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem singleton_tuple_bytes_copy_path:
  !cenv dst src dcap scap sa.
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    compile_store_memory_typed cenv dst (TupleT [BaseT (BytesT (Dynamic dcap))])
      src (TupleT [BaseT (BytesT (Dynamic scap))]) sa =
    compile_store_bytestring src dst sa
Proof
  rpt strip_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def,
    compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
  simp[Once contextTheory.compile_store_memory_typed_def] >>
  simp[contextTheory.compile_with_byte_offset_def, compileEnvTheory.comp_bind_def,
    compileEnvTheory.comp_return_def] >>
  simp[Once contextTheory.compile_store_memory_typed_def,
    compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
  simp[Once contextTheory.compile_store_memory_typed_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
    compileEnvTheory.comp_ignore_bind_def] >>
  Cases_on `compile_store_bytestring src dst sa` >>
  Cases_on `q` >> simp[compileEnvTheory.comp_bind_def,
    compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def]
QED

Theorem zero_alloca_success:
  FLOOKUP s.vs_allocas id = NONE ==>
  step_inst_base (mk_inst id ALLOCA [Lit 0w] [out]) s =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,0))))
Proof
  simp[Once venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
    venomStateTheory.eval_operand_def, venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem zero_region_header_copy_rejected:
  eval_operand (Var dst) s = SOME dw /\ eval_operand src s = SOME sw /\
  FLOOKUP G dst = SOME (w2n dw,0) /\ ~in_revert_forward func s ==>
  ~access_ok 0 G func (mk_inst id MCOPY [Var dst;src;Lit 32w] []) s
Proof
  strip_tac >> simp[ptrDisciplineTheory.access_ok_def] >> disj1_tac >>
  qexistsl [`w2n dw`, `32`] >>
  simp[codegenRelTheory.source_memory_write_ranges_def,
    venomStateTheory.eval_operand_def, memLocDefsTheory.mem_write_ops_def,
    venomInstTheory.mk_inst_def, wordsTheory.dimword_def,
    codegenRelTheory.sized_source_write_range_def]
QED

Theorem bytestring_copy_final_instruction:
  compile_store_bytestring src dst sa = ((),sb) ==>
  ?len sm. compile_bytestring_copy_len src sa = (len,sm) /\
    emit_void MCOPY [dst;src;len] sm = ((),sb)
Proof
  simp[contextTheory.compile_store_bytestring_def, compileEnvTheory.comp_bind_def] >>
  Cases_on `compile_bytestring_copy_len src sa` >> simp[]
QED

Theorem empty_bytes_copy_count:
  w2n (((0w + 31w) && i2w (-32)) + 32w : 256 word) = 32 /\
  val_store_size (BaseTV (BytesT (Dynamic 1))) (BytesV []) = 32
Proof
  simp[exprSimTheory.val_store_size_def, vfmConstantsTheory.word_size_def] >>
  mp_tac (Q.SPEC `0` valueCopyTheory.bytestring_copy_len_word_exact) >>
  simp[vfmConstantsTheory.word_size_def, wordsTheory.dimword_def] >>
  metis_tac[wordsTheory.w2n_11, wordsTheory.w2n_n2w]
QED

Theorem overflow_tuple_allocation_emits_zero:
  compile_alloc_buffer (type_memory_bytes cenv
    (TupleT [BaseT (BytesT (Dynamic (dimword(:256)-32)))])) sa = (buf,sb) ==>
  ?sx p. buf.buf_operand = Var p /\
    emit_inst ALLOCA [Lit 0w] [p] sx = ((),sb) /\
    ~not_fresh_at sa p /\ not_fresh_at sb p
Proof
  strip_tac >> drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >>
  qexistsl [`sx`, `p`] >>
  mp_tac (Q.SPEC `cenv` tuple_bytes_normalization_overflow_layout) >>
  strip_tac >> gvs[]
QED

Theorem overflow_bytes_tuple_supported:
  !tops.
    supported_value_type tops
      (TupleT [BaseT (BytesT (Dynamic (dimword(:256)-32)))]) /\
    well_formed_type (type_env tops)
      (TupleT [BaseT (BytesT (Dynamic (dimword(:256)-32)))])
Proof
  gen_tac >> EVAL_TAC
QED
