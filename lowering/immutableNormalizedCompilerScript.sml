(* Compiler decomposition for either constructor immutable base form. *)
Theory immutableNormalizedCompiler
Ancestors
  immutableFixedOptionMem immutableAssignStore immutableDeployAssignBytes stmtLowering compileEnv context
  fragExec loweringSlice exprLoweringProps externalEntryShape
  venomState words arithmetic list pair

Theorem immutable_normalized_compiler_parts_option:
  compile_assign_value ce dst LocCode src F sl dty sty
    (type_memory_bytes ce dty) sm = ((),sb) /\
  sty <> dty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_memory_bytes ce dty = sz /\ 0 < sz /\ sz MOD 32 = 0 ==>
  ?buf mid sn n.
    compile_alloc_buffer sz sm = (buf,mid) /\
    compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sn) /\
    compile_imm_store_words ce.ce_imm_alloca buf.buf_operand dst n 0 sn = ((),sb) /\
    sz = 32*n /\ 0 < n
Proof
  strip_tac >> `dty <> sty` by metis_tac[] >>
  drule_all immutable_assign_normalized_compile >> strip_tac >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ mid = ((),sn)` >>
  `?n. type_memory_bytes ce dty = 32*n /\ 0 < n` by
    (qexists_tac `type_memory_bytes ce dty DIV 32` >>
     mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[] >>
     disch_then (qspec_then `type_memory_bytes ce dty` mp_tac) >> simp[] >> decide_tac) >>
  `compile_imm_store_words ce.ce_imm_alloca buf.buf_operand dst n 0 sn = ((),sb)` by
    (Cases_on `n = 1`
     >- (gvs[] >> CONV_TAC (DEPTH_CONV numLib.num_CONV) >>
         simp[compile_imm_store_words_def, compile_lit_byte_offset_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
         pairarg_tac >> gvs[] >> pairarg_tac >> gvs[comp_bind_def]) >>
     `~(32*n <= 32) /\ (32*n+31) DIV 32 = n` by simp[] >> gvs[]) >>
  qexistsl_tac [`buf`,`mid`,`sn`,`n`] >> simp[] >> metis_tac[]
QED

Theorem immutable_normalized_code_windows_option:
  compile_alloc_buffer sz sm = (buf,mid) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sn) /\
  compile_imm_store_words imm buf.buf_operand dst n 0 sn = ((),sb) /\
  fn_has_code sm sb func /\
  (emitted_blocks sm sb <> [] ==> ?bb.
    lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  fn_has_code sm mid func /\ fn_has_code mid sn func /\ fn_has_code sn sb func /\
  sn.cs_current_bb = sb.cs_current_bb /\ emitted_blocks sn sb = [] /\
  (emitted_blocks mid sn <> [] ==> ?bb.
    lookup_block sn.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `cs_extends sm mid /\ cs_extends mid sn /\ cs_extends sn sb` by
    (conj_tac
     >- metis_tac[externalEntryShapeTheory.compile_alloc_buffer_labels, SND] >>
     conj_tac
     >- metis_tac[externalEntryShapeTheory.typed_memory_family_labels, SND] >>
     metis_tac[externalEntryShapeTheory.compile_imm_store_words_labels, SND]) >>
  `fn_has_code sm mid func /\ fn_has_code mid sn func /\ fn_has_code sn sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `sn.cs_current_bb = sb.cs_current_bb /\ emitted_blocks sn sb = []` by
    (drule immutable_fixed_words_code_option >> simp[same_blocks_def, emitted_blocks_def] >>
     strip_tac >> simp[]) >>
  simp[] >> strip_tac >>
  `emitted_blocks sm sb <> []` by
    (gvs[emitted_blocks_def, cs_extends_def] >>
     metis_tac[TAKE_EQ_NIL, LENGTH_APPEND]) >>
  metis_tac[]
QED
