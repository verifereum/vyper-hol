Theory exprSimAbiEncodeArgsTupleLayout
Ancestors
  exprSimAbiEncodeArgsTupleTarget exprSimAbiEncodeArgsTupleProbe
  exprSimPrecompiles valueCopy valueEncodingProps abiDecodeStaticProps
  venomState byte words exprLowering compileEnv context exprSimProps loweringPosts

Theorem tuple_target_writes_slice:
  w2n (p:bytes32) + 128 < dimword (:256) ==>
  mem_bytes_at (w2n p) 128 (tuple_target_writes p s).vs_memory = tuple_memory
Proof
  strip_tac >>
  `w2n (p + 32w) = w2n p + 32 /\
   w2n (p + 64w) = w2n p + 64 /\
   w2n (p + 96w) = w2n p + 96` by
    (rpt conj_tac >> irule w2n_add_n2w_lt >> decide_tac) >>
  simp[tuple_target_writes_def, scratch_four_word_stores] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC
QED

Theorem tuple_target_writes_value:
  w2n (p:bytes32) + 128 < dimword (:256) ==>
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (BytesT (Dynamic 32))])
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))
    (w2n p) (tuple_target_writes p s).vs_memory
Proof
  strip_tac >>
  irule valueCopyTheory.val_in_memory_relocate >>
  conj_tac >- EVAL_TAC >>
  qexistsl_tac [`0`, `128`, `tuple_memory`] >>
  simp[cj 1 tuple_memory_mismatch, tuple_target_writes_slice] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem tuple_target_writes_region_frame:
  w2n (p:bytes32) + 128 < dimword (:256) /\
  regions_disjoint (w2n p) 128 b len ==>
  mem_bytes_at b len (tuple_target_writes p s).vs_memory =
  mem_bytes_at b len s.vs_memory
Proof
  strip_tac >> irule mem_bytes_at_bytewise >> rpt strip_tac >>
  irule tuple_target_writes_frame >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem tuple_target_unwrap_buffer:
  unwrap_value ce (LocatedValue tuple_narrow (base_ptr buf)) sb =
    (buf.buf_operand,sb)
Proof
  simp[unwrap_value_def, tuple_narrow_def, is_word_type_def,
       contextTheory.base_ptr_def, comp_return_def]
QED

Theorem tuple_target_writes_locals:
  w2n (p:bytes32) + 128 < dimword (:256) /\
  (!name b len. local_region ce es.scopes s name b len ==>
     regions_disjoint (w2n p) 128 b len) ==>
  locals_kept ce es es s
    (s with vs_memory := (tuple_target_writes p s).vs_memory)
Proof
  strip_tac >> irule locals_kept_regions >> rpt strip_tac >> simp[] >>
  irule tuple_target_writes_region_frame >> simp[] >> metis_tac[]
QED
