(* The folded selector bypasses evaluation of the signature operand. *)
Theory bodyPtrEnvBuiltinsMethodFolded
Ancestors bodyPtrEnvBuiltinsMethodLiteral bodyPtrEnvBuiltinsMethodShape
  bodyPtrEnvBuiltinsSelectorCounted exprLoweringProps exprSimLiteralBuffer
  context emitHelper compileEnv exprLowering list rich_list words

Theorem folded_selector_chunk:
  LENGTH (bs:word8 list) = 4 ==>
  compile_store_byte_chunks pop bs 32 sa =
    do dst <- emit_op ADD [pop; Lit 32w];
       emit_void MSTORE [dst; Lit (word_of_bytes T 0w
         (TAKE 32 (bs ++ REPLICATE 31 (0w:word8))))]
    od sa
Proof
  strip_tac >>
  `bs <> [] /\ DROP 32 bs = []` by
    (simp[DROP_EQ_NIL] >> strip_tac >> gvs[]) >>
  Cases_on `bs` >- gvs[] >>
  once_rewrite_tac[compile_store_byte_chunks_def] >>
  simp[compile_store_byte_chunks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[emit_void_def, emit_inst_def,
         comp_bind_def, comp_return_def, fresh_id_def, emit_def]
QED

Theorem folded_selector_compile:
  LENGTH (bs:word8 list) = 4 ==>
  compile_bytelike_literal bs 4 sa =
    do buf <- compile_alloc_buffer 64;
       emit_void MSTORE [buf.buf_operand; Lit 4w];
       dst <- emit_op ADD [buf.buf_operand; Lit 32w];
       emit_void MSTORE [dst; Lit (word_of_bytes T 0w
         (TAKE 32 (bs ++ REPLICATE 31 (0w:word8))))];
       return buf
    od sa
Proof
  strip_tac >>
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[folded_selector_chunk, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> gvs[]
QED
