(* The folded selector bypasses evaluation of the signature operand. *)
Theory bodyPtrEnvBuiltinsMethodFolded
Ancestors bodyPtrEnvBuiltinsMethodLiteral bodyPtrEnvBuiltinsMethodShape
  bodyPtrEnvBuiltinsSelectorCounted bodyPtrEnvBuiltinsSelectorRun
  bodyPtrEnvBuiltinsSelectorPost exprLoweringProps exprSimLiteralBuffer
  context emitHelper compileEnv exprLowering exprSimHash bodyPtrDefs
  list rich_list words venomState

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

Theorem folded_selector_code:
  LENGTH (bs:word8 list) = 4 /\
  compile_bytelike_literal bs 4 sa = (buf,sb) ==>
  ?sm p q.
    compile_alloc_buffer 64 sa = (buf,sm) /\ buf.buf_operand = Var p /\
    p = STRING #"%" (toString sa.cs_next_var) /\
    q = STRING #"%" (toString (sa.cs_next_var+1)) /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p];
       mk_inst (sa.cs_next_id+1) MSTORE [Var p; Lit 4w] [];
       mk_inst (sa.cs_next_id+2) ADD [Var p; Lit 32w] [q];
       mk_inst (sa.cs_next_id+3) MSTORE [Var q;
         Lit (word_of_bytes T 0w (TAKE 32 (bs ++ REPLICATE 31 (0w:word8))))] []] /\
    sb.cs_next_id = sa.cs_next_id+4 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+4
Proof
  strip_tac >>
  gvs[folded_selector_compile, compile_alloc_buffer_def, emit_op_def,
    emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

