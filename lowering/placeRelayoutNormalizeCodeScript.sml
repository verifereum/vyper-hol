(* Code certificates for the fresh typed-normalization prefix. *)
Theory placeRelayoutNormalizeCode
Ancestors
  aggregateTypedCopyRawShape context compileEnv fragExec exprSimAbiGasBridge

Theorem place_normalize_alloc_certified:
  code_trace_certified (compile_alloc_buffer nbytes)
Proof
  simp[compile_alloc_buffer_def] >>
  irule code_trace_certified_bind >>
  simp[code_trace_certified_emit_op, code_trace_certified_return]
QED

Theorem place_normalize_prefix_certified:
  code_trace_certified
    (comp_bind (compile_alloc_buffer nbytes) (\buf.
      compile_store_memory_typed ce buf.buf_operand ty src sty))
Proof
  irule code_trace_certified_bind >>
  simp[place_normalize_alloc_certified, code_trace_certified_typed_copy_family]
QED

Theorem place_normalize_prefix_raw_shape:
  compile_alloc_buffer nbytes sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand ty src sty sm = ((),sb) ==>
  frag_ops_free sa sb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  strip_tac >>
  `code_trace_certified (comp_bind (compile_alloc_buffer nbytes) (\buf.
     compile_store_memory_typed ce buf.buf_operand ty src sty))` by
    simp[place_normalize_prefix_certified] >>
  drule code_trace_certified_raw_shape >>
  disch_then irule >> simp[comp_bind_def]
QED
