(* Compiler boundaries for overlap-safe copies with distinct layouts. *)
Theory widenedAssignValueParts
Ancestors
  stmtLowering context compileEnv externalEntryShape bodyCopyMemory
  abiBuiltinAllocation emitHelperProps exprLoweringProps freshWrites
  loweringHalt exprSimBufferStore fragExec list rich_list
Libs monadsyntax

Theorem assign_memory_layout_parts:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb)
Proof
  simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[pairTheory.PAIR]
QED

Theorem assign_memory_layout_code:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sn fn /\ fn_has_code sa sm fn /\ fn_has_code sm sn fn /\
    fn_has_code sn sb fn
Proof
  strip_tac >> drule assign_memory_layout_parts >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule buffer_copy_memory_shape >> simp[cs_extends_def, same_blocks_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sn sb` by
    (mp_tac (Q.SPECL [`ce`, `buf.buf_operand`, `dst`, `dty`, `sty`, `sn`]
       compile_store_memory_labels) >> simp[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn fn /\ fn_has_code sn sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sn fn` by
    (irule fn_has_code_split >> simp[]) >>
  qexistsl_tac [`buf`, `sm`, `sn`] >> simp[]
QED

Theorem assign_memory_typed_layout_code:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory_typed ce dst dty buf.buf_operand sty sn = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sn fn /\ fn_has_code sa sm fn /\ fn_has_code sm sn fn /\
    fn_has_code sn sb fn
Proof
  strip_tac >> drule_all assign_memory_layout_code >>
  simp[compile_store_memory_def]
QED
