(* Compiler and execution composition for retained widened local assignments. *)
Theory widenedAssignPtrContinuation
Ancestors widenedAssignPtrTypedLocal widenedAssignPtrRhsInput
  assignBasePtrLocalAssign externalEntryShape stmtLowering context
  abiBuiltinAllocation abiBuiltinEncodeAllocate emitHelper emitHelperProps
  compileEnv exprLoweringProps valueCopyBytes fragExec exprSimBufferStore

Theorem widened_assign_local_staged_code:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm fn /\ fn_has_code sm sn fn /\ fn_has_code sn sb fn
Proof
  strip_tac >>
  `?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[pairTheory.PAIR]) >>
  qexistsl_tac [`buf`, `sm`, `sn`] >> simp[] >>
  `cs_extends sa sm` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sm sn` by
    (drule buffer_copy_memory_shape >> simp[cs_extends_def, same_blocks_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sn sb` by
    (mp_tac compile_store_memory_labels >>
     disch_then (qspecl_then [`ce`,`buf.buf_operand`,`dst`,`dty`,`sty`,`sn`] mp_tac) >>
     simp[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn fn /\ fn_has_code sn sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sn fn` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED
