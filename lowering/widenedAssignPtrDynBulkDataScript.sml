(* Counted flat data transport for widened dynamic arrays. *)
Theory widenedAssignPtrDynBulkData
Ancestors
  assignBasePtrBytesPost assignTuplePtrStageFrame bodyPtrPopLocalRootFrame
  typedCopyPtr typedMemoryCopy fragExecPtr ptrDiscipline venomState
  venomExecSemantics venomInst emitHelper emitHelperProps context
  bodyPtrDefs ptrSafeRun memLocDefs codegenRel contextCodegenRel valueEncoding valueEncodingProps words finite_map pred_set

Theorem widened_assign_mcopy_empty_operand[local]:
  eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
  eval_operand count_op s = SOME 0w /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn count_op = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MCOPY [dst;src;count_op] []) s
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_inst id MCOPY [dst;src;count_op] []) s =
    OK (mcopy (w2n a) (w2n b) 0 s)` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, mcopy_def,
       write_memory_with_expansion_def] >>
  gen_tac >> Cases_on `op = dst` >> gvs[] >>
  Cases_on `op = src` >> gvs[] >>
  Cases_on `op = count_op` >> gvs[]
QED
