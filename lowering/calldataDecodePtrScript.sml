(* Pointer and taint boundaries for calldata decoding writes. *)
Theory calldataDecodePtr
Ancestors bodyPtrDefs ptrDiscipline venomInst venomState venomExecSemantics
  codegenRel contextCodegenRel memLocDefs pred_set

Theorem calldatacopy_access_ok:
  eval_operand n s = SOME nw /\ ptr_covers G tn p s (w2n nw) ==>
  access_ok lo G fn (mk_inst id CALLDATACOPY [Var p;src;n] []) s
Proof
  rw[ptr_covers_def, access_ok_def, mk_inst_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     source_memory_read_ranges_def, mem_write_ops_def, eval_operand_def] >>
  Cases_on `eval_operand src s` >> gvs[]
QED

Theorem calldatacopy_taint_ok:
  op_taint tn (Var p) = {} /\ op_taint tn src = {} /\ op_taint tn n = {} ==>
  taint_ok fn tn (mk_inst id CALLDATACOPY [Var p;src;n] []) s
Proof
  simp[taint_ok_def, mk_inst_def, source_memory_read_ranges_def] >>
  metis_tac[]
QED

Theorem calldatacopy_written_range_clean:
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\ w2n dw <= i /\ i < w2n dw + w2n nw ==>
  i NOTIN (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_mem
Proof
  simp[step_taint_def, mem_taint_def, step_writes_def, written_taint_def,
       mk_inst_def, source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def] >> metis_tac[]
QED

Theorem calldatacopy_nonmemory_taint:
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def]
QED
