Theory bodyPtrSignedConvertIszero
Ancestors
  bodyPtrDefs decoderGhostFramePtr typedCopyLoopHeaderPtr
  bodyPtrSignedConvertScalarTransfer emitHelperProps ptrSafeRun ptrDiscipline
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map pred_set

(* The allocation premises belong to ptr_inst_ok even for a pure opcode. *)
Theorem iszero_ptr_inst_ok:
  op_taint tn x = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  step_inst_base (mk_inst id ISZERO [x] [y]) s = OK u ==>
  ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id ISZERO [x] [y]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, exec_pure1_def] >>
  Cases_on `eval_operand x s` >> simp[update_var_def] >> strip_tac >> gvs[]
QED

Theorem iszero_run_shape:
  step_inst_base (mk_inst id ISZERO [x] [y]) s = OK u ==>
  ?w. eval_operand x s = SOME w /\
      u = update_var y (bool_to_word (w = 0w)) s
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure1_def] >>
  Cases_on `eval_operand x s` >> simp[] >> strip_tac >> gvs[]
QED

(* Use the existing general ghost theorem, which clears stale output entries.
   Other-variable frames are decoderGhostFramePtr's opcode-independent facts. *)
Theorem iszero_ghost_update:
  step_inst_base (mk_inst id ISZERO [x] [y]) s = OK u ==>
  step_prov PG G (mk_inst id ISZERO [x] [y]) u =
    DRESTRICT G (COMPL {y}) /\
  step_taint (mk_inst id ISZERO [x] [y]) s u tn =
    (tn with t_var := tn.t_var |+ (y,{}))
Proof
  strip_tac >> drule iszero_run_shape >> strip_tac >> gvs[] >>
  irule typed_copy_loop_arith_ghost_clean >> simp[update_var_def]
QED
