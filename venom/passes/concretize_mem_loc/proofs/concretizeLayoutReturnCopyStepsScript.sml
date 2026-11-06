Theory concretizeLayoutReturnCopySteps
Ancestors ptrDiscipline venomExecSemantics venomState codegenRel list pred_set finite_map words

Theorem masked_clean_slice:
  LENGTH xs = LENGTH ys /\ off+n <= LENGTH xs /\
  (!i. i < LENGTH xs /\ i NOTIN M ==> EL i xs = EL i ys) /\
  (!k. k < n ==> off+k NOTIN M) ==>
  TAKE n (DROP off xs) = TAKE n (DROP off ys)
Proof
  strip_tac >> irule LIST_EQ >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP] >>
  rpt strip_tac >> simp[EL_TAKE, EL_DROP] >>
  first_x_assum irule >> simp[]
QED

Theorem return_copy_dispatch:
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [opd;os;on] /\
  eval_operand opd s = SOME d /\ eval_operand opd t = SOME dT /\
  eval_operand os s = SOME src /\ eval_operand os t = SOME src /\
  eval_operand on s = SOME n /\ eval_operand on t = SOME n /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata ==>
  (w2n src + w2n n > LENGTH s.vs_returndata ==>
    step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
    step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))) /\
  (w2n src + w2n n <= LENGTH s.vs_returndata ==>
    step_inst_base inst s = OK (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n src) s.vs_returndata)) s) /\
    step_inst_base inst t = OK (write_memory_with_expansion (w2n dT)
      (TAKE (w2n n) (DROP (w2n src) t.vs_returndata)) t))
Proof
  strip_tac >> simp[step_inst_base_def]
QED

Theorem return_copy_taint:
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [opd;os;on] /\
  eval_operand opd s = SOME d /\ eval_operand on s = SOME n /\
  eval_operand os s = SOME src ==>
  (step_taint inst s (write_memory_with_expansion (w2n d) bytes s) tn).t_mem =
    tn.t_mem DIFF range_bytes [(w2n d,w2n n)] /\
  (step_taint inst s post tn).t_stor = tn.t_stor /\
  (step_taint inst s post tn).t_trans = tn.t_trans /\
  (step_taint inst s post tn).t_imm = tn.t_imm
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       write_memory_with_expansion_def, source_memory_write_ranges_def,
       sized_source_write_range_def, FLOOKUP_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[EXTENSION] >> metis_tac[]
QED
