Theory concretizePtrDallocaWriterTaint
Ancestors ptrDiscipline codegenRel venomInst venomState
  pred_set list words

(* A covered write removes old and fresh allocation taint alike.  Thus this
   local boundary is stronger than its successful-step use: post states may
   be arbitrary, and neither a freshness nor an execution premise is needed.
   The remaining premise concerns only the incoming writer data, factored
   below into stores, copies and the other (untainted-data) writers. *)
Theorem ptr_dalloca_writer_taint_transport:
  y IN range_bytes (step_writes instT t postT) /\
  (y IN written_taint un instT t ==> x IN written_taint tn inst s) /\
  x NOTIN (step_taint inst s post tn).t_mem ==>
  y NOTIN (step_taint instT t postT un).t_mem
Proof
  simp[step_taint_def, mem_taint_def] >> metis_tac[]
QED

Theorem ptr_dalloca_store_taint_transport:
  (inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE) /\
  instT.inst_opcode = inst.inst_opcode /\
  inst.inst_operands = [a;v] /\ instT.inst_operands = [aT;vT] /\
  eval_operand a s = SOME dst /\ eval_operand v s = SOME value /\
  eval_operand aT t = SOME dstT /\ eval_operand vT t = SOME valueT /\
  k < 32 /\ op_taint un vT SUBSET op_taint tn v /\
  w2n dst+k NOTIN (step_taint inst s post tn).t_mem ==>
  w2n dstT+k NOTIN (step_taint instT t postT un).t_mem
Proof
  strip_tac >>
  (irule ptr_dalloca_writer_taint_transport >>
   reverse conj_tac
   >- (gvs[step_writes_def, source_memory_write_ranges_def,
            fixed_source_write_range_def, range_bytes_def] >> decide_tac) >>
   qexistsl [`inst`, `post`, `s`, `tn`, `w2n dst+k`] >> simp[] >>
   gvs[written_taint_def, SUBSET_DEF] >> metis_tac[arithmeticTheory.EQ_ADD_LCANCEL])
QED

(* The copy input is the pre-state byte, also for overlapping copies.  Only
   the single corresponding read is required, not global memory inclusion. *)
Theorem ptr_dalloca_copy_taint_transport:
  inst.inst_opcode = MCOPY /\ instT.inst_opcode = MCOPY /\
  inst.inst_operands = [d;r;n] /\ instT.inst_operands = [dT;rT;nT] /\
  eval_operand d s = SOME dst /\ eval_operand r s = SOME src /\
  eval_operand n s = SOME sz /\
  eval_operand dT t = SOME dstT /\ eval_operand rT t = SOME srcT /\
  eval_operand nT t = SOME szT /\ k < w2n sz /\ k < w2n szT /\
  (w2n srcT+k IN un.t_mem ==> w2n src+k IN tn.t_mem) /\
  w2n dst+k NOTIN (step_taint inst s post tn).t_mem ==>
  w2n dstT+k NOTIN (step_taint instT t postT un).t_mem
Proof
  strip_tac >> irule ptr_dalloca_writer_taint_transport >>
  reverse conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
           sized_source_write_range_def, range_bytes_def] >> decide_tac) >>
  qexistsl [`inst`, `post`, `s`, `tn`, `w2n dst+k`] >> simp[] >>
  gvs[written_taint_def, arithmeticTheory.ADD_COMM]
QED

Theorem ptr_dalloca_other_writer_clean:
  inst.inst_opcode <> MSTORE /\ inst.inst_opcode <> ISTORE /\
  inst.inst_opcode <> MCOPY /\
  y IN range_bytes (step_writes inst s post) ==>
  y NOTIN (step_taint inst s post tn).t_mem
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (simp[written_taint_def] >>
     namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[] >>
     namedCases_on `rest` ["", "v tail"] >> simp[] >>
     namedCases_on `tail` ["", "n more"] >> simp[] >>
     Cases_on `more` >> simp[]) >>
  simp[step_taint_def, mem_taint_def]
QED
