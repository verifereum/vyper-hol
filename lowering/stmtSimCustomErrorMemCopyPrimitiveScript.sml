Theory stmtSimCustomErrorMemCopyPrimitive
Ancestors
  placeMemoryTypedPrimitive bodyCopyMemory exprSimMemUnwrap
  externalReturnNormalizeMem list venomState venomExecSemantics
  placeMemoryTypedBase exprSimBufferStore bodyMemAggregateStore
  context compileEnv exprLoweringProps valueCopyBytes typedCopyAgreement
  vfmConstants

Theorem compile_copy_memory_checked_path:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  let t = (if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
            with vs_inst_idx := LENGTH sb.cs_current_insts in
  gas_path_mem ctx func s 0 (OK t) /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  drule_all compile_copy_memory_sequence >> strip_tac >>
  drule_all compile_copy_memory_body_mem_ok >> strip_tac >>
  simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := _))` >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[EVERY_MEM] >> gvs[EVERY_MEM]) >>
  simp[] >> Cases_on `n = 0` >>
  gvs[Abbr `u`, mcopy_def, write_memory_with_expansion_def]
QED
