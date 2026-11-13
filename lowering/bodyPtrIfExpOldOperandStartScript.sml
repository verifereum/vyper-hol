Theory bodyPtrIfExpOldOperandStart
Ancestors
  bodyPtrIfExpStorageStart bodyPtrIfExpStorageInvariant bodyPtrIfExpAllocSource
  exprSimCopy loweringHalt compileEnv allocationPtr slotCopyExecution
  venomExecSemantics venomState

Theorem ifexp_old_operand_external:
  copy_old_operand st op ==> slot_copy_external st op
Proof
  Cases_on `op` >> simp[copy_old_operand_def, slot_copy_external_def] >>
  metis_tac[ifexp_copy_not_fresh_external, slot_copy_external_def]
QED

Theorem ifexp_alloc_old_operands:
  compile_alloc_buffer n sb = (buf,cs) /\ buf.buf_operand = Var out /\
  copy_old_operand sb src ==>
  (!x. src = Var x ==> x <> out) /\
  copy_old_operand cs src /\ copy_old_operand cs (Var out) /\
  slot_copy_external cs src /\ slot_copy_external cs (Var out)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `copy_old_operand cs src /\ copy_old_operand cs (Var out)` by
    (fs[copy_old_operand_def] >> metis_tac[]) >>
  simp[ifexp_old_operand_external] >>
  metis_tac[copy_old_operand_def]
QED

Theorem ifexp_alloc_old_source:
  compile_alloc_buffer n sb = (buf,cs) /\ buf.buf_operand = Var out /\
  copy_old_operand sb src /\ eval_operand src s = SOME w /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  eval_operand src (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w /\
  op_prov (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u) src = op_prov G src /\
  op_taint (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) src = op_taint tn src /\
  copy_old_operand cs src /\ copy_old_operand cs (Var out) /\
  slot_copy_external cs src /\ slot_copy_external cs (Var out)
Proof
  strip_tac >> drule_all ifexp_alloc_old_operands >> strip_tac >>
  drule_all alloca_step_operand_preserved >> strip_tac >>
  `eval_operand src (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_def]) >>
  metis_tac[alloca_step_operand_prov, alloca_step_operand_taint]
QED
