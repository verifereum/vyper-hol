Theory bodyPtrIfExpStorageStart
Ancestors
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocSource allocationPtr
  slotCopyExecution emitHelperProps loweringHalt compileEnv loweringStateRelDefs exprLowering
  context emitHelper
  venomExecSemantics venomInst venomState finite_map

Theorem ifexp_alloc_source_exclusion:
  compile_alloc_buffer n sb = (buf,cs) /\ buf.buf_operand = Var out /\
  fresh_vars_wrt sb s /\ eval_operand src s = SOME w ==>
  (!x. src = Var x ==> x <> out)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  Cases_on `src` >> gvs[eval_operand_def, lookup_var_def] >>
  fs[fresh_vars_wrt_def, FLOOKUP_DEF] >>
  first_x_assum (qspec_then `sb.cs_next_var` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ifexp_alloc_start_fresh:
  compile_alloc_buffer n sb = (buf,cs) /\ buf.buf_operand = Var out /\
  fresh_vars_wrt sb s /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  fresh_vars_wrt cs (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
  >- (strip_tac >> gvs[fresh_vars_wrt_def, update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[fresh_vars_wrt_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ifexp_alloc_start_source:
  compile_alloc_buffer n sb = (buf,cs) /\ buf.buf_operand = Var out /\
  fresh_vars_wrt sb s /\ eval_operand src s = SOME w /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  eval_operand src (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w /\
  op_prov (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u) src = op_prov G src /\
  op_taint (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) src = op_taint tn src /\
  slot_copy_external cs src
Proof
  strip_tac >>
  `!x. src = Var x ==> x <> out` by
    (metis_tac[ifexp_alloc_source_exclusion]) >>
  drule_all alloca_step_operand_preserved >> strip_tac >>
  drule_all ifexp_alloc_start_fresh >> strip_tac >>
  `eval_operand src (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_def]) >>
  metis_tac[alloca_step_operand_prov, alloca_step_operand_taint,
            slot_copy_fresh_operand_external]
QED

Theorem ifexp_alloc_start_cursor:
  compile_alloc_buffer n sb = (buf,cs) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\ n < dimword (:256) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  (u with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb = cs.cs_current_bb /\
  (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = LENGTH cs.cs_current_insts
Proof
  strip_tac >> drule_all alloca_step_contracts >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> strip_tac >> gvs[]
QED

Theorem ifexp_alloc_start_destination_external:
  compile_alloc_buffer n sb = (buf,cs) /\ buf.buf_operand = Var out /\
  fresh_vars_wrt sb s /\ ptr_covers G1 tn1 out
    (u with vs_inst_idx := SUC s.vs_inst_idx) n /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  slot_copy_external cs buf.buf_operand
Proof
  strip_tac >> drule_all ifexp_alloc_start_fresh >> strip_tac >>
  irule slot_copy_fresh_operand_external >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, eval_operand_def, lookup_var_def]
QED
