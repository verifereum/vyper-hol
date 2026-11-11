(* Isolate compiler layout from the unavailable semantic Convert ancestor. *)
Theory assignBasePtrWidenLayout
Ancestors exprSimAlloc exprLoweringProps emitHelperProps exprLowering context
  compileEnv loweringStateRelDefs fragExec words list

Theorem assign_base_widen_parts[local]:
  !d x k sm op sb.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\ 0 < k ==>
    ?buf mid. compile_alloc_buffer d sm = (buf,mid) /\
      op = buf.buf_operand /\
      emit_void MCOPY [buf.buf_operand; x; Lit (n2w k)] mid = ((),sb)
Proof
  rpt gen_tac >> Cases_on `k` >> simp[] >>
  simp[compile_bytestring_widen_copy_def, contextTheory.compile_copy_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem assign_base_widen_code:
  !d x k sm op sb func.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\ 0 < k /\
    fn_has_code sm sb func ==>
    ?buf mid inst p.
      compile_alloc_buffer d sm = (buf,mid) /\ op = buf.buf_operand /\
      buf.buf_operand = Var p /\ ~not_fresh_at sm p /\
      emit_void MCOPY [Var p; x; Lit (n2w k)] mid = ((),sb) /\
      ci_mono sm mid /\ ci_mono mid sb /\
      fn_has_code sm mid func /\ fn_has_code mid sb func /\
      MEM inst (fn_insts func) /\ inst.inst_id = sm.cs_next_id /\
      inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p]
Proof
  rpt strip_tac >> drule_all assign_base_widen_parts >> strip_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`d`, `sm`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid sb` by
    (qspecl_then [`MCOPY`, `[buf.buf_operand; x; Lit (n2w k)]`, `mid`]
       mp_tac ci_mono_emit_void >> simp[]) >>
  `fn_has_code sm mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `emit_op ALLOCA [Lit (n2w d)] sm = (buf.buf_operand,mid)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qexistsl_tac [`buf`, `mid`,
    `mk_inst sm.cs_next_id ALLOCA [Lit (n2w d)]
       [STRING #"%" (toString sm.cs_next_var)]`,
    `STRING #"%" (toString sm.cs_next_var)`] >>
  gvs[venomInstTheory.mk_inst_def, not_fresh_at_def]
QED
