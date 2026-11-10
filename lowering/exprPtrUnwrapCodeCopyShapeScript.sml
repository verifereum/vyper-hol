(* Runtime code forcing has one allocation followed by an unrolled copy. *)
Theory exprPtrUnwrapCodeCopyShape
Ancestors
  exprPtrUnwrapCodeEdges exprPtrCodeCopyInduction exprLoweringProps
  loweringHalt fragExec compileEnv loweringStateRelDefs exprLowering pair arithmetic emitHelper
  exprSimCopy ASCIInumbers context

Theorem ensure_runtime_code_layout:
  compile_ensure_in_memory src LocCode nb n F imm sa = (op,sb) /\
  fn_has_code sa sb func ==>
  ?buf mid.
    compile_alloc_buffer nb sa = (buf,mid) /\ op = buf.buf_operand /\
    compile_imm_copy_to_memory F imm src buf.buf_operand ((nb+31) DIV 32) 0 mid = ((),sb) /\
    fn_has_code sa mid func /\ fn_has_code mid sb func /\
    sa.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= sb.cs_next_var
Proof
  simp[ensure_code_copy_route, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    pairTheory.pair_case_eq] >> rpt strip_tac >>
  Cases_on `compile_alloc_buffer nb sa` >>
  Cases_on `compile_imm_copy_to_memory F imm src q.buf_operand ((nb+31) DIV 32) 0 r` >>
  gvs[] >> rename1 `compile_alloc_buffer nb sa = (buf,mid)` >>
  rename1 `compile_imm_copy_to_memory F imm src buf.buf_operand _ 0 mid = ((),sb)` >>
  `cs_extends sa mid` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends mid sb /\ mid.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_imm_copy_to_memory, ci_mono_def, SND] >>
  `sa.cs_next_var <= mid.cs_next_var` by
    (mp_tac (Q.SPECL [`nb`, `sa`] ci_mono_compile_alloc_buffer) >>
     asm_rewrite_tac[] >> simp[ci_mono_def]) >>
  drule_all fn_has_code_split >> simp[] >> metis_tac[]
QED

Theorem allocated_copy_operands_old:
  compile_alloc_buffer nb sa = (buf,mid) /\ buf.buf_operand = Var root /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  copy_old_operand mid src /\ not_fresh_at mid root
Proof
  strip_tac >>
  gvs[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  simp[exprSimCopyTheory.copy_old_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[not_fresh_at_def] >> rpt strip_tac >>
  strip_tac >> gvs[ASCIInumbersTheory.toString_inj] >> decide_tac
QED
