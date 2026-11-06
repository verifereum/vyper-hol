(* Code boundaries for the two allocations and two straight instructions
   that initialize concat's result buffer and offset scratch. *)
Theory bodyMemBiConcatPrefix
Ancestors
  bodyMemAggregateAlloc bodyMemEmitOpFrame bodyDeclWordMemory
  exprSimConcatResult fragExec context emitHelper emitHelperProps
  exprLoweringProps loweringHalt compileEnv list rich_list

Theorem concat_prefix_code_cuts:
  context$compile_alloc_buffer bsz sa = (buf,s1) /\
  emit_op ADD [buf.buf_operand; Lit 32w] s1 = (d,s2) /\
  context$compile_alloc_buffer 64 s2 = (ob,s3) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u,s4) /\
  fn_has_code sa s4 func ==>
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func
Proof
  strip_tac >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 s4` by
    (gvs[contextTheory.compile_alloc_buffer_def, comp_bind_def,
         comp_return_def, emit_op_def, emit_void_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt conj_tac >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends s1 s4 /\ cs_extends s2 s4` by
    metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED
