Theory bodyPtrPopBytesWordBoundary
Ancestors bodyPtrPopCompilerBoundary bodyPtrPopBoundaryContract
  exprLowering emitHelper compileEnv venomInst list

Theorem pop_bytestring_word_shape:
  (shift_opc = SAR \/ shift_opc = SHR) /\
  load_bytestring_as_word v shift_opc sa = (r,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    sb.cs_blocks = sa.cs_blocks /\
    EVERY (\i. i.inst_opcode <> ASSERT) t
Proof
  strip_tac >> gvs[] >>
  gvs[load_bytestring_as_word_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >>
  irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_load_bytestring_as_word_boundary:
  (shift_opc = SAR \/ shift_opc = SHR) /\ pop_comp_boundary sa /\
  load_bytestring_as_word v shift_opc sa = (r,sb) ==> pop_comp_boundary sb
Proof
  strip_tac >> drule_at (Pat `_ sa = (_,sb)`) pop_bytestring_word_shape >>
  simp[] >> strip_tac >>
  gvs[pop_comp_boundary_def] >>
  irule pop_boundary_clean_append_no_assert >> simp[]
QED
