Theory assignValueMemoryOpen
Ancestors
  stmtLowering exprOpenCopies exprOpenPrimitives compileEnv

Theorem compile_assign_value_memory_open:
  !cenv dst src loc dty sty info bytes sa sb.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    ~block_is_terminated sa /\
    compile_assign_value cenv dst LocMemory src F loc dty sty info bytes sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = SOME LocMemory`
  >- (gvs[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      drule compile_alloc_buffer_open >> strip_tac >>
      drule_all compile_copy_memory_open >> strip_tac >>
      drule_at (Pos last) compile_store_memory_open >> simp[]) >>
  gvs[compile_assign_value_def] >>
  drule_at (Pos last) compile_store_memory_open >> simp[]
QED
