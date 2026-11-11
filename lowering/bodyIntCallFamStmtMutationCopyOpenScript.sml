Theory bodyIntCallFamStmtMutationCopyOpen
Ancestors
  stmtLowering exprOpenCopies exprOpenPrimitives compileEnv bodySim
Libs
  monadsyntax

Theorem intcall_memory_copy_open:
  (is_word_type dty \/ is_bytestring_type dty \/ dty = sty \/
   acyclic_struct_metadata ce.ce_struct_fields) /\
  ~block_is_terminated sa /\
  compile_assign_value ce dst LocMemory src F loc dty sty info bytes sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  simp[compile_assign_value_def] >>
  Cases_on `loc = SOME LocMemory` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac)
  >- (drule compile_alloc_buffer_open >> strip_tac >>
      rename1 `compile_copy_memory tmp src (type_memory_bytes ce sty) s1 = (r,s2)` >>
      `compile_store_memory ce src tmp (TupleT [sty]) (TupleT [sty]) s1 = (r,s2)` by
        simp[contextTheory.compile_store_memory_def, is_word_type_def,
             is_bytestring_type_def, type_memory_bytes_def] >>
      `~block_is_terminated s2` by
        (irule compile_store_memory_open >>
         goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
         simp[]) >>
      irule compile_store_memory_open >> metis_tac[]) >>
  irule compile_store_memory_open >> metis_tac[]
QED
