Theory tupleWidenedStoreOpen
Ancestors
  tupleWidenedTargetStore tupleTargetStoreRun tupleTargetStoreProps
  stmtLowering exprLowering exprLoweringProps exprOpenCopies exprOpenPrimitives compileEnv

Theorem tuple_store_widened_singleton_open:
  tuple_compiler_target cenv g dty /\
  (is_word_type sty = is_word_type dty) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  ~block_is_terminated sa /\
  compile_tuple_store_all cenv [sty] [g] [op] sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >> Cases_on `is_word_type sty`
  >- (`is_word_type dty` by fs[] >>
      mp_tac (tuple_word_source_code |> Q.INST [`ce` |-> `cenv`]) >>
      simp[] >> strip_tac >>
      irule tuple_store_singleton_open >>
      qpat_assum `tuple_compiler_target _ _ _` (irule_at Any) >>
      metis_tac[]) >>
  gvs[tuple_compiler_target_def] >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_store_all_def, compile_get_target_ptr_def,
       compile_store_at_loc_def, compile_assign_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[compile_store_memory_open]
QED
