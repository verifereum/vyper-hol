Theory placeRelayoutOpen
Ancestors
  annassignRelayoutContinue stmtSimDeclMem exprOpenCopies
  stmtLowering context compileEnv exprLowering exprOpenPrimitives

Theorem compile_word_copy_loop_endpoint_open:
  !src dst n loc ctor sa u sb.
    compile_word_copy_loop src dst n LocMemory loc ctor sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_word_copy_loop_def, comp_ignore_bind_def, comp_bind_def] >>
  ntac 17 (pairarg_tac >> simp[]) >>
  strip_tac >> pop_assum mp_tac >>
  simp[new_block_def, block_is_terminated_def] >> strip_tac >> gvs[]
QED

Theorem compile_dynarray_to_storage_endpoint_open:
  !src dst ew ems tr sa u sb.
    compile_dynarray_to_storage src dst ew ems tr sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_dynarray_to_storage_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `ew = 1` >> simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `tr` >> simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
  simp[venomInstTheory.is_terminator_def]
QED

Theorem compile_assign_storage_endpoint_open:
  !cenv dst src tr sloc dty sty info bytes sa sf.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F sloc dty sty info bytes sa = ((),sf) ==>
    ~block_is_terminated sf
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_assign_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `info` >> simp[]
  >- (IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
      >- (pairarg_tac >> simp[] >> strip_tac >>
          drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
          simp[venomInstTheory.is_terminator_def]) >>
      simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[compile_word_copy_loop_endpoint_open])
  >- (PairCases_on `x` >> simp[] >>
      metis_tac[compile_dynarray_to_storage_endpoint_open])
  >- (IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
      >- (pairarg_tac >> simp[] >> strip_tac >>
          drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
          simp[venomInstTheory.is_terminator_def]) >>
      simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[compile_word_copy_loop_endpoint_open]) >>
  PairCases_on `x` >> simp[] >>
  metis_tac[compile_dynarray_to_storage_endpoint_open]
QED

Theorem compile_assign_place_endpoint_open:
  compile_assign_value cenv dst loc src F sloc dty sty info bytes st = ((),sf) /\
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  (sloc = NONE \/ sloc = SOME LocMemory) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated st ==>
  ~block_is_terminated sf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `loc = LocMemory`
  >- (gvs[] >> metis_tac[compile_assign_memory_relayout_open]) >>
  `?tr. loc = if tr then LocTransient else LocStorage` by metis_tac[] >>
  gvs[] >> metis_tac[compile_assign_storage_endpoint_open]
QED

Theorem compile_get_target_ptr_endpoint_open:
  !cfn cenv bt sa tr sb.
    compile_get_target_ptr cfn cenv bt sa = (tr,sb) /\
    ~block_is_terminated sa ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `bt`
  >- (simp[compile_get_target_ptr_def] >>
      rpt CASE_TAC >> simp[comp_return_def] >> rpt strip_tac >> gvs[])
  >- (simp[compile_get_target_ptr_def] >>
      rpt CASE_TAC >> simp[comp_return_def] >> rpt strip_tac >> gvs[])
  >- (simp[compile_get_target_ptr_def, comp_bind_def] >>
      rpt (pairarg_tac >> simp[]) >>
      rpt CASE_TAC >> simp[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      metis_tac[compile_mapping_subscript_open, compile_array_subscript_open]) >>
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[venomInstTheory.is_terminator_def]
QED
