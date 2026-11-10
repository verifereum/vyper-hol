Theory placeRelayoutOpen
Ancestors
  annassignRelayoutContinue stmtSimDeclMem exprOpenCopies stmtSimAssignStorageSparse
  stmtLowering context compileEnv exprLowering exprOpenPrimitives

Theorem compile_assign_storage_endpoint_open:
  !cenv dst src tr sloc dty sty bytes sa sf.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F sloc dty sty bytes sa = ((),sf) /\
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    ~block_is_terminated sf
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_assign_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  metis_tac[cj 1 store_slots_open]
QED

Theorem compile_assign_place_endpoint_open:
  compile_assign_value cenv dst loc src F sloc dty sty bytes st = ((),sf) /\
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
      CASE_TAC >> simp[comp_return_def] >- (rpt strip_tac >> gvs[]) >>
      CASE_TAC >> simp[comp_return_def] >> rpt strip_tac >> gvs[])
  >- (simp[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars p`
      >- (simp[comp_return_def] >> rpt strip_tac >> gvs[]) >>
      rename1 `SOME loc` >> Cases_on `loc` >>
      simp[comp_return_def] >> rpt strip_tac >> gvs[])
  >- (simp[compile_get_target_ptr_def, comp_bind_def] >>
      rpt (pairarg_tac >> simp[]) >>
      Cases_on `SND (SND result)`
      >- (simp[comp_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          metis_tac[compile_array_subscript_open]) >>
      rename1 `SOME pt` >> Cases_on `pt` >>
      simp[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      metis_tac[compile_mapping_subscript_open, compile_array_subscript_open]) >>
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[venomInstTheory.is_terminator_def]
QED
