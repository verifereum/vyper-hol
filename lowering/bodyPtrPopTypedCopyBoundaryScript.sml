Theory bodyPtrPopTypedCopyBoundary
Ancestors bodyPtrPopCopyBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopMaterialization context compileEnv emitHelper list

Theorem pop_typed_copy_boundary_mutual:
  (!cenv dst dty src sty sa r sb.
    pop_comp_boundary sa /\
    compile_store_memory_typed cenv dst dty src sty sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!cenv dst src dtys stys doff soff sa r sb.
    pop_comp_boundary sa /\
    compile_typed_copy_fields cenv dst src dtys stys doff soff sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!cenv dst dty src sty n sa r sb.
    pop_comp_boundary sa /\
    compile_copy_sarray_typed cenv dst dty src sty n sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!cenv dst dty cap src sty sa r sb.
    pop_comp_boundary sa /\
    compile_copy_dynarray_typed cenv dst dty cap src sty sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!cenv dst src dfs sfs doff soff sa r sb.
    pop_comp_boundary sa /\
    compile_struct_typed_copy cenv dst src dfs sfs doff soff sa = (r,sb) ==>
    pop_comp_boundary sb)
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "store"
  >- suspend "fields_nil"
  >- suspend "fields_missing"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED

Resume pop_typed_copy_boundary_mutual[fields_nil]:
  simp[Once compile_store_memory_typed_def] >> rpt strip_tac >>
  drule_all pop_comp_boundary_return >> simp[]
QED

Resume pop_typed_copy_boundary_mutual[fields_missing]:
  simp[Once compile_store_memory_typed_def] >> rpt strip_tac >>
  drule_all pop_comp_boundary_return >> simp[]
QED

Resume pop_typed_copy_boundary_mutual[struct_nil]:
  simp[Once compile_store_memory_typed_def] >> rpt strip_tac >>
  drule_all pop_comp_boundary_return >> simp[]
QED

Resume pop_typed_copy_boundary_mutual[fields_cons]:
  rpt strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_with_byte_offset_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_with_byte_offset_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac >> rpt strip_tac >> metis_tac[]
QED

Resume pop_typed_copy_boundary_mutual[struct_cons]:
  rpt strip_tac >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_with_byte_offset_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_with_byte_offset_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac >> rpt strip_tac >> metis_tac[]
QED

Resume pop_typed_copy_boundary_mutual[store]:
  rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `is_word_type dty`
  >- (ntac 4 (qpat_x_assum `!dty'. _` kall_tac) >>
      simp[comp_ignore_bind_def] >> strip_tac >>
      drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
      disch_then irule >> simp[] >> conj_tac
      >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`)
            pop_emit_op_boundary >> simp[]) >>
      rpt strip_tac >> drule_at (Pat `emit_void _ _ _ = _`)
        pop_emit_void_boundary >> simp[]) >>
  Cases_on `is_bytestring_type dty /\ is_bytestring_type sty`
  >- (simp[] >> strip_tac >> drule_all pop_compile_store_bytestring_boundary >> simp[]) >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (qpat_assum `~is_word_type dty` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `~(is_bytestring_type dty /\ is_bytestring_type sty)`
        (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `acyclic_struct_metadata _` (fn th => pure_rewrite_tac[th]) >>
      pure_rewrite_tac[COND_CLAUSES, NOT_CLAUSES] >>
      Cases_on `dty` >> Cases_on `sty` >>
      simp_tac pure_ss [TypeBase.case_def_of ``:type``, pairTheory.pair_case_def] >>
      TRY (rename1 `compile_copy_memory _ _ _ _ = _ ==> _` >>
           strip_tac >> drule_all pop_compile_copy_memory_boundary >>
           simp[NoAsms] >> NO_TAC) >>
      rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
      IF (rename1 `~is_word_type (ArrayT et dsz)`)
        (qmatch_goalsub_rename_tac `case ssz of Fixed _ => _ | Dynamic _ => _` >>
         Cases_on `dsz` >> Cases_on `ssz` >>
         simp_tac pure_ss [TypeBase.case_def_of ``:bound``]) all_tac >>
      simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
      metis_tac[pop_compile_copy_memory_boundary]) >>
  simp[] >> strip_tac >> drule_at (Pat `emit_void _ _ _ = _`)
    pop_emit_void_boundary >> simp[]
QED

Resume pop_typed_copy_boundary_mutual[sarray]:
  rpt strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  simp_tac (srw_ss()) [LET_THM, comp_ignore_bind_def] >>
  IF_CASES_TAC
  >- (strip_tac >> drule_all pop_compile_copy_memory_boundary >> simp[]) >>
  strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  TRY (FIRST [drule_all pop_fresh_label_boundary,
              drule_all pop_fresh_var_boundary,
              drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
              drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
              drule_all pop_comp_boundary_new_block,
              drule_all pop_comp_boundary_return] >> simp[] >> NO_TAC) >>
  metis_tac[]
QED

Resume pop_typed_copy_boundary_mutual[dynarray]:
  rpt strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  CONV_TAC (ONCE_DEPTH_CONV (HO_REWR_CONV pop_typed_capacity_cont_factor)) >>
  strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_typed_capacity_boundary >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [comp_ignore_bind_def] >>
  qpat_x_assum `_ sa = _` kall_tac >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty` >>
  gvs[comp_ignore_bind_def] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  TRY (FIRST [drule_all pop_fresh_label_boundary,
              drule_all pop_fresh_var_boundary,
              drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
              drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
              drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
              drule_all pop_compile_copy_memory_dynamic_boundary,
              drule_all pop_comp_boundary_new_block,
              drule_all pop_comp_boundary_return] >> simp[] >> NO_TAC) >>
  metis_tac[]
QED

Finalise pop_typed_copy_boundary_mutual

Theorem pop_compile_store_memory_typed_boundary:
  pop_comp_boundary sa /\
  compile_store_memory_typed cenv dst dty src sty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_typed_copy_boundary_mutual]
QED

Theorem pop_compile_typed_copy_fields_boundary:
  pop_comp_boundary sa /\
  compile_typed_copy_fields cenv dst src dtys stys doff soff sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_typed_copy_boundary_mutual]
QED

Theorem pop_compile_copy_sarray_typed_boundary:
  pop_comp_boundary sa /\
  compile_copy_sarray_typed cenv dst dty src sty n sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_typed_copy_boundary_mutual]
QED

Theorem pop_compile_copy_dynarray_typed_boundary:
  pop_comp_boundary sa /\
  compile_copy_dynarray_typed cenv dst dty cap src sty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_typed_copy_boundary_mutual]
QED

Theorem pop_compile_struct_typed_copy_boundary:
  pop_comp_boundary sa /\
  compile_struct_typed_copy cenv dst src dfs sfs doff soff sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_typed_copy_boundary_mutual]
QED

Theorem pop_compile_store_memory_boundary:
  pop_comp_boundary sa /\
  compile_store_memory cenv src dst dty sty sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `is_word_type dty` >>
  Cases_on `is_bytestring_type dty` >> Cases_on `dty = sty` >>
  simp[compile_store_memory_def] >> rpt strip_tac >>
  FIRST [drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_compile_store_bytestring_boundary,
         drule_all pop_compile_store_memory_typed_boundary,
         drule_all pop_compile_copy_memory_boundary] >> simp[]
QED
