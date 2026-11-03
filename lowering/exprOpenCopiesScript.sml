(*
 * compile_expr keeps its block open: aggregate literals
 *
 * TOP-LEVEL:
 *   compile_store_memory_open — a memory store to a word, a bytestring
 *                               or the source's own type
 *   compile_make_tuple_open, compile_make_array_open,
 *   compile_struct_lit_open   — tuple, array and struct literals
 *)

Theory exprOpenCopies
Ancestors
  exprOpenPrimitives exprOpenTerminals exprLowering context compileEnv
  supportedExprForms supportedTypes typedCopyMetadata list rich_list pair alist finite_map venomInst
  exprSimAggregateLayout exprSimHyps vyperTypeInvariants vyperTypeSystem

Theorem compile_store_memory_open:
  !cenv src dst dty sty sa r sb.
    (is_word_type dty \/ is_bytestring_type dty \/ dty = sty) /\
    ~block_is_terminated sa /\
    compile_store_memory cenv src dst dty sty sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_store_memory_def] >>
  Cases_on `is_word_type dty`
  >- (simp[] >> strip_tac >> drule emit_void_terminated >> simp[is_terminator_def]) >>
  Cases_on `is_bytestring_type dty`
  >- (simp[compile_store_bytestring_def, comp_bind_def] >>
      pairarg_tac >> simp[] >> strip_tac >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  Cases_on `type_memory_bytes cenv dty` >>
  gvs[compile_copy_memory_def, comp_return_def] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem supported_copy_types_store_path:
  !dst src.
    supported_copy_types dst src ==>
    is_word_type dst \/ is_bytestring_type dst \/ dst = src
Proof
  rpt gen_tac >> simp[supported_copy_types_def] >> strip_tac
  >- simp[]
  >- metis_tac[supported_word_type_is_word] >>
  Cases_on `dst` >> Cases_on `src` >>
  gvs[AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `is_word_type (BaseT dst_base) \/ _ \/ dst_base = src_base` >>
  Cases_on `dst_base` >> Cases_on `src_base` >>
  gvs[AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `is_word_type (BaseT (BytesT dst_bound)) \/ _ \/ dst_bound = src_bound` >>
  Cases_on `dst_bound` >> Cases_on `src_bound` >>
  gvs[is_bytestring_type_def]
QED

Theorem compile_make_tuple_open:
  !cfn cenv es buf off sa r sb.
    ~block_is_terminated sa /\
    compile_make_tuple cfn cenv es buf off sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  Induct_on `es` >- (simp[compile_make_tuple_def, comp_return_def] >> metis_tac[]) >>
  rpt gen_tac >>
  simp[compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def] >> disch_tac >>
  drule_all unwrap_value_open >> disch_tac >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    compile_store_memory_open >> simp[] >> disch_tac >>
  metis_tac[]
QED

Theorem compile_make_array_elems_open:
  !cfn cenv es elem size lw buf idx sa r sb.
    EVERY (\e. is_word_type elem \/ is_bytestring_type elem \/ elem = expr_type e) es /\
    ~block_is_terminated sa /\
    compile_make_array_elems cfn cenv es elem size lw buf idx sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  Induct_on `es`
  >- (simp[compile_make_array_elems_def, comp_return_def] >> metis_tac[]) >>
  rpt gen_tac >>
  simp[compile_make_array_elems_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def] >> disch_tac >>
  drule_all unwrap_value_open >> disch_tac >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    compile_store_memory_open >> simp[] >> disch_tac >> metis_tac[]
QED

Theorem compile_make_array_open:
  !cfn cenv es elem size lw buf sa r sb.
    EVERY (\e. is_word_type elem \/ is_bytestring_type elem \/ elem = expr_type e) es /\
    ~block_is_terminated sa /\
    compile_make_array cfn cenv es elem size lw buf sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_make_array_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  irule compile_make_array_elems_open >>
  goal_assum (drule_at (Pat `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> Cases_on `lw` >> gvs[comp_return_def] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_struct_lit_open:
  !cfn cenv ty fields buf off sa r sb.
    (!name e fty sz.
       MEM (name,e) fields /\
       ALOOKUP (get_struct_fields cenv.ce_struct_fields
         (case ty of StructT n => nsid_to_string n | _ => "")) name = SOME (fty,sz) ==>
       is_word_type fty \/ is_bytestring_type fty \/ fty = expr_type e) /\
    ~block_is_terminated sa /\
    compile_struct_lit cfn cenv ty fields buf off sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  Induct_on `fields`
  >- (simp[compile_struct_lit_def, comp_return_def] >> metis_tac[]) >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_struct_lit_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def] >> disch_tac >>
  drule_all unwrap_value_open >> disch_tac >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    compile_store_memory_open >> simp[] >>
  impl_tac
  >- (BasicProvers.TOP_CASE_TAC >> gvs[] >>
      qmatch_goalsub_rename_tac `case fld_pair of (fty,sz) => fty` >>
      PairCases_on `fld_pair` >> gvs[] >>
      metis_tac[]) >>
  disch_tac >> first_x_assum irule >>
  goal_assum (drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem aligned_fields_lookup_type[local]:
  !values fields f key e ty size.
    MAP FST fields = MAP FST values /\
    MAP (FST o SND) fields = MAP (f o SND) values /\
    ALL_DISTINCT (MAP FST fields) /\ MEM (key,e) values /\
    ALOOKUP fields key = SOME (ty,size) ==> ty = f e
Proof
  Induct_on `values` >- simp[] >>
  rpt gen_tac >> Cases_on `fields` >> simp[] >>
  PairCases_on `h` >> rename1 `ALOOKUP (fld::rest) _ = SOME _` >>
  PairCases_on `fld` >>
  simp[] >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs()]
  >- (qpat_x_assum `!fields f key e ty size. _` kall_tac >>
      metis_tac[MEM_MAP_f, FST]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem struct_literal_store_paths:
  !cenv cx env ann nsid kes es.
    expr_sim_inv cenv cx env es /\ well_typed_expr env (StructLit ann nsid kes) ==>
    !name e fty sz.
      MEM (name,e) kes /\
      ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid)) name =
        SOME (fty,sz) ==> fty = expr_type e
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    gvs[expr_sim_inv_def] >>
  drule_all struct_literal_layout_types >> strip_tac >>
  `ALL_DISTINCT (MAP FST fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  rpt gen_tac >> simp[get_struct_fields_def] >> strip_tac >>
  drule_all aligned_fields_lookup_type >> simp[]
QED
