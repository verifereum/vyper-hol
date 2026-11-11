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
  exprSimHypsDefs
  exprOpenPrimitives exprOpenTerminals exprLowering context compileEnv
  supportedExprForms supportedTypes typedCopyMetadata list rich_list pair alist finite_map venomInst
  structFieldsProps  vyperTypeInvariants vyperTypeSystem

Theorem compile_copy_memory_open[local]:
  !dst src n sa r sb.
    ~block_is_terminated sa /\ compile_copy_memory dst src n sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `n` >>
  simp[compile_copy_memory_def, comp_return_def] >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_with_byte_offset_open[local]:
  !base off sa r sb.
    ~block_is_terminated sa /\ compile_with_byte_offset base off sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rw[compile_with_byte_offset_def] >> gvs[comp_return_def] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

(* Past the word and bytestring cases, acyclic metadata sends the typed
   copy to one of its helpers or to a plain copy. *)
Theorem compile_store_memory_typed_complex_cases[local]:
  !cenv dst dst_ty src src_ty sa r sb.
    ~is_word_type dst_ty /\
    ~(is_bytestring_type dst_ty /\ is_bytestring_type src_ty) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    compile_store_memory_typed cenv dst dst_ty src src_ty sa = (r,sb) ==>
    (?de dc se sc. dst_ty = ArrayT de (Dynamic dc) /\
       src_ty = ArrayT se (Dynamic sc) /\
       compile_copy_dynarray_typed cenv dst de dc src se sa = (r,sb)) \/
    (?de n se m. dst_ty = ArrayT de (Fixed n) /\ src_ty = ArrayT se (Fixed m) /\
       compile_copy_sarray_typed cenv dst de src se n sa = (r,sb)) \/
    (?ds ss. dst_ty = TupleT ds /\ src_ty = TupleT ss /\
       compile_typed_copy_fields cenv dst src ds ss 0 0 sa = (r,sb)) \/
    (?dn sn. dst_ty = StructT dn /\ src_ty = StructT sn /\
       compile_struct_typed_copy cenv dst src
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string dn))
         (get_struct_fields cenv.ce_struct_fields (nsid_to_string sn)) 0 0 sa =
       (r,sb)) \/
    compile_copy_memory dst src (type_memory_bytes cenv dst_ty) sa = (r,sb)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, LET_THM] >>
  Cases_on `src_ty` >> simp[] >>
  Cases_on `dst_ty` >> simp[] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[]
QED

(* With acyclic struct metadata the typed copy never takes its INVALID
   fallback: word and bytestring stores, MCOPY fast paths, and per-field
   copies keep the block open, and the array loops end by opening their
   exit block. *)
Theorem compile_store_memory_typed_open_family[local]:
  (!cenv dst dst_ty src src_ty sa r sb.
     acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa /\
     compile_store_memory_typed cenv dst dst_ty src src_ty sa = (r,sb) ==>
     ~block_is_terminated sb) /\
  (!cenv dst src dst_tys src_tys dst_off src_off sa r sb.
     acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa /\
     compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off sa =
       (r,sb) ==>
     ~block_is_terminated sb) /\
  (!cenv dst dst_ty src src_ty count sa r sb.
     acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa /\
     compile_copy_sarray_typed cenv dst dst_ty src src_ty count sa = (r,sb) ==>
     ~block_is_terminated sb) /\
  (!cenv dst dst_ty cap src src_ty sa r sb.
     acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa /\
     compile_copy_dynarray_typed cenv dst dst_ty cap src src_ty sa = (r,sb) ==>
     ~block_is_terminated sb) /\
  (!cenv dst src dst_fields src_fields dst_off src_off sa r sb.
     acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa /\
     compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off
       sa = (r,sb) ==>
     ~block_is_terminated sb)
Proof
  ho_match_mp_tac compile_store_memory_typed_ind
  >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, comp_return_def]
  >- simp[Once compile_store_memory_typed_def, comp_return_def]
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, comp_return_def]
  >> suspend "struct_cons"
QED

Resume compile_store_memory_typed_open_family[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dst_ty`
  >- (gvs[Once compile_store_memory_typed_def, comp_bind_def] >>
      pairarg_tac >> gvs[] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
  >- (gvs[Once compile_store_memory_typed_def] >>
      gvs[compile_store_bytestring_def, comp_bind_def] >>
      pairarg_tac >> gvs[] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  drule_all compile_store_memory_typed_complex_cases >> strip_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  metis_tac[compile_copy_memory_open]
QED

Resume compile_store_memory_typed_open_family[fields_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  imp_res_tac compile_with_byte_offset_open >>
  imp_res_tac compile_with_byte_offset_open >>
  metis_tac[]
QED

Resume compile_store_memory_typed_open_family[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, LET_THM] >>
  IF_CASES_TAC >- metis_tac[compile_copy_memory_open] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[new_block_open]
QED

Resume compile_store_memory_typed_open_family[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, LET_THM] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  IF_CASES_TAC
  >- (simp[comp_bind_def, compile_copy_memory_dynamic_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[new_block_open]
QED

Resume compile_store_memory_typed_open_family[struct_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP src_fields name` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  imp_res_tac compile_with_byte_offset_open >>
  imp_res_tac compile_with_byte_offset_open >>
  metis_tac[]
QED

Finalise compile_store_memory_typed_open_family

Theorem compile_store_memory_typed_open:
  !cenv dst dst_ty src src_ty sa r sb.
    acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa /\
    compile_store_memory_typed cenv dst dst_ty src src_ty sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  metis_tac[compile_store_memory_typed_open_family]
QED

Theorem compile_store_memory_open:
  !cenv src dst dty sty sa r sb.
    (is_word_type dty \/ is_bytestring_type dty \/ dty = sty \/
     acyclic_struct_metadata cenv.ce_struct_fields) /\
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
  Cases_on `dty = sty`
  >- (simp[] >> metis_tac[compile_copy_memory_open]) >>
  Cases_on `tuple_memory_layout_eq dty sty`
  >- (simp[] >> metis_tac[compile_copy_memory_open]) >>
  simp[] >> metis_tac[compile_store_memory_typed_open]
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
    acyclic_struct_metadata cenv.ce_struct_fields /\
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
    acyclic_struct_metadata cenv.ce_struct_fields /\
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
    acyclic_struct_metadata cenv.ce_struct_fields /\
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
    acyclic_struct_metadata cenv.ce_struct_fields /\
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
