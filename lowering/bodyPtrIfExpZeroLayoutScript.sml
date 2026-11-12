Theory bodyPtrIfExpZeroLayout
Ancestors bodyPtrIfExpZeroStore bodyPtrIfExpReturnMetadata bodyPtrIfExpLayout bodyPtrIfExpLayoutRefl
  supportedTypes supportedDecls supportedProgram compileVyper bodySim
  compileEnv context exprLowering vyperTypeSystem vyperAST list arithmetic

Theorem ifexp_return_map_supported:
  !decls tops name.
  EVERY (supported_declaration_header tops) decls ==>
  supported_return_type tops (build_func_return_type decls name)
Proof
  Induct >> simp[build_func_return_type_def, supported_return_type_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[supported_declaration_header_def, build_func_return_type_def] >>
  strip_tac
  >~ [`supported_function_return tops vis ret`] >-
    (Cases_on `vis` >> gvs[supported_function_return_def] >>
     rw[] >> metis_tac[supported_return_type_def]) >>
  metis_tac[supported_return_type_def]
QED

Theorem ifexp_frame_return_supported:
  body_inv tops ctx ce cx ==>
  supported_return_type tops (ce.ce_func_return_type name)
Proof
  strip_tac >>
  `ce.ce_func_return_type = build_func_return_type tops /\
   EVERY (supported_declaration_header tops) tops` by
    gvs[body_inv_def, supported_program_def, supported_declaration_headers_def] >>
  metis_tac[ifexp_return_map_supported]
QED

Theorem ifexp_supported_scalar_positive:
  supported_scalar_type ty ==> 0 < type_memory_bytes ce ty
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def, supported_string_type_def] >>
  Cases_on `b` >>
  gvs[supported_word_type_def, supported_string_type_def, type_memory_bytes_def] >>
  Cases_on `b'` >> gvs[supported_word_type_def, supported_string_type_def, type_memory_bytes_def]
QED

Theorem ifexp_scalar_sizes_zero:
  !tys. EVERY supported_scalar_type tys ==>
  (SUM (MAP (type_memory_bytes ce) tys) = 0 <=> tys = [])
Proof
  Induct_on `tys` >> simp[] >> rpt strip_tac >>
  `0 < type_memory_bytes ce h` by metis_tac[ifexp_supported_scalar_positive] >>
  simp[]
QED

Theorem ifexp_supported_zero_struct:
  supported_value_type tops ty /\ type_memory_bytes ce ty = 0 ==>
  ?id. ty = StructT id
Proof
  strip_tac >>
  `~supported_scalar_type ty` by
    (strip_tac >> drule ifexp_supported_scalar_positive >>
     disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
  Cases_on `ty` >> gvs[supported_value_type_def]
  >~ [`TupleT tys`] >-
    (gvs[type_memory_bytes_def] >>
     drule ifexp_scalar_sizes_zero >> disch_then (qspec_then `ce` mp_tac) >>
     gvs[listTheory.NULL_EQ, SF ETA_ss]) >>
  Cases_on `b` >> gvs[type_memory_bytes_def] >>
  `supported_scalar_type t` by simp[supported_scalar_type_def] >>
  drule ifexp_supported_scalar_positive >> disch_then (qspec_then `ce` mp_tac) >> simp[]
QED

Theorem ifexp_supported_zero_widening_eq:
  supported_return_type tops sty /\ type_memory_bytes ce sty = 0 /\
  type_widens_to tenv sty dty ==> sty = dty
Proof
  strip_tac >> gvs[supported_return_type_def] >>
  drule_all ifexp_supported_zero_struct >> strip_tac >> gvs[] >>
  Cases_on `dty` >> gvs[type_widens_to_def, arg_type_fits_def]
QED

Theorem ifexp_zero_call_annotation_eq:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args dret) es /\
  ce.ce_func_info (nsid_to_string fid) = (0,0,pvs) ==>
  ce.ce_func_return_type (nsid_to_string fid) = ann
Proof
  strip_tac >>
  `supported_return_type tops (ce.ce_func_return_type (nsid_to_string fid))` by
    metis_tac[ifexp_frame_return_supported] >>
  drule_all ifexp_call_annotation_widens >> strip_tac >>
  drule_all ifexp_internal_call_zero_extent >> strip_tac
  >- gvs[] >>
  drule_all ifexp_supported_zero_widening_eq >> simp[]
QED

Theorem ifexp_zero_call_layout:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args dret) es /\
  ce.ce_func_info (nsid_to_string fid) = (0,0,pvs) ==>
  same_memory_layout ce (lowered_value_type ce (Call ann (IntCall fid) args dret)) ann
Proof
  strip_tac >> drule_all ifexp_zero_call_annotation_eq >>
  simp[lowered_value_type_def, same_memory_layout_reflexive]
QED
