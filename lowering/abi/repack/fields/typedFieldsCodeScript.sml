(* TOP-LEVEL: a tuple field step exposes its two actual address actions,
   recursive typed child, remaining fields, and all containing code spans. *)
Theory typedFieldsCode
Ancestors
  typedCopyOffset typedCopyAppend compileAppendProps typedCopyVarFlow compileVarFlow context compileEnv
  fragExec list pair

Theorem compile_store_memory_typed_extends =
  REWRITE_RULE [cs_appends_def] (CONJUNCT1 cs_appends_typed_copy_mutual);

Theorem compile_typed_copy_fields_extends =
  REWRITE_RULE [cs_appends_def] (CONJUNCT1 (CONJUNCT2 cs_appends_typed_copy_mutual));

Theorem compile_typed_copy_fields_next_var:
  !cenv dst src fts ats dst_off src_off cs ret cs'.
    compile_typed_copy_fields cenv dst src fts ats dst_off src_off cs = (ret,cs') ==>
    cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  `compiler_vars_mono (compile_typed_copy_fields cenv dst src fts ats dst_off src_off)` by
    simp[CONJUNCT1 (CONJUNCT2 compiler_vars_mono_typed_copy)] >>
  drule_all compiler_vars_mono_result >> simp[]
QED

Theorem compile_typed_copy_fields_cons_split:
  !cenv dst src fty fts aty ats dst_off src_off cs ret cs'.
    compile_typed_copy_fields cenv dst src (fty::fts) (aty::ats) dst_off src_off cs = (ret,cs') <=>
    ?dst_ptr after_dst src_ptr after_src after_child.
      compile_with_byte_offset dst dst_off cs = (dst_ptr,after_dst) /\
      compile_with_byte_offset src src_off after_dst = (src_ptr,after_src) /\
      compile_store_memory_typed cenv dst_ptr fty src_ptr aty after_src = ((),after_child) /\
      compile_typed_copy_fields cenv dst src fts ats
        (dst_off + type_memory_bytes cenv fty) (src_off + type_memory_bytes cenv aty) after_child = (ret,cs')
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_store_memory_typed_def])) >>
  simp_tac bool_ss [LET_THM, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_with_byte_offset dst dst_off cs` >>
  rename1 `compile_with_byte_offset dst dst_off cs = (dst_ptr,after_dst)` >>
  Cases_on `compile_with_byte_offset src src_off after_dst` >>
  rename1 `compile_with_byte_offset src src_off after_dst = (src_ptr,after_src)` >>
  Cases_on `compile_store_memory_typed cenv dst_ptr fty src_ptr aty after_src` >>
  rename1 `compile_store_memory_typed cenv dst_ptr fty src_ptr aty after_src = (unit_result,after_child)` >>
  Cases_on `unit_result` >> simp[]
QED

Theorem compile_typed_copy_fields_cons_contains:
  !cenv dst src fty fts aty ats dst_off src_off cs ret cs' func.
    compile_typed_copy_fields cenv dst src (fty::fts) (aty::ats) dst_off src_off cs = (ret,cs') /\
    fn_has_code cs cs' func ==>
    ?dst_ptr after_dst src_ptr after_src after_child.
      compile_with_byte_offset dst dst_off cs = (dst_ptr,after_dst) /\
      compile_with_byte_offset src src_off after_dst = (src_ptr,after_src) /\
      compile_store_memory_typed cenv dst_ptr fty src_ptr aty after_src = ((),after_child) /\
      compile_typed_copy_fields cenv dst src fts ats
        (dst_off + type_memory_bytes cenv fty) (src_off + type_memory_bytes cenv aty) after_child = (ret,cs') /\
      fn_has_code cs after_dst func /\ fn_has_code after_dst after_src func /\
      fn_has_code after_src after_child func /\ fn_has_code after_child cs' func
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ (_::_) (_::_) _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_typed_copy_fields_cons_split]) >>
  disch_then (qx_choose_then `dst_ptr` (qx_choose_then `after_dst` (qx_choose_then `src_ptr`
    (qx_choose_then `after_src` (qx_choose_then `after_child` strip_assume_tac))))) >>
  `cs_extends cs after_dst` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_extends)) >>
  `cs_extends after_dst after_src` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_extends)) >>
  `cs_extends after_src after_child` by (first_assum (ACCEPT_TAC o MATCH_MP compile_store_memory_typed_extends)) >>
  `cs_extends after_child cs'` by (first_assum (ACCEPT_TAC o MATCH_MP compile_typed_copy_fields_extends)) >>
  `cs_extends after_src cs'` by
    (irule cs_extends_trans >> qexists_tac `after_child` >> simp[]) >>
  `cs_extends after_dst cs'` by
    (irule cs_extends_trans >> qexists_tac `after_src` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `after_dst`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`after_dst`, `after_src`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`after_src`, `after_child`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`dst_ptr`, `after_dst`, `src_ptr`, `after_src`, `after_child`] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
