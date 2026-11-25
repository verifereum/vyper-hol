(* Keep the prepared Extract32 descriptor across the actual offset run. *)
Theory bodyExtractSavedDescriptorMods
Ancestors
  bodyFullPostsMods exprSimExtract32Post exprSimAttributeFields placeMemoryTypedBase
  exprSimProps typedMemoryCopy robustCopyTransportPtr exprBopSimProps
  stateRelProj assignTuplePtrCopyLen loweringPosts compileEnv vyperAST vyperValue
  finite_map valueEncoding valueEncodingDefs valueEncodingProofs valueEncodingProps
  exprSimHypsDefs bodyPtrDefs ptrDiscipline exprSimMemDefs exprSimWordArgs
  exprLoweringProps exprSimHashBoundary venomState words pair list

(* A declared struct field has the same offset in its evaluated layout. *)
Theorem extract_field_offset[local]:
  !fields tvs fld fty sz.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(nm,ty,n). !tv. evaluate_type tenv ty = SOME tv ==>
                            n = type_memory_size tv) fields /\
    ALOOKUP fields fld = SOME (fty,sz) ==>
    ?ftv. evaluate_type tenv fty = SOME ftv /\
      mem_field_offset (ZIP (MAP FST fields,tvs)) fld =
        SOME (struct_field_offset fields fld,ftv)
Proof
  Induct >> simp[] >> PairCases >> rpt gen_tac >>
  simp[AllCaseEqs(), PULL_EXISTS, mem_field_offset_def, struct_field_offset_def] >>
  rpt strip_tac >> gvs[mem_field_offset_def] >>
  first_x_assum drule >> strip_tac >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem extract_take_layout[local]:
  !tys tvs i.
    OPT_MMAP (evaluate_type tenv) tys = SOME tvs /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
        type_memory_bytes cenv ty = type_memory_size tv) ==>
    SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
      type_memory_size_list (TAKE i tvs)
Proof
  Induct >> simp[type_memory_size_def] >> rpt gen_tac >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >>
  gvs[] >> Cases_on `i` >> simp[type_memory_size_def] >>
  first_x_assum drule >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem extract_step_layout[local]:
  !ty tv sb k et.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(nm,fty,n). !rt. evaluate_type tenv fty = SOME rt ==>
                              n = type_memory_size rt) fields) /\
    evaluate_type tenv ty = SOME tv /\
    type_step_offset cenv ty sb = SOME (k,et) ==>
    ?etv. mem_step_offset tv sb = SOME (k,etv) /\
          evaluate_type tenv et = SOME etv
Proof
  rpt gen_tac >> Cases_on `ty` >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  TRY (rename1 `ArrayT _ bd` >> Cases_on `bd`) >>
  simp[type_step_offset_def] >> rpt strip_tac >> gvs[]
  >~ [`StructT sid`]
  >- (drule_all_then strip_assume_tac typed_memory_struct_evaluation >>
      gvs[get_struct_fields_def, evaluate_types_OPT_MMAP] >>
      qpat_x_assum `MAP FST fields = _` (SUBST_ALL_TAC o SYM) >>
      `EVERY (\(nm,fty,n). !rt. evaluate_type tenv fty = SOME rt ==>
                                n = type_memory_size rt) fields` by metis_tac[] >>
      rename1 `ALOOKUP fields fld = SOME z` >> PairCases_on `z` >> gvs[] >>
      qpat_x_assum `MAP (FST o SND) fields = _` (SUBST_ALL_TAC o SYM) >>
      drule_all_then strip_assume_tac extract_field_offset >>
      simp[mem_step_offset_def])
  >~ [`TupleT tys`]
  >- (qpat_x_assum `evaluate_type _ (TupleT _) = _` mp_tac >>
      simp[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
      strip_tac >> gvs[] >>
      drule_all_then strip_assume_tac opt_mmap_el >>
      simp[mem_step_offset_def] >>
      irule (GSYM extract_take_layout) >> qexists_tac `tenv` >>
      simp[] >> metis_tac[typed_copy_memory_size]) >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >>
  strip_tac >> gvs[mem_step_offset_def] >>
  drule_all typed_copy_memory_size >> simp[]
QED

Theorem extract_path_layout[local]:
  !path cenv cx env es ty tv k pt.
    expr_sim_inv_mods mods cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_path_offset cenv ty path = SOME (k,pt) ==>
    ?ptv. mem_path_offset tv path = SOME (k,ptv) /\
          evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[type_path_offset_def, mem_path_offset_def] >>
  gvs[type_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     EVERY (\(nm,fty,n). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                              n = type_memory_size rt) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all_then strip_assume_tac extract_step_layout >>
  first_x_assum drule_all >> strip_tac >> simp[mem_path_offset_def]
QED

Theorem extract_base_path_apart[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  local_path_at cenv cx n k (BaseTV bt) /\
  dynarray_len_at cenv n j ==>
  k + type_memory_size (BaseTV bt) <= j \/ j + 32 <= k
Proof
  rw[local_path_at_def, dynarray_len_at_def] >> gvs[] >>
  drule_all_then strip_assume_tac extract_path_layout >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `dynarray_free (BaseTV bt)` by simp[dynarray_free_base] >>
  drule_all mem_path_offset_dynarray_apart >> simp[]
QED

Theorem extract_local_window_apart:
  expr_sim_inv_mods mods cenv cx env es /\
  local_val_at cenv cx n k (BaseTV bt) v /\
  val_wf (BaseTV bt) v /\ dynarray_len_at cenv n j ==>
  k + val_footprint (BaseTV bt) v <= j \/ j + 32 <= k
Proof
  rw[local_val_at_def]
  >- (drule_all extract_base_path_apart >> drule val_footprint_le >> decide_tac) >>
  drule_all extract_base_path_apart >> decide_tac
QED

Theorem extract_saved_window[local]:
  expr_sim_inv_mods mods cenv cx env mid /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic m))) sa sn mid
    (BytesV bs) (Var sv) u /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic m))) =
    SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand (Var sv) u = SOME (n2w p) /\ p < dimword(:256) /\
  wb_frame cenv mid ee sn u t /\ ghost_kept_at lo cenv mid sn G2 tn2 u G3 tn3 ==>
  val_wf (BaseTV (BytesT (Dynamic m))) (BytesV bs) /\
  mem_bytes_at p (32+LENGTH bs) t.vs_memory =
    mem_bytes_at p (32+LENGTH bs) u.vs_memory /\
  (!i. i < 32+LENGTH bs /\ p+i IN tn3.t_mem ==> p+i IN tn2.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, is_word_type_def,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  simp[val_footprint_def, val_store_size_def] >> strip_tac >> simp[]
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz u.vs_memory` by
        (fs[wb_frame_def] >>
         qpat_assum `!aid off sz. _` (qspecl_then [`aid`,`b`,`sz`] mp_tac) >>
         simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (sym_tac >> drule mem_bytes_at_agree_window >> strip_tac >>
          first_x_assum irule >> decide_tac) >>
      fs[ghost_kept_at_def] >> rpt strip_tac >>
      qpat_assum `!a off sz j. FLOOKUP u.vs_allocas a = _ /\ _ ==> _`
        (qspecl_then [`aid`,`b`,`sz`,`i+p`] mp_tac) >>
      `b <= i+p /\ i+p < b+sz` by decide_tac >>
      simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
      simp[wb_frame_def,locals_kept_def] >> strip_tac >>
      qpat_x_assum `!n b sz off len. _` irule >>
      qexistsl [`b`,`n`,`sz`] >> simp[] >> rpt strip_tac >>
      drule exprSimPropsTheory.dynarray_len_untupled_imp_at >> strip_tac >>
      drule_all extract_local_window_apart >>
      simp[val_footprint_def, val_store_size_def] >> decide_tac) >>
  fs[ghost_kept_at_def] >> rpt strip_tac >>
  qpat_assum `!n b sz j. local_region _ _ _ n b sz /\ _ ==> _`
    (qspecl_then [`n`,`b`,`sz`,`i+p`] mp_tac) >>
  simp[] >> `b <= i+p /\ i+p < b+sz` by decide_tac >> simp[]
QED

Theorem extract_saved_ptr[local]:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic m))) =
    SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand (Var sv) u = SOME (n2w p) /\
  eval_operand (Var sv) t = SOME (n2w p) /\ p < dimword(:256) /\
  FLOOKUP G3 sv = FLOOKUP G2 sv /\
  ptr_mem_ok cx (BaseT (BytesT (Dynamic m))) (BytesV bs) (Var sv) G2 tn2 u /\
  val_wf (BaseTV (BytesT (Dynamic m))) (BytesV bs) /\
  mem_bytes_at p (32+LENGTH bs) t.vs_memory =
    mem_bytes_at p (32+LENGTH bs) u.vs_memory /\
  (!i. i < 32+LENGTH bs /\ p+i IN tn3.t_mem ==> p+i IN tn2.t_mem) ==>
  ptr_mem_ok cx (BaseT (BytesT (Dynamic m))) (BytesV bs) (Var sv) G3 tn3 t /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p t.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  strip_tac >>
  `!mem. mem_agree_outside tn3.t_mem t.vs_memory mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p mem` by
    (rpt strip_tac >> irule robust_val_in_memory_decreasing_taint_transport >>
     simp[val_footprint_def, val_store_size_def] >>
     qexistsl [`u.vs_memory`,`t.vs_memory`,`32+LENGTH bs`,`p`,`tn2.t_mem`,`tn3.t_mem`] >>
     fs[arithmeticTheory.ADD_COMM]) >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p t.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >> simp[]
QED

Theorem extract32_saved_descriptor_mods:
  expr_post_mods H ctx func cenv cx src es sa sn s0 mid (BytesV bs) (Var sv) u /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  p+32+LENGTH bs <= u.vs_alloca_next /\
  ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u /\
  expr_sim_inv_mods mods cenv cx env mid /\
  not_fresh_at sn sv /\ not_fresh_at sn len /\ not_fresh_at sn data /\
  eval_operand (Var sv) u = SOME (n2w p) /\ p+32 < dimword(:256) /\
  eval_operand (Var len) u = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) u = SOME (n2w (p+32)) /\
  op_prov G2 (Var len) = NONE /\ op_taint tn2 (Var len) = {} /\
  (!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G2 tn2 data u span) /\
  expr_post_mods H ctx func cenv cx off mid sn sq u ee w offop t /\
  ghost_kept_at lo cenv mid sn G2 tn2 u G3 tn3 /\ u.vs_alloca_next <= t.vs_alloca_next ==>
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p t.vs_memory /\
  eval_operand (Var sv) t = SOME (n2w p) /\
  eval_operand (Var len) t = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) t = SOME (n2w (p+32)) /\
  LENGTH bs < dimword(:256) /\ p+32+LENGTH bs < dimword(:256) /\
  p+32+LENGTH bs <= t.vs_alloca_next /\
  op_prov G3 (Var len) = NONE /\ op_taint tn3 (Var len) = {} /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G3 tn3 t /\
  (!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G3 tn3 data t span)
Proof
  strip_tac >> fs[expr_post_mods_def] >>
  `p < dimword(:256)` by decide_tac >>
  drule_all_then (qx_choose_then `src_addr` strip_assume_tac) extract32_source_post_view >>
  `src_addr = p` by gvs[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD] >> gvs[] >>
  `p < dimword(:256) /\ p+32+LENGTH bs <= t.vs_alloca_next` by decide_tac >>
  `post_value_type cenv src = expr_type src` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic m))) sa sn mid (BytesV bs) (Var sv) u` by
    fs[expr_post_def] >>
  qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ _`
    (assume_tac o MATCH_MP expr_post_frame) >>
  drule_all_then strip_assume_tac extract_saved_window >>
  `!x q. not_fresh_at sn x /\ eval_operand (Var x) u = SOME q ==>
          eval_operand (Var x) t = SOME q` by fs[wb_frame_def,eval_operand_def] >>
  `eval_operand (Var sv) t = SOME (n2w p) /\
   eval_operand (Var len) t = SOME (n2w (LENGTH bs)) /\
   eval_operand (Var data) t = SOME (n2w (p+32))` by simp[] >>
  `FLOOKUP G3 sv = FLOOKUP G2 sv /\ FLOOKUP G3 data = FLOOKUP G2 data /\
   op_taint tn3 (Var data) = op_taint tn2 (Var data) /\
   op_prov G3 (Var len) = NONE /\ op_taint tn3 (Var len) = {}` by
    fs[ghost_kept_at_def,op_prov_def] >>
  `ptr_mem_ok cx (BaseT (BytesT (Dynamic m))) (BytesV bs) (Var sv) G2 tn2 u` by
    fs[ptr_val_ok_def,is_word_type_def] >>
  drule_all_then strip_assume_tac extract_saved_ptr >> simp[] >>
  rpt strip_tac >> irule ptr_covers_lookup_frame >>
  qexistsl [`G2`,`u`,`tn2`] >> fs[eval_operand_def]
QED
