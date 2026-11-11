Theory bodyIntCallCopySharpRank
Ancestors
  bodyIntCallCopySharpChild bodyIntCallCopySharpPrimitive
  bodyIntCallCopySharpFixed bodyIntCallCopySharpFast bodyIntCallCopySharpDynamic
  bodyIntCallCopySharpFields placeMemoryTypedForward placeMemoryTypedPrimitive
  typedCopyDomain compileEnv vyperTypeSystem vyperValue vyperTyping valueEncoding valueEncodingDefs
  placeMemoryCopyEffect placeMemoryTypedBase context vyperTypeValues
  placeMemoryDynarrayForward list

Theorem typed_memory_rank_forward_sharp:
  !n cenv tenv ctx func dt.
    type_rank cenv.ce_struct_fields dt = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
       type_memory_bytes cenv ty = type_memory_size tv) /\
    fn_inst_ids_distinct func ==>
    typed_memory_child_forward_sharp cenv tenv ctx func dt
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  simp[typed_memory_child_forward_sharp_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type dt` >- suspend "word" >>
  Cases_on `is_bytestring_type dt` >- suspend "bytes" >>
  Cases_on `dt`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()])
  >~ [`ArrayT et bd`]
  >- (Cases_on `bd` >- suspend "fixed" >> suspend "dynamic")
  >~ [`TupleT tys`] >- suspend "tuple"
  >~ [`StructT name`] >- suspend "struct" >>
  gvs[is_word_type_def, evaluate_type_def] >> suspend "empty"
QED

Resume typed_memory_rank_forward_sharp[word]:
  markerLib.RESUME_TAC >>
  `st = dt` by metis_tac[type_widens_to_word] >> gnvs[] >>
  `type_memory_size dtv = 32` by
    (qpat_x_assum `evaluate_type tenv dt = SOME dtv` mp_tac >>
     qpat_x_assum `is_word_type dt` mp_tac >>
     rpt (first_x_assum kall_tac) >>
     Cases_on `dt` >> simp[is_word_type_def]
     >~ [`FlagT _`] >- (rw[evaluate_type_def, AllCaseEqs()] >> simp[type_memory_size_def]) >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     rw[is_word_type_def, evaluate_type_def, type_memory_size_def] >>
     gvs[type_memory_size_def] >> rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_word_type_def, evaluate_type_def, type_memory_size_def, AllCaseEqs()]) >>
  `type_widens_to tenv dt dt` by simp[type_widens_to_def] >>
  drule_all typed_memory_word_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  gnvs[] >> qexists_tac `t` >> simp[typed_copy_effect_def] >>
  qpat_x_assum `_ = u` (mp_tac o Q.AP_TERM
    `\z. z with <|vs_prev_bb := u.vs_prev_bb; vs_current_bb := u.vs_current_bb|>`) >>
  simp[] >> metis_tac[]
QED

Resume typed_memory_rank_forward_sharp[bytes]:
  markerLib.RESUME_TAC >>
  `is_bytestring_type st` by
    (gvs[type_widens_to_def] >> metis_tac[arg_type_fits_bytestring_source]) >>
  `w2n dw + type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all typed_memory_bytestring_forward_sharp >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume typed_memory_rank_forward_sharp[fixed]:
  markerLib.RESUME_TAC >>
  `?se. st = ArrayT se (Fixed n') /\ type_widens_to tenv se et` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     Cases_on `st` >> simp[type_widens_to_def, arg_type_fits_def] >>
     rpt strip_tac >> gnvs[] >> Cases_on `b'` >>
     gvs[arg_type_fits_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()]) >>
  gnvs[] >>
  qpat_assum `evaluate_type tenv (ArrayT et _) = _`
    (strip_assume_tac o MATCH_MP typed_memory_array_stride_bounds) >>
  `?sv. evaluate_type tenv se = SOME sv /\ stv = ArrayTV sv (Fixed n')` by
    gvs[evaluate_type_def, AllCaseEqs()] >> gnvs[] >>
  `compile_copy_sarray_typed cenv dp et sp se n' a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields et` >- suspend "fixed_fast" >>
  `typed_memory_child_forward_sharp cenv tenv ctx func et` by
    (first_x_assum (qspec_then `type_rank cenv.ce_struct_fields et` mp_tac) >>
     simp[type_rank_def] >> disch_then irule >> simp[] >> metis_tac[]) >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_bytes cenv se = type_memory_size sv` by metis_tac[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `value_has_type (ArrayTV tv (Fixed n')) (ArrayV (SArrayV l)) /\
   value_has_type (ArrayTV sv (Fixed n')) (ArrayV (SArrayV l))` by
    simp[value_has_type_def] >>
  `w2n sw + n' * type_memory_size sv < dimword (:256) /\
   w2n dw + n' * type_memory_size tv < dimword (:256) /\
   (w2n sw + n' * type_memory_size sv <= w2n dw \/
    w2n dw + n' * type_memory_size tv <= w2n sw)` by
    (gvs[type_memory_size_def] >> decide_tac) >>
  `~(type_memory_bytes cenv et = type_memory_bytes cenv se /\
     ~is_abi_dynamic cenv.ce_struct_fields et)` by simp[] >>
  rewrite_tac[type_memory_size_def] >>
  irule typed_memory_sarray_slow_forward_sharp >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`sv`, `sw`, `tenv`] >> simp[value_has_type_def] >> metis_tac[]
QED

Resume typed_memory_rank_forward_sharp[dynamic]:
  markerLib.RESUME_TAC >>
  `?se cap. st = ArrayT se (Dynamic cap) /\ type_widens_to tenv se et` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     Cases_on `st` >> simp[type_widens_to_def, arg_type_fits_def] >>
     rpt strip_tac >> gnvs[] >> Cases_on `b'` >>
     gvs[arg_type_fits_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()]) >>
  gnvs[] >>
  qpat_assum `evaluate_type tenv (ArrayT et _) = _`
    (strip_assume_tac o MATCH_MP typed_memory_array_stride_bounds) >>
  `?sv. evaluate_type tenv se = SOME sv /\ stv = ArrayTV sv (Dynamic cap)` by
    gvs[evaluate_type_def, AllCaseEqs()] >> gnvs[] >>
  `compile_copy_dynarray_typed cenv dp et n' sp se a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  Cases_on `et = se` >- suspend "dynamic_fast" >>
  `typed_memory_child_forward_sharp cenv tenv ctx func et` by
    (first_x_assum (qspec_then `type_rank cenv.ce_struct_fields et` mp_tac) >>
     simp[type_rank_def] >> disch_then irule >> simp[] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  irule typed_memory_dynarray_slow_forward_sharp >> simp[value_has_type_def] >>
  goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`cap`, `sv`, `sw`, `tenv`] >> simp[value_has_type_def] >> metis_tac[]
QED

Resume typed_memory_rank_forward_sharp[tuple]:
  markerLib.RESUME_TAC >>
  `?sts. st = TupleT sts` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     Cases_on `st` >> simp[type_widens_to_def, arg_type_fits_def]) >> gnvs[] >>
  `!dt. MEM dt tys ==> typed_memory_child_forward_sharp cenv tenv ctx func dt` by
    (rpt strip_tac >> first_x_assum (qspec_then `type_rank cenv.ce_struct_fields dt` mp_tac) >>
     `type_rank cenv.ce_struct_fields dt < type_rank cenv.ce_struct_fields (TupleT tys)` by
       (irule member_rank_lt_tuple >> simp[]) >> simp[] >> disch_then irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_assum `evaluate_type tenv (TupleT tys) = SOME dtv`
    (strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >>
  rename1 `dtv = TupleTV dtvs` >>
  qpat_assum `evaluate_type tenv (TupleT sts) = SOME stv`
    (strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >>
  rename1 `stv = TupleTV stvs` >> gnvs[] >>
  `LIST_REL (\dt st. type_widens_to tenv st dt) tys sts` by
    (`!ds ss vs. LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ds vs ==>
        arg_types_fit ss ds ==> LIST_REL (\dt st. type_widens_to tenv st dt) ds ss` by
       (rpt (first_x_assum kall_tac) >> Induct >> Cases_on `ss` >> Cases_on `vs` >>
        simp[arg_type_fits_def] >> rpt strip_tac >> gnvs[] >>
        first_x_assum drule >> disch_then drule >> strip_tac >>
        simp[type_widens_to_def, well_formed_type_def]) >>
     qpat_x_assum `type_widens_to tenv (TupleT _) _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def] >> strip_tac
     >- simp[listTheory.LIST_REL_refl] >>
     qpat_x_assum `!ds ss vs. _` (qspecl_then [`tys`, `sts`, `dtvs`] mp_tac) >>
     simp[type_widens_to_def]) >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
       type_memory_bytes cenv ty = type_memory_size tv) tys dtvs /\
   LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
       type_memory_bytes cenv ty = type_memory_size tv) sts stvs` by
    (gvs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  `compile_typed_copy_fields cenv dp sp tys sts 0 0 a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_memory_fields_forward_sharp >>
  disch_then (irule o SRULE []) >> simp[] >>
  qexistsl_tac [`stvs`, `tenv`] >> simp[] >> decide_tac
QED

Resume typed_memory_rank_forward_sharp[struct]:
  markerLib.RESUME_TAC >>
  drule typed_memory_struct_widening >> strip_tac >> gnvs[] >>
  drule_all typed_memory_struct_evaluation >> strip_tac >> gnvs[] >>
  `!dt. MEM dt (MAP (FST o SND) fields) ==>
     typed_memory_child_forward_sharp cenv tenv ctx func dt` by
    (rpt strip_tac >>
     `type_rank cenv.ce_struct_fields dt < type_rank cenv.ce_struct_fields (StructT name)` by
       (irule type_copy_child_rank >> gvs[type_copy_child_def, get_struct_fields_def]) >>
     first_x_assum (qspec_then `type_rank cenv.ce_struct_fields dt` mp_tac) >>
     simp[] >> disch_then irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
      type_memory_bytes cenv ty = type_memory_size tv)
      (MAP (FST o SND) fields) tvs` by
    (`LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs` by
       (irule vyperTypeABITheory.OPT_MMAP_LIST_REL >> gvs[evaluate_types_OPT_MMAP]) >>
     gvs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) fields` by
    (qpat_x_assum `!name fields. FLOOKUP _ name = SOME fields ==> _`
       (qspec_then `nsid_to_string name` mp_tac) >> simp[] >> strip_tac >>
     simp[] >> gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     PairCases_on `e` >> gnvs[] >>
     `?tv. evaluate_type tenv e1 = SOME tv` by
       (qpat_x_assum `LIST_REL _ (MAP SND args) tvs` mp_tac >>
        simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
        `MEM e1 (MAP (FST o SND) fields)` by
          (simp[listTheory.MEM_MAP] >> qexists_tac `(e0,e1,e2)` >> simp[]) >>
        gvs[listTheory.MEM_EL] >> metis_tac[listTheory.EL_MAP]) >>
     qpat_x_assum `!e. MEM e fields ==> _`
       (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >>
     disch_then (qspec_then `tv` mp_tac) >> simp[]) >>
  `compile_struct_typed_copy cenv dp sp fields fields 0 0 a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def,
          get_struct_fields_def]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def, val_in_memory_def] >>
  `type_memory_size (StructTV (ZIP (MAP FST args,tvs))) = type_memory_size_list tvs` by
    (simp[type_memory_size_def] >>
     irule valueEncodingTypingTheory.type_memory_size_fields_zip >> metis_tac[listTheory.LENGTH_MAP]) >>
  gnvs[] >>
  qpat_assum `MAP FST fields = MAP FST args` (fn th => rewrite_tac[GSYM th]) >>
  drule_at (Pat `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _`)
    typed_memory_struct_forward_sharp >> disch_then (irule o SRULE []) >> simp[] >>
  qexists_tac `tenv` >> simp[]
QED

Resume typed_memory_rank_forward_sharp[empty]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  gvs[type_widens_to_def, arg_type_fits_def, is_bytestring_type_def] >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  gvs[evaluate_type_def, Once compile_store_memory_typed_def,
      is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
      type_memory_size_def, val_in_memory_def] >>
  `0 < dimword (:256)` by simp[] >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO]
    (GEN_ALL placeMemoryTypedPrimitiveTheory.compile_copy_memory_forward)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >> metis_tac[]
QED

Resume typed_memory_rank_forward_sharp[fixed_fast]:
  markerLib.RESUME_TAC >>
  `type_memory_bytes cenv (ArrayT et (Fixed n')) = type_memory_size (ArrayTV tv (Fixed n'))` by metis_tac[] >>
  `w2n dw + type_memory_size (ArrayTV tv (Fixed n')) < dimword (:256)` by decide_tac >>
  drule_all typed_memory_sarray_fast_forward_sharp >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >> rpt strip_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >> decide_tac
QED

Resume typed_memory_rank_forward_sharp[dynamic_fast]:
  markerLib.RESUME_TAC >>
  gnvs[] >> qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `DynArrayV vs` >>
  `LENGTH vs <= n'` by gvs[value_has_type_def] >>
  `LENGTH vs * type_memory_size sv < dimword (:256) /\
   w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256)` by
    (gvs[type_memory_size_def] >>
     `LENGTH vs * type_memory_size sv <= n' * type_memory_size sv` by
       simp[arithmeticTheory.LE_MULT_RCANCEL] >> decide_tac) >>
  `type_memory_bytes cenv et = type_memory_size sv` by metis_tac[] >>
  `value_has_type (ArrayTV sv (Dynamic cap)) (ArrayV (DynArrayV vs))` by simp[value_has_type_def] >>
  Q.SUBGOAL_THEN
    `w2n sw + type_memory_size (ArrayTV sv (Dynamic cap)) <= w2n dw \/
     w2n dw + type_memory_size (ArrayTV sv (Dynamic n')) <= w2n sw` assume_tac
  >- decide_tac >>
  drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)
    typed_memory_dynarray_fast_forward >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (qspecl_then [`func`, `dw`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >> rpt strip_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >> decide_tac
QED

Finalise typed_memory_rank_forward_sharp

Theorem compile_store_memory_typed_forward_sharp:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  fn_inst_ids_distinct func /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
  fn_has_code a b func /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule typed_memory_child_forward_sharp_apply >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw`, `tenv`] >> simp[] >>
  irule typed_memory_rank_forward_sharp >> simp[] >> metis_tac[]
QED
