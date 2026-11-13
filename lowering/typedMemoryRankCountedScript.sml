Theory typedMemoryRankCounted
Ancestors
  placeMemoryTypedForward typedCopyCounted typedCopyAggregateCounted
  typedSarrayForwardCounted typedDynarrayForwardCounted typedCopyFieldsSemanticCounted
  typedNormalizeStaticRigidity typedNormalizeDynarray typedNormalizeStructMetadata
  typedCopyDomain compileEnv vyperTypeSystem vyperValue vyperTyping valueEncoding
  placeMemoryChildForward placeMemoryCopyEffect placeMemoryTypedBase context
  vyperTypeValues exprLoweringProps venomState fragGasMode fragGasPathMem

Theorem typed_memory_rank_forward_counted:
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
    !st dtv stv v dp sp a b u dw sw.
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
    u.vs_inst_idx = LENGTH a.cs_current_insts /\
    alloca_history func u /\ alloca_inv u /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (Cases_on `is_word_type dt`
  >- suspend "word" >>
  Cases_on `is_bytestring_type dt`
  >- suspend "bytes" >>
  Cases_on `dt`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()])
  >~ [`ArrayT et bd`]
  >- (Cases_on `bd` >- suspend "fixed" >> suspend "dynamic")
  >~ [`TupleT tys`]
  >- suspend "tuple"
  >~ [`StructT name`]
  >- suspend "struct" >>
  gvs[is_word_type_def, evaluate_type_def] >> suspend "empty")
QED

Resume typed_memory_rank_forward_counted[word]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `st = dt` by metis_tac[type_widens_to_word] >> gvs[] >>
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
  `w2n sw + 32 <= u.vs_alloca_next /\ w2n dw + 32 <= u.vs_alloca_next` by decide_tac >>
  `!x. sp = Var x \/ dp = Var x ==> not_fresh_at a x` by metis_tac[] >>
  drule_all normalize_word_window_path_length >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func u 0 (OK t)` by
    (simp[gas_marked_path_def] >> metis_tac[gas_path_mem_exec]) >>
  qexists `t` >> simp[typed_copy_effect_def] >>
  qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = _` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >> simp[]
QED

Resume typed_memory_rank_forward_counted[bytes]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `is_bytestring_type st` by
    (gvs[type_widens_to_def] >> metis_tac[arg_type_fits_bytestring_source]) >>
  `val_in_memory dtv v (w2n sw) u.vs_memory` by
    metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer] >>
  drule_all exprSimBufferStoreTheory.buffer_typed_bytestring_header >> strip_tac >>
  `val_store_size stv v = val_store_size dtv v` by
    metis_tac[valueCopyBytesTheory.bytestring_val_store_size_eq] >>
  `32 + 32 * word_size len <= type_memory_size stv /\
   32 + 32 * word_size len <= type_memory_size dtv` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= u.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= u.vs_alloca_next` by decide_tac >>
  `val_footprint dtv v <= 32 + 32 * word_size len` by
    metis_tac[exprSimPropsTheory.val_footprint_le_store_size] >>
  `!x. sp = Var x \/ dp = Var x ==> not_fresh_at a x` by metis_tac[] >>
  drule_all normalize_bytestring_window_path_length >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func u 0 (OK t)` by
    (simp[gas_marked_path_def] >> metis_tac[gas_path_mem_exec]) >>
  qexists `t` >> simp[typed_copy_effect_def] >>
  qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = _` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume typed_memory_rank_forward_counted[fixed]:
  markerLib.RESUME_TAC >>
  `?se. st = ArrayT se (Fixed n') /\ type_widens_to tenv se et` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     Cases_on `st` >> simp[type_widens_to_def, arg_type_fits_def] >>
     rpt strip_tac >> gvs[] >> Cases_on `b'` >>
     gvs[arg_type_fits_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()]) >>
  gvs[] >>
  qpat_assum `evaluate_type tenv (ArrayT et _) = _`
    (strip_assume_tac o MATCH_MP typed_memory_array_stride_bounds) >>
  `?sv. evaluate_type tenv se = SOME sv /\ stv = ArrayTV sv (Fixed n')` by
    gvs[evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `compile_copy_sarray_typed cenv dp et sp se n' a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  (Cases_on `~is_abi_dynamic cenv.ce_struct_fields et`
  >- suspend "fixed_fast" >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields et` mp_tac) >>
  simp[type_rank_def] >>
  disch_then (qspecl_then [`cenv`, `tenv`, `ctx`, `func`] mp_tac) >>
  disch_then (qspec_then `et` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (markerLib.mk_asm "child") >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_bytes cenv se = type_memory_size sv` by metis_tac[] >>
  simp[type_memory_size_def] >>
  irule typed_memory_sarray_slow_forward_counted >>
  qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl [`tenv`, `sw`, `sv`] >>
  asm "child" mp_tac >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  disch_then assume_tac >> simp[] >>
  gvs[value_has_type_def, type_memory_size_def] >>
  qpat_x_assum `!st' stv' v' dp' sp' a' b' u' dw' sw'. _` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[])
QED
Resume typed_memory_rank_forward_counted[dynamic]:
  markerLib.RESUME_TAC >>
  `?se sn. st = ArrayT se (Dynamic sn) /\ type_widens_to tenv se et` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     Cases_on `st` >> simp[type_widens_to_def, arg_type_fits_def] >>
     rpt strip_tac >> gvs[] >> Cases_on `b'` >>
     gvs[arg_type_fits_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()]) >>
  gvs[] >>
  qpat_assum `evaluate_type tenv (ArrayT et _) = _`
    (strip_assume_tac o MATCH_MP typed_memory_array_stride_bounds) >>
  `?sv. evaluate_type tenv se = SOME sv /\ stv = ArrayTV sv (Dynamic sn)` by
    gvs[evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `compile_copy_dynarray_typed cenv dp et n' sp se a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  (Cases_on `se = et` >- suspend "dynamic_fast" >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields et` mp_tac) >>
  simp[type_rank_def] >>
  disch_then (qspecl_then [`cenv`, `tenv`, `ctx`, `func`] mp_tac) >>
  disch_then (qspec_then `et` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (markerLib.mk_asm "child") >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `type_memory_bytes cenv et = type_memory_size tv /\
   type_memory_bytes cenv se = type_memory_size sv` by metis_tac[] >>
  irule typed_memory_dynarray_slow_forward_counted >>
  qpat_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl [`tenv`, `sw`, `sv`, `sn`] >>
  asm "child" mp_tac >>
  PURE_REWRITE_TAC [arithmeticTheory.ADD_ASSOC] >>
  disch_then assume_tac >> simp[] >>
  gvs[value_has_type_def, type_memory_size_def] >>
  qpat_x_assum `!st' stv' v' dp' sp' a' b' u' dw' sw'. _` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[])
QED
Resume typed_memory_rank_forward_counted[tuple]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` (markerLib.mk_asm "rank") >>
  `?stys. st = TupleT stys` by
    (Cases_on `st` >> gvs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  qpat_assum `evaluate_type tenv (TupleT tys) = SOME dtv`
    (strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >>
  rename1 `dtv = TupleTV dtvs` >>
  qpat_assum `evaluate_type tenv (TupleT stys) = SOME stv`
    (strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >>
  rename1 `stv = TupleTV stvs` >> gvs[] >>
  `LIST_REL (type_widens_to tenv) stys tys` by
    (drule typedMemoryCopyTheory.typed_copy_tuple_widening >>
     simp[] >> strip_tac >>
     irule typedMemoryCopyTheory.typed_copy_tuple_children_widen >>
     simp[] >> qexists `dtvs` >>
     gvs[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()]) >>
  `LIST_REL (\dt st. type_widens_to tenv st dt) tys stys` by
    (gvs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
       type_memory_bytes cenv ty = type_memory_size tv) tys dtvs /\
   LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
       type_memory_bytes cenv ty = type_memory_size tv) stys stvs` by
    (gvs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  `compile_typed_copy_fields cenv dp sp tys stys 0 0 a = ((),b)` by
    gvs[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_memory_fields_forward_counted >>
  disch_then (irule o SRULE []) >>
  simp[] >> qexistsl [`stvs`, `tenv`] >>
  simp[] >>
  qx_gen_tac `dt` >> strip_tac >>
      `type_rank cenv.ce_struct_fields dt < type_rank cenv.ce_struct_fields (TupleT tys)` by
        (irule member_rank_lt_tuple >> simp[]) >>
      asm_x "rank" (qspec_then `type_rank cenv.ce_struct_fields dt` mp_tac) >>
      simp[] >> disch_then (qspecl_then [`cenv`, `tenv`, `ctx`, `func`, `dt`] mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED
Resume typed_memory_rank_forward_counted[struct]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` (markerLib.mk_asm "rank") >>
  drule_all normalize_struct_metadata >> strip_tac >> gvs[] >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
      type_memory_bytes cenv ty = type_memory_size tv)
      (MAP (FST o SND) fields) tvs` by
    (drule vyperTypeABITheory.OPT_MMAP_LIST_REL >> strip_tac >>
     gvs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  `EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) fields` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
     qpat_x_assum `!fname fty sz. _` drule >> simp[]) >>
  `compile_struct_typed_copy cenv dp sp fields fields 0 0 a = ((),b)` by
    gvs[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def,
        get_struct_fields_def] >>
  `type_memory_size (StructTV (ZIP (MAP FST fields,tvs))) = type_memory_size_list tvs` by
    (simp[type_memory_size_def] >>
     irule valueEncodingTypingTheory.type_memory_size_fields_zip >> simp[]) >>
  gvs[value_has_type_def, val_wf_def, val_in_memory_def] >>
  drule_at (Pat `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _`)
    typed_memory_struct_forward_counted >>
  disch_then (irule o SRULE []) >> simp[] >> qexists `tenv` >> simp[] >>
  qx_gen_tac `dt` >> strip_tac >>
  `type_rank cenv.ce_struct_fields dt < type_rank cenv.ce_struct_fields (StructT name)` by
    (irule type_copy_child_rank >> gvs[type_copy_child_def, get_struct_fields_def]) >>
  asm_x "rank" (qspec_then `type_rank cenv.ce_struct_fields dt` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`cenv`, `tenv`, `ctx`, `func`, `dt`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED
Resume typed_memory_rank_forward_counted[empty]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `st = NoneT` by
    (Cases_on `st` >> gvs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  qexists `u` >> simp[val_in_memory_def, gas_path_mem_rules,
                         typed_copy_effect_identity]
QED
Resume typed_memory_rank_forward_counted[fixed_fast]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `se = et` by metis_tac[type_widens_to_static_identity] >> gvs[] >>
  rename1 `evaluate_type tenv et = SOME tv` >>
  `type_memory_bytes cenv et = type_memory_size tv` by metis_tac[] >>
  `val_footprint (ArrayTV tv (Fixed n')) v <= n' * type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le_store_size,
              exprSimPropsTheory.val_store_size_le, type_memory_size_def,
              arithmeticTheory.LESS_EQ_TRANS] >>
  `n' * type_memory_bytes cenv et < dimword (:256) /\
   w2n sw + n' * type_memory_bytes cenv et <= u.vs_alloca_next /\
   w2n dw + n' * type_memory_bytes cenv et <= u.vs_alloca_next` by
    (simp[type_memory_size_def] >>
     `type_memory_bytes cenv et = type_memory_size tv` by metis_tac[] >>
     gvs[type_memory_size_def] >> decide_tac) >>
  `val_footprint (ArrayTV tv (Fixed n')) v <= n' * type_memory_bytes cenv et` by simp[] >>
  drule_all (SRULE [] (Q.INST [`st` |-> `dt`] typed_sarray_fast_window_path_length)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func u 0 (OK t)` by
    (simp[gas_marked_path_def] >> metis_tac[gas_path_mem_exec]) >>
  qexists `t` >> simp[typed_copy_effect_def, type_memory_size_def] >>
  qpat_x_assum `(_ with <|vs_memory := _; vs_inst_idx := _|>) = _` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >> simp[]
QED
Resume typed_memory_rank_forward_counted[dynamic_fast]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >> gvs[] >>
  rename1 `evaluate_type tenv et = SOME tv` >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `type_memory_bytes cenv et = type_memory_size tv` by metis_tac[] >>
  `mload (w2n sw) u = n2w (LENGTH l)` by
    fs[val_in_memory_def, valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `val_in_memory (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l)) (w2n sw) u.vs_memory /\
   val_wf (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l)) /\
   val_footprint (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l)) <=
     32 + LENGTH l * type_memory_bytes cenv et` by
    (fs[val_in_memory_def, val_wf_def, loweringPostsTheory.val_footprint_def,
        type_memory_size_def]) >>
  `LENGTH l * type_memory_size tv <= sn * type_memory_size tv /\
   LENGTH l * type_memory_size tv <= n' * type_memory_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `LENGTH l * type_memory_bytes cenv et < dimword (:256) /\
   w2n sw + 32 < dimword (:256) /\
   w2n dw + 32 < dimword (:256) /\
   32 + LENGTH l * type_memory_bytes cenv et <= type_memory_size (ArrayTV tv (Dynamic sn)) /\
   w2n sw + type_memory_size (ArrayTV tv (Dynamic sn)) <= u.vs_alloca_next /\
   w2n dw + 32 + LENGTH l * type_memory_bytes cenv et <= u.vs_alloca_next /\
   (w2n sw + type_memory_size (ArrayTV tv (Dynamic sn)) <= w2n dw \/
    w2n dw + 32 + LENGTH l * type_memory_bytes cenv et <= w2n sw)` by
    (fs[type_memory_size_def] >>
     `type_memory_bytes cenv et = type_memory_size tv` by metis_tac[] >>
     fs[] >>
     assume_tac (Q.SPECL [`LENGTH (l:value list)`, `sn`, `type_memory_size tv`] arithmeticTheory.LESS_MONO_MULT) >>
     assume_tac (Q.SPECL [`LENGTH (l:value list)`, `n'`, `type_memory_size tv`] arithmeticTheory.LESS_MONO_MULT) >>
     decide_tac) >>
  `!x. sp = Var x \/ dp = Var x ==> not_fresh_at a x` by metis_tac[] >>
  drule_at (Pat `val_footprint _ _ <= _`) typed_dynarray_equal_window_path_length >>
  disch_then drule >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspecl_then [`type_memory_size (ArrayTV tv (Dynamic sn))`,
    `func`, `dw`, `ctx`] mp_tac) >>
  ((impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
   rename1 `gas_path_mem ctx func u 0 (OK t)` >>
   `gas_marked_path F ctx func u 0 (OK t)` by
     (simp[gas_marked_path_def] >> metis_tac[gas_path_mem_exec]) >>
   `val_in_memory (ArrayTV tv (Dynamic n')) (ArrayV (DynArrayV l)) (w2n dw) t.vs_memory` by
     fs[val_in_memory_def] >>
   qexists `t` >> simp[typed_copy_effect_def] >>
   qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = _` mp_tac >>
   simp[venom_state_component_equality] >> rpt strip_tac >> simp[] >>
   rpt strip_tac >> first_x_assum irule >> fs[type_memory_size_def] >>
   mp_tac (Q.SPECL [`LENGTH (l:value list)`, `n'`, `type_memory_size tv`] arithmeticTheory.LESS_MONO_MULT) >>
   decide_tac)
QED
Finalise typed_memory_rank_forward_counted
