Theory placeTypedCopyForwardMem
Ancestors
  placeTypedCopyArrayMem placeTypedFieldsMem placeTypedCopyMem
  placeMemoryTypedForward typedCopyDomain vyperTypeSystem vyperTypeValues
  compileEnv vyperValue vyperTyping valueEncoding context exprLoweringProps
  placeMemoryCopyEffect placeMemoryTypedBase placeMemoryChildForward
  abiValueEncoding placeTypedCopyPrimitiveMem exprSimProps venomState venomExecSemantics
  valueEncodingProps immutableMemoryFrame finite_map ASCIInumbers
  fragGasPathMem fragGasMode

Theorem typed_memory_rank_forward_mem:
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
      w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
      w2n sw + type_memory_size stv <= u.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
      compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
      (!x. dp = Var x ==> not_fresh_at a x) /\
      (!x. sp = Var x ==> not_fresh_at a x) /\
      eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
      fn_has_code a b func /\ ~u.vs_halted /\
      u.vs_current_bb = a.cs_current_bb /\
      u.vs_inst_idx = LENGTH a.cs_current_insts ==>
      ?t. gas_path_mem ctx func u 0 (OK t) /\
          val_in_memory dtv v (w2n dw) t.vs_memory /\
          typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
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

Resume typed_memory_rank_forward_mem[word]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `st = dt` by metis_tac[type_widens_to_word] >> gnvs[] >>
  `type_memory_size dtv = 32` by metis_tac[abi_word_type_size] >>
  `w2n sw + 32 <= u.vs_alloca_next /\ w2n dw + 32 <= u.vs_alloca_next` by decide_tac >>
  drule_all typed_memory_word_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func u 0 (OK r)` >>
  qexists_tac `r` >> simp[] >>
  `mem_word_at (w2n sw) u.vs_memory = typed_val_to_w256 dtv v` by
    metis_tac[val_in_memory_word] >>
  conj_tac
  >- (drule_all val_in_memory_word >> disch_then (fn th => rewrite_tac[th]) >>
      simp[Abbr `r`, mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]) >>
  simp[typed_copy_effect_def] >>
  rpt conj_tac
  >~ [`gas_marked_path F _ _ _ _ _`]
  >- metis_tac[gas_path_mem_exec, gas_marked_path_def]
  >- simp[Abbr `r`, mstore_def, write_memory_with_expansion_def,
          update_var_def, venom_state_component_equality]
  >- (rpt strip_tac >>
      `x <> STRING #"%" (toString a.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      simp[Abbr `r`, mstore_def, write_memory_with_expansion_def,
           update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >- simp[Abbr `r`, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (rpt strip_tac >> simp[Abbr `r`] >>
      simp[mstore_mem_bytes_at_disjoint, update_var_def])
  >~ [`LENGTH u.vs_memory <= _`]
  >- simp[Abbr `r`, immutable_mstore_capacity, update_var_def, arithmeticTheory.MAX_DEF] >>
  simp[Abbr `r`, mstore_def, write_memory_with_expansion_def, update_var_def,
       venom_state_component_equality]
QED
Resume typed_memory_rank_forward_mem[bytes]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `is_bytestring_type st` by
    (gvs[type_widens_to_def] >> metis_tac[arg_type_fits_bytestring_source]) >>
  `val_store_size stv v <= type_memory_size stv` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  irule placeTypedCopyPrimitiveMemTheory.typed_memory_bytestring_path_mem >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> decide_tac
QED
Resume typed_memory_rank_forward_mem[fixed]:
  markerLib.RESUME_TAC >> (
  `?se. st = ArrayT se (Fixed n') /\ type_widens_to tenv se et` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     rpt (first_x_assum kall_tac) >> Cases_on `st` >> simp[type_widens_to_def, arg_type_fits_def] >>
     rpt strip_tac >> gvs[] >> Cases_on `b` >>
     gvs[arg_type_fits_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
     Cases_on `evaluate_type tenv et` >> gvs[]) >>
  gnvs[] >>
  qpat_assum `evaluate_type tenv (ArrayT et _) = _`
    (strip_assume_tac o MATCH_MP typed_memory_array_stride_bounds) >>
  `?sv. evaluate_type tenv se = SOME sv /\ stv = ArrayTV sv (Fixed n')` by
    gvs[evaluate_type_def, AllCaseEqs()] >> gnvs[] >>
  `compile_copy_sarray_typed cenv dp et sp se n' a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields et`
  >- (irule typed_memory_sarray_fast_forward_mem >>
      qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  Cases_on `v` >> gnvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gnvs[value_has_type_def] >>
  rewrite_tac[type_memory_size_def] >>
  irule typed_memory_sarray_slow_forward_mem >>
  qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[value_has_type_def, type_memory_size_def] >> suspend "fixed_finish")
QED
Resume typed_memory_rank_forward_mem[fixed_finish]:
  markerLib.RESUME_TAC >> (
  gnvs[type_memory_size_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields et` mp_tac) >>
  simp[type_rank_def] >> disch_then irule >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[])

QED
Resume typed_memory_rank_forward_mem[dynamic]:
  markerLib.RESUME_TAC >> (
  `?se cap. st = ArrayT se (Dynamic cap) /\ type_widens_to tenv se et` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     rpt (first_x_assum kall_tac) >> Cases_on `st` >>
     simp[type_widens_to_def, arg_type_fits_def] >>
     rpt strip_tac >> gvs[] >> Cases_on `b` >>
     gvs[arg_type_fits_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
     Cases_on `evaluate_type tenv et` >> gvs[]) >>
  gnvs[] >>
  qpat_assum `evaluate_type tenv (ArrayT et _) = _`
    (strip_assume_tac o MATCH_MP typed_memory_array_stride_bounds) >>
  `?sv. evaluate_type tenv se = SOME sv /\ stv = ArrayTV sv (Dynamic cap)` by
    gvs[evaluate_type_def, AllCaseEqs()] >> gnvs[] >>
  `compile_copy_dynarray_typed cenv dp et n' sp se a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  Cases_on `v` >> gnvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gnvs[value_has_type_def] >>
  rename1 `DynArrayV vs` >>
  Cases_on `et = se` >- suspend "dynamic_fast" >>
  irule typed_memory_dynarray_slow_forward_mem >>
  qpat_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[value_has_type_def, type_memory_size_def] >> suspend "dynamic_finish")
QED
Resume typed_memory_rank_forward_mem[dynamic_fast]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `!m. m < _ ==> _` kall_tac >> gnvs[] >>
  `LENGTH vs <= cap /\ LENGTH vs <= n'` by fs[] >>
  `LENGTH vs * type_memory_size sv <= cap * type_memory_size sv` by simp[] >>
  irule typed_memory_dynarray_fast_forward_mem >>
  qpat_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[value_has_type_def, type_memory_size_def] >>
  gvs[type_memory_size_def] >>
  `LENGTH vs * type_memory_size sv <= cap * type_memory_size sv` by simp[] >>
  decide_tac)
QED
Resume typed_memory_rank_forward_mem[dynamic_finish]:
  markerLib.RESUME_TAC >> (
  `LENGTH vs * type_memory_size sv <= cap * type_memory_size sv` by simp[] >>
  gnvs[type_memory_size_def] >>
  reverse conj_tac
  >- (`LENGTH vs <= cap` by fs[] >>
      `LENGTH vs * type_memory_size sv <= cap * type_memory_size sv` by simp[] >>
      decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields et` mp_tac) >>
  simp[type_rank_def] >> disch_then irule >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[])

QED
Resume typed_memory_rank_forward_mem[tuple]:
  markerLib.RESUME_TAC >> (
  `?sts. st = TupleT sts` by
    (qpat_x_assum `type_widens_to tenv st _` mp_tac >>
     Cases_on `st` >> simp[type_widens_to_def, arg_type_fits_def]) >> gnvs[] >>
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
        simp[arg_type_fits_def] >> rpt strip_tac >> gvs[] >>
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
  Cases_on `v` >> gnvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gnvs[value_has_type_def] >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_memory_fields_forward_mem >>
  disch_then (irule o SRULE []) >> simp[] >>
  qexistsl_tac [`stvs`, `tenv`] >> simp[] >> suspend "tuple_finish")
QED
Resume typed_memory_rank_forward_mem[tuple_finish]:
  markerLib.RESUME_TAC >> (
  rpt gen_tac >> strip_tac >>
  `type_rank cenv.ce_struct_fields dt < type_rank cenv.ce_struct_fields (TupleT tys)` by
    (irule member_rank_lt_tuple >> simp[]) >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields dt` mp_tac) >>
  simp[] >> disch_then irule >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[])
QED
Resume typed_memory_rank_forward_mem[struct]:
  markerLib.RESUME_TAC >> (
  drule typed_memory_struct_widening >> strip_tac >> gnvs[] >>
  drule_all typed_memory_struct_evaluation >> strip_tac >> gnvs[] >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
      type_memory_bytes cenv ty = type_memory_size tv)
      (MAP (FST o SND) fields) tvs` by
    (`LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs` by
       (irule vyperTypeABITheory.OPT_MMAP_LIST_REL >>
        gvs[evaluate_types_OPT_MMAP]) >>
     gvs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) fields` by
    (qpat_x_assum `!name fields. FLOOKUP _ name = SOME fields ==> _`
       (qspec_then `nsid_to_string name` mp_tac) >> simp[] >> strip_tac >>
     simp[] >> gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     PairCases_on `e` >> gvs[] >>
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
  Cases_on `v` >> gnvs[value_has_type_def, val_wf_def, val_in_memory_def] >>
  `type_memory_size (StructTV (ZIP (MAP FST args,tvs))) = type_memory_size_list tvs` by
    (simp[type_memory_size_def] >>
     irule valueEncodingTypingTheory.type_memory_size_fields_zip >>
     metis_tac[listTheory.LENGTH_MAP]) >>
  gnvs[] >>
  qpat_assum `MAP FST fields = MAP FST args` (fn th => rewrite_tac[GSYM th]) >>
  drule_at (Pat `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _`)
    typed_memory_struct_forward_mem >> disch_then (irule o SRULE []) >> simp[] >>
  qexists_tac `tenv` >> simp[] >> suspend "struct_finish")
QED
Resume typed_memory_rank_forward_mem[struct_finish]:
  markerLib.RESUME_TAC >> (
  rpt gen_tac >> strip_tac >>
  `type_rank cenv.ce_struct_fields dt < type_rank cenv.ce_struct_fields (StructT name)` by
    (irule type_copy_child_rank >> gvs[type_copy_child_def, get_struct_fields_def]) >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields dt` mp_tac) >>
  simp[] >> disch_then irule >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[])
QED
Resume typed_memory_rank_forward_mem[empty]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  gvs[type_widens_to_def, arg_type_fits_def, is_bytestring_type_def] >>
  gvs[evaluate_type_def, Once compile_store_memory_typed_def,
      is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
      type_memory_size_def, val_in_memory_def] >>
  `w2n sw <= u.vs_alloca_next /\ w2n dw <= u.vs_alloca_next` by decide_tac >>
  drule_all (SRULE [] (Q.INST [`n` |-> `0`] compile_copy_memory_effect_mem)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[])
QED
Finalise typed_memory_rank_forward_mem
