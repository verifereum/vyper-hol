(* No-access execution for recursively empty typed layouts. *)
Theory typedCopyEmptyRankMemory
Ancestors
  typedCopyEmptyArrayMemory typedCopyEmptyFieldsMemory typedCopyRankMemory typedCopyDomain
  exprSimAggregateChildren typedMemoryCopy compileEnv context exprLowering
  emitHelper fragExecMem valueEncoding vyperTypeSystem vyperTypeArgFits vyperValue
  vyperTyping words list finite_map arithmetic

Theorem typed_copy_empty_rank_mem[local]:
  !n cenv tenv ctx dty sty dtv stv v.
    type_rank cenv.ce_struct_fields dty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
      FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\ type_memory_size stv = 0 ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. t.vs_memory = s.vs_memory /\
          typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `type_memory_size dtv = 0` by metis_tac[widening_zero_memory_size] >>
  Cases_on `is_word_type dty` >- suspend "word" >>
  Cases_on `is_bytestring_type dty` >- suspend "bytes" >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db` >- suspend "fixed" >> suspend "dynamic")
  >~ [`TupleT dtys`] >- suspend "tuple"
  >~ [`StructT name`] >- suspend "struct" >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  rpt strip_tac >> qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  irule frag_exec_mem_refl >> simp[]
QED

Resume typed_copy_empty_rank_mem[word]:
  `type_memory_size dtv = 32` by metis_tac[abiValueEncodingTheory.abi_word_type_size] >> gvs[]
QED

Resume typed_copy_empty_rank_mem[bytes]:
  `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))` by
    metis_tac[valueCopyBytesTheory.bytestring_type_value] >>
  gvs[type_memory_size_def]
QED

Resume typed_copy_empty_rank_mem[fixed]:
  rename1 `ArrayT de (Fixed cap)` >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `sb = Fixed cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  gvs[type_memory_size_def] >>
  `default_value tv = default_value tv'` by metis_tac[typed_copy_default_widening] >>
  `type_memory_bytes cenv de = 0 /\ type_memory_bytes cenv se = 0` by
    metis_tac[typed_copy_memory_size] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  suspend "fixed_child"
QED

Resume typed_copy_empty_rank_mem[dynamic]:
  gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Resume typed_copy_empty_rank_mem[tuple]:
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (irule typed_copy_tuple_children_widen >>
     (conj_tac >- metis_tac[]) >>
     drule typed_copy_tuple_widening >> simp[] >> strip_tac >> simp[]) >>
  `LENGTH stys = LENGTH dtys /\ LENGTH tvs' = LENGTH dtys /\
   LENGTH tvs = LENGTH dtys /\ LENGTH l = LENGTH dtys` by
    metis_tac[vyperTypeABITheory.OPT_MMAP_LENGTH, LIST_REL_LENGTH, values_have_types_length] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule typed_copy_fields_empty_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> suspend "tuple_children"
QED

Resume typed_copy_empty_rank_mem[struct]:
  drule typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    metis_tac[typed_copy_struct_values, LENGTH_MAP] >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by
    (irule typed_copy_tuple_children_widen >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    ((conj_tac >- metis_tac[]) >>
     irule typed_copy_struct_field_bytes >> qexistsl_tac [`tenv`, `tvs`] >>
     simp[] >>
     (conj_tac >- (rpt strip_tac >> irule typed_copy_memory_size >>
       qexists_tac `tenv` >> simp[] >> metis_tac[])) >> metis_tac[]) >>
  suspend "struct_execution"
QED

Resume typed_copy_empty_rank_mem[fixed_child]:
  `!dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst de src se sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. t.vs_memory = s.vs_memory /\
        typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)` by
    (qpat_x_assum `!m. m < _ ==> _`
       (qspec_then `type_rank cenv.ce_struct_fields de` mp_tac) >>
     simp[Once type_rank_def] >>
     disch_then ho_match_mp_tac >> simp[] >>
     qexistsl_tac [`tenv`, `tv'`, `tv`, `default_value tv`] >>
     simp[valueEncodingProofsTheory.val_wf_default_value_proof] >>
     metis_tac[vyperTypingTheory.default_value_well_typed,
               cj 1 vyperTypingTheory.evaluate_type_well_formed]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule typed_copy_sarray_empty_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  metis_tac[]
QED

Resume typed_copy_empty_rank_mem[tuple_children]:
  `tuple_val_wf l tvs /\ tuple_val_wf l tvs'` by gvs[val_wf_def] >>
  gen_tac >> strip_tac >>
  drule_all typedCopySemanticIndexTheory.typed_copy_semantic_index >> strip_tac >>
  `type_memory_size (EL i tvs) = 0 /\ type_memory_size (EL i tvs') = 0` by
    (gvs[type_memory_size_def, valueEncodingProofsTheory.type_memory_size_list_sum,
         listTheory.SUM_eq_0, MEM_MAP] >> metis_tac[EL_MEM]) >>
  conj_tac >- metis_tac[typed_copy_memory_size] >>
  conj_tac >- metis_tac[typed_copy_memory_size] >>
  `type_rank cenv.ce_struct_fields (EL i dtys) <
   type_rank cenv.ce_struct_fields (TupleT dtys)` by
    metis_tac[member_rank_lt_tuple, EL_MEM] >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields (EL i dtys)` mp_tac) >>
  simp[] >> disch_then ho_match_mp_tac >> simp[] >>
  qexistsl_tac [`tenv`, `EL i tvs'`, `EL i tvs`, `EL i l`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Resume typed_copy_empty_rank_mem[struct_execution]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, get_struct_fields_def] >> strip_tac >>
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  `compile_struct_typed_copy cenv dst src fields fields 0 0 =
   compile_typed_copy_fields cenv dst src
     (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0` by
    (drule_all typed_copy_struct_suffix_producer >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >> gvs[] >>
  irule typed_copy_fields_empty_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> suspend "struct_children"
QED

Resume typed_copy_empty_rank_mem[struct_children]:
  gen_tac >> strip_tac >>
  `i < LENGTH (MAP SND args)` by simp[] >>
  drule_all typedCopySemanticIndexTheory.typed_copy_semantic_index >> strip_tac >>
  `type_memory_size (EL i tvs) = 0` by
    (gvs[type_memory_size_def, valueEncodingTypingTheory.type_memory_size_fields_zip,
         valueEncodingProofsTheory.type_memory_size_list_sum, SUM_eq_0, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  conj_tac >- metis_tac[typed_copy_memory_size] >>
  conj_tac >- metis_tac[typed_copy_memory_size] >>
  `MEM (EL i (MAP SND args)) (MAP (FST o SND) fields)` by
    metis_tac[EL_MEM] >>
  `type_rank cenv.ce_struct_fields (EL i (MAP SND args)) <
   type_rank cenv.ce_struct_fields (StructT name)` by
    (qpat_x_assum `MEM _ (MAP (FST o SND) fields)` mp_tac >>
     simp[MEM_MAP] >> strip_tac >> PairCases_on `y` >> gvs[] >>
     `MEM (y0,EL i (MAP SND args),y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[get_struct_fields_def] >>
     drule_all member_rank_lt_struct >> simp[type_rank_def, nsid_to_string_def]) >>
  qpat_x_assum `!m. m < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields (EL i (MAP SND args))` mp_tac) >>
  simp[] >> disch_then ho_match_mp_tac >> simp[] >>
  qexistsl_tac [`tenv`, `EL i tvs`, `EL i tvs`, `EL i vs`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise typed_copy_empty_rank_mem

Theorem compile_store_memory_typed_empty_frag_mem:
  !cenv tenv ctx dty sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\ type_memory_size stv = 0 ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. t.vs_memory = s.vs_memory /\
          typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac typed_copy_empty_rank_mem >> simp[] >>
  metis_tac[]
QED
