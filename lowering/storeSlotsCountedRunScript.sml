(* Counted sparse stores by type rank. *)
Theory storeSlotsCountedRun
Ancestors
  storeSlotsCountedArrays storeSlotsCountedMembers storeSlotsCountedBase
  placeStoreSlots context compileEnv fragExec fragGasMode venomState venomInst
  valueEncoding valueEncodingProps vyperTyping vyperStorage vyperTypeSystem
  typedMemoryCopy typedCopyDomain abiTypeBoundProps exprSimAggregateEncoding
  words arithmetic list rich_list stmtLowering

Theorem store_slots_rank_run_mem:
  !n cenv tenv ctx ty tv v.
    type_rank cenv.ce_struct_fields ty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    !src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot ty tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory tv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size tv < dimword (:256) /\
      w2n sw + type_memory_size tv <= s.vs_alloca_next /\
      w2n dw + type_slot_size tv <= dimword (:256) /\
      encode_value tv v = SOME writes /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
      ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
        store_copy_normalize s t =
          FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
            (mload (w2n sw + 32*j) s) q) s ks /\
        (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
        t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
        t.vs_alloca_next = s.vs_alloca_next /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields ty`
  >- suspend "dynamic" >>
  rpt gen_tac >> strip_tac >>
  irule storeSlotsCountedBaseTheory.store_slots_static_entry_mem >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `src`, `tenv`, `ty`] >> simp[] >> metis_tac[]
QED

Resume store_slots_rank_run_mem[dynamic]:
  Cases_on `is_bytestring_type ty`
  >- (rpt gen_tac >> strip_tac >> irule store_slots_bytes_entry_mem >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`cenv`, `src`, `tenv`, `ty`] >> simp[] >> metis_tac[]) >>
  Cases_on `ty`
  >~ [`ArrayT elem bd`] >- suspend "arrays"
  >~ [`TupleT tys`] >- suspend "tuple"
  >~ [`StructT nsid`] >- suspend "struct"
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_abi_dynamic_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_abi_dynamic_def, is_bytestring_type_def]) >>
  gvs[is_abi_dynamic_def]
QED

Resume store_slots_rank_run_mem[arrays]:
  qpat_x_assum `evaluate_type tenv (ArrayT elem bd) = SOME tv` mp_tac >>
  disch_then (strip_assume_tac o SRULE [vyperValueTheory.evaluate_type_def, LET_THM, AllCaseEqs()]) >>
  rename1 `evaluate_type tenv elem = SOME etv` >>
  qpat_x_assum `ArrayTV etv bd = tv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `bd`
  >- suspend "fixed"
  >> suspend "dynarray"
QED
Resume store_slots_rank_run_mem[tuple]:
  drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  Cases_on `v` >> FULL_SIMP_TAC (srw_ss()) [value_has_type_def] >>
  rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
  Cases_on `av` >> FULL_SIMP_TAC (srw_ss()) [value_has_type_def] >>
  rename1 `values_have_types tvs vs` >>
  `LENGTH vs = LENGTH tvs` by metis_tac[vyperTypingTheory.values_have_types_length] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_bytestring_type_def] >> strip_tac >>
  drule store_slots_members_run_mem >>
  disch_then (qspecl_then [`tvs`, `vs`, `ctx`] mp_tac) >>
  disch_then (qspecl_then [`func`, `s`, `sw`, `dw`] mp_tac) >>
  (impl_tac >- suspend "tuple_members") >>
  strip_tac >> qexistsl_tac [`t`, `ks`] >> simp[] >>
  fs[vyperStorageTheory.encode_value_def] >>
  drule_all store_slots_tuple_support >> simp[ADD_COMM]
QED
Resume store_slots_rank_run_mem[struct]:
  qpat_x_assum `evaluate_type tenv (StructT nsid) = SOME tv` mp_tac >>
  disch_then (strip_assume_tac o SRULE [vyperValueTheory.evaluate_type_def, LET_THM, AllCaseEqs()]) >>
  qpat_x_assum `v1 = StructArgs args` SUBST_ALL_TAC >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (fs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  qpat_x_assum `_ = tv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `v` >> FULL_SIMP_TAC (srw_ss()) [value_has_type_def] >>
  rename1 `struct_has_type _ vals` >>
  `fields_val_wf vals (ZIP (MAP FST args,tvs))` by
    metis_tac[cj 5 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `values_have_types tvs (MAP SND vals) /\ LENGTH vals = LENGTH tvs` by
    metis_tac[placeStoreStorageTheory.place_store_struct_tuple_values, listTheory.LENGTH_MAP] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_bytestring_type_def, get_struct_fields_def] >> strip_tac >>
  drule store_slots_members_run_mem >>
  disch_then (qspecl_then [`tvs`, `MAP SND vals`, `ctx`] mp_tac) >>
  disch_then (qspecl_then [`func`, `s`, `sw`, `dw`] mp_tac) >>
  (impl_tac >- suspend "struct_members") >>
  strip_tac >> qexistsl_tac [`t`, `ks`] >> simp[] >>
  suspend "struct_support"
QED
Resume store_slots_rank_run_mem[fixed]:
  Cases_on `v` >> FULL_SIMP_TAC (srw_ss()) [value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv (Fixed cap)) (ArrayV av)` >>
  Cases_on `av` >> FULL_SIMP_TAC (srw_ss()) [value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  irule store_slots_sarray_run_mem >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `elem`, `slot`, `src`] >>
  simp[value_has_type_def] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (conj_tac
      >- (fs[vyperValueTheory.type_slot_size_def] >>
          `cap <= cap * type_slot_size etv` by
            (Cases_on `type_slot_size etv` >> fs[MULT_CLAUSES]) >> decide_tac) >>
      irule typedMemoryCopyTheory.typed_copy_memory_size >>
      qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields elem` mp_tac) >>
  (impl_tac >- (fs[type_rank_def] >> decide_tac)) >>
  disch_then (qspecl_then [`cenv`, `tenv`, `ctx`, `elem`, `etv`, `v`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED
Resume store_slots_rank_run_mem[dynarray]:
  Cases_on `v` >> FULL_SIMP_TAC (srw_ss()) [value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av)` >>
  Cases_on `av` >> FULL_SIMP_TAC (srw_ss()) [value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  irule store_slots_dynarray_run_mem >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `elem`, `slot`, `src`] >>
  simp[value_has_type_def] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_memory_size >>
      qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields elem` mp_tac) >>
  (impl_tac >- (fs[type_rank_def] >> decide_tac)) >>
  disch_then (qspecl_then [`cenv`, `tenv`, `ctx`, `elem`, `etv`, `v`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED
Resume store_slots_rank_run_mem[tuple_members]:
  simp[valueEncodingTheory.val_in_memory_def,
    valueEncodingTheory.type_memory_size_def, vyperValueTheory.type_slot_size_def] >>
  conj_tac >- suspend "tuple_alignment" >>
  fs[valueEncodingTheory.val_in_memory_def,
     valueEncodingTheory.type_memory_size_def, vyperValueTheory.type_slot_size_def] >>
  first_assum ACCEPT_TAC
QED
Resume store_slots_rank_run_mem[tuple_alignment]:
  fs[vyperTypeDefaultsTheory.values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >> rpt gen_tac >> disch_tac >>
  rename1 `idx < LENGTH tvs` >>
  `evaluate_type tenv (EL idx tys) = SOME (EL idx tvs)` by metis_tac[] >>
  `value_has_type (EL idx tvs) (EL idx vs)` by metis_tac[] >>
  conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_memory_size >>
      qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[value_has_type_equiv] >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields (EL idx tys)` mp_tac) >>
  (impl_tac >- (qpat_x_assum `type_rank _ (TupleT _) = n` (SUBST1_TAC o SYM) >>
    irule member_rank_lt_tuple >> simp[EL_MEM])) >>
  disch_then (qspecl_then [`cenv`, `tenv`, `ctx`] mp_tac) >>
  disch_then (qspecl_then [`EL idx tys`, `EL idx tvs`, `EL idx vs`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED
Resume store_slots_rank_run_mem[struct_members]:
  `LENGTH (MAP FST args) = LENGTH tvs` by simp[] >>
  simp[valueEncodingTheory.val_in_memory_def,
    valueEncodingProofsTheory.fields_in_memory_tuple,
    valueEncodingTheory.type_memory_size_def,
    valueEncodingTypingTheory.type_memory_size_fields_zip,
    vyperValueTheory.type_slot_size_def,
    vyperStorageRegionWriteTheory.type_slot_size_fields_list, MAP_ZIP] >>
  conj_tac >- suspend "struct_alignment" >>
  fs[valueEncodingTheory.val_in_memory_def,
    valueEncodingProofsTheory.fields_in_memory_tuple,
    valueEncodingTheory.type_memory_size_def,
    valueEncodingTypingTheory.type_memory_size_fields_zip,
    vyperValueTheory.type_slot_size_def,
    vyperStorageRegionWriteTheory.type_slot_size_fields_list, MAP_ZIP] >>
  first_assum ACCEPT_TAC
QED
Resume store_slots_rank_run_mem[struct_support]:
  `LENGTH (MAP FST args) = LENGTH tvs` by simp[] >>
  `!i. i < LENGTH tvs ==>
    SND (EL i (ZIP (MAP FST args,tvs))) = EL i tvs /\
    SND (EL i vals) = EL i (MAP SND vals)` by
    (rpt strip_tac >> simp[EL_ZIP, EL_MAP]) >>
  fs[vyperStorageTheory.encode_value_def] >>
  drule store_slots_struct_support >> simp[MAP_ZIP] >>
  disch_then assume_tac >> gen_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[SF CONJ_ss, ADD_COMM]
QED
Resume store_slots_rank_run_mem[struct_alignment]:
  `LENGTH fields = LENGTH tvs` by metis_tac[LENGTH_MAP] >>
  qpat_assum `evaluate_types tenv _ [] = SOME tvs`
    (mp_tac o SRULE [vyperValueTheory.evaluate_types_OPT_MMAP]) >>
  disch_then (strip_assume_tac o MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
  fs[vyperTypeDefaultsTheory.values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >> rpt gen_tac >> disch_tac >>
  rename1 `idx < LENGTH tvs` >>
  `evaluate_type tenv (FST (SND (EL idx fields))) = SOME (EL idx tvs)` by
    (qpat_x_assum `MAP (FST o SND) fields = MAP SND args` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `EL idx`) >> simp[EL_MAP] >> strip_tac >>
     qpat_x_assum `!k. k < LENGTH args ==> _`
       (qspec_then `idx` mp_tac) >> simp[EL_MAP]) >>
  `value_has_type (EL idx tvs) (SND (EL idx vals))` by
    (qpat_x_assum `!k. k < LENGTH tvs ==> value_has_type _ _`
      (qspec_then `idx` mp_tac) >> simp[EL_MAP]) >>
  simp[pairTheory.ELIM_UNCURRY] >>
  conj_tac >- suspend "struct_size" >>
  conj_tac >- metis_tac[value_has_type_equiv] >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields (FST (SND (EL idx fields)))` mp_tac) >>
  (impl_tac >- suspend "struct_rank") >>
  disch_then (qspecl_then [`cenv`, `tenv`, `ctx`] mp_tac) >>
  disch_then (qspecl_then [`FST (SND (EL idx fields))`, `EL idx tvs`,
    `SND (EL idx vals)`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED
Resume store_slots_rank_run_mem[struct_size]:
  qpat_x_assum `!name fields. FLOOKUP _ name = SOME fields ==> _`
    (qspec_then `nsid_to_string nsid` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `EVERY _ fields` mp_tac >>
  simp[EVERY_EL, pairTheory.ELIM_UNCURRY] >>
  disch_then (qspec_then `idx` mp_tac) >> simp[]
QED
Resume store_slots_rank_run_mem[struct_rank]:
  qpat_x_assum `type_rank _ (StructT _) = n` (SUBST1_TAC o SYM) >>
  once_rewrite_tac[type_rank_nsid] >>
  irule member_rank_lt_struct >> simp[get_struct_fields_def] >>
  qexistsl_tac [`SND (SND (EL idx fields))`, `FST (EL idx fields)`] >>
  simp[pairTheory.PAIR, EL_MEM]
QED
Finalise store_slots_rank_run_mem
