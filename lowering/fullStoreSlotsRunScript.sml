(* Canonical typed sparse execution, assembled by type rank. *)
Theory fullStoreSlotsRun
Ancestors
  fullStoreSlotsLeafCases fullStoreSlotsArrayCases fullStoreSlotsCompositeCases
  fullStoreSlotsTupleAlign fullStoreSlotsStructAlign fullStoreSlotsTypedEntry
  abiTypeBoundProps typedMemoryCopy typedCopyDomain valueEncodingTyping
  context vyperValue compileEnv arithmetic valueEncoding

Theorem store_slots_origin_ptr:
  !ty tv v.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  assignable_type tenv ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  !ctx lo root slot tr sa sb func s sw dw writes G tn.
  compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
  not_fresh_at sa root /\ (!x. slot=Var x ==> not_fresh_at sa x) /\
  lookup_var root s=SOME sw /\ eval_operand slot s=SOME dw /\
  op_prov G slot=NONE /\ op_taint tn slot={} /\
  ptr_covers G tn root s (val_store_size tv v) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw) m) /\
  w2n sw+type_memory_size tv<dimword(:256) /\
  w2n dw+type_slot_size tv<=dimword(:256) /\
  encode_value tv v=SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb=sa.cs_current_bb /\
  s.vs_inst_idx=LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n sw+val_store_size tv v<=s.vs_alloca_next ==>
  ?Gf tf u ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u =
      FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n sw+32*k) s) q) s ks /\
    u.vs_memory=s.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (dw+n2w k)
        (mem_word_taint tn.t_mem (w2n sw+32*k)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans) /\
    (!k. MEM k ks <=> MEM k (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x u=lookup_var x s /\
      FLOOKUP Gf x=FLOOKUP G x /\ op_taint tf (Var x)=op_taint tn (Var x)) /\
    u.vs_allocas=s.vs_allocas /\ u.vs_alloca_next=s.vs_alloca_next /\
    u.vs_labels=s.vs_labels /\ u.vs_call_ctx=s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sb.cs_current_bb /\
    u.vs_inst_idx=LENGTH sb.cs_current_insts
Proof
  measureInduct_on `type_rank cenv.ce_struct_fields ty` >>
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields ty`
  >- (Cases_on `is_bytestring_type ty`
      >- (rpt gen_tac >> strip_tac >> irule store_slots_leaf_origin_ptr >>
          asm_simp_tac bool_ss [] >> qexistsl_tac [`cenv`,`root`,`slot`,`tenv`,`tv`,`ty`,`v`] >>
          asm_simp_tac bool_ss []) >>
      suspend "composite") >>
  `~vyper_is_dynamic tenv ty` by metis_tac[abi_props_vyper_typed] >>
  rpt gen_tac >> strip_tac >> irule store_slots_leaf_origin_ptr >>
  asm_simp_tac bool_ss [] >> qexistsl_tac [`cenv`,`root`,`slot`,`tenv`,`tv`,`ty`,`v`] >>
  asm_simp_tac bool_ss []
QED

Resume store_slots_origin_ptr[composite]:
  Cases_on `ty` >> gvs[is_bytestring_type_def, is_abi_dynamic_def]
  >~ [`evaluate_type tenv (BaseT bt) = SOME tv`]
  >- (Cases_on `bt` >> gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_bytestring_type_def, is_abi_dynamic_def])
  >~ [`evaluate_type tenv (ArrayT elem bd) = SOME tv`]
  >- suspend "array"
  >~ [`evaluate_type tenv (TupleT tys) = SOME tv`]
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume store_slots_origin_ptr[array]:
  qpat_x_assum `evaluate_type tenv (ArrayT elem bd) = SOME tv`
    (strip_assume_tac o SRULE [AllCaseEqs()] o
      SRULE [Once evaluate_type_def, LET_THM, AllCaseEqs()]) >>
  qpat_x_assum `ArrayTV _ _ = tv` (SUBST_ALL_TAC o SYM) >>
  rename1 `evaluate_type tenv elem = SOME etv` >>
  `assignable_type tenv elem` by fs[vyperTypeSystemTheory.assignable_type_def] >>
  `type_rank cenv.ce_struct_fields elem < type_rank cenv.ce_struct_fields (ArrayT elem bd)` by
    simp[type_rank_def] >>
  first_x_assum (drule_then assume_tac) >>
  `type_memory_bytes cenv elem = type_memory_size etv` by
    (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `0 < type_memory_size etv` by metis_tac[store_slots_assignable_memory_positive] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`) store_slots_array_origin_ptr >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`tn`,`lo`,`ctx`,`G`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >>
    conj_tac >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!tv' v' ctx lo root slot tr sa sb func s sw dw writes G tn. _`
        (qspecl_then [`etv`,`v'`,`ctx`,`lo`] mp_tac) >>
      disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
      disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      simp[] >> (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
    conj_tac >- (Cases_on `bd` >>
      fs[type_memory_size_def] >>
      irule store_slots_positive_stride_count >>
      qexistsl_tac [`w2n sw`,`type_memory_size etv`] >> simp[] >> decide_tac) >>
    simp[] >> metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value])) >>
  simp[]
QED

Resume store_slots_origin_ptr[tuple]:
  drule_at (Pat `evaluate_type _ _ = _`) (Q.INST [`R` |-> `\cty ctv cv.
    type_rank cenv.ce_struct_fields cty < type_rank cenv.ce_struct_fields (TupleT tys) /\
    evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv`]
    store_slots_tuple_align) >>
  disch_then (qspecl_then [`v`,`cenv`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `tv = TupleTV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  `LIST_REL (\(ty,sz) (tv,v).
      sz = type_memory_size tv /\
      (type_rank cenv.ce_struct_fields ty < type_rank cenv.ce_struct_fields (TupleT tys) /\
       assignable_type tenv ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v) /\
      IS_SOME (encode_value tv v) /\ val_store_size tv v <= type_memory_size tv)
    (MAP (\ty. (ty,type_memory_bytes cenv ty)) tys) (ZIP (tvs,vs))` by
    (fs[listTheory.LIST_REL_EL_EQN,vyperTypeSystemTheory.assignable_type_def,listTheory.EVERY_EL] >>
     rpt strip_tac >> first_x_assum (qspec_then `n` mp_tac) >>
     fs[listTheory.EL_MAP,listTheory.EL_ZIP]) >>
  qpat_x_assum `LIST_REL (\(ty,sz) (tv,v). _ /\ (\cty ctv cv. _) ty tv v /\ _) _ _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def,LET_THM,is_abi_dynamic_def,is_bytestring_type_def] >>
  disch_tac >>
  drule_at (Pat `compile_store_slots_members _ _ _ _ _ _ _ _ = _`)
    (Q.INST [`R` |-> `\cty ctv cv.
      type_rank cenv.ce_struct_fields cty < type_rank cenv.ce_struct_fields (TupleT tys) /\
      assignable_type tenv cty /\ evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv`]
      store_slots_members_origin_ptr) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspecl_then [`tys`,`tenv`,`cenv`,`tvs`,`vs`,`ctx`,`lo`,`func`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        qpat_x_assum `!y. type_rank _ y < _ ==> _` (drule_then assume_tac) >>
        first_x_assum (drule_at (Pat `assignable_type _ _`)) >>
        disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
        disch_then (drule_at (Pat `value_has_type _ _`)) >>
        disch_then assume_tac >> rpt gen_tac >> strip_tac >>
        qpat_x_assum `!ctx lo root slot tr sa sb func s sw dw writes G tn. _`
          (qspecl_then [`ctx`,`lo`] mp_tac) >>
        disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
        disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
        disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
        disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
        disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
        simp[] >> (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
    suspend "tuple_resources")) >>
  suspend "tuple_support"
QED

Resume store_slots_origin_ptr[tuple_resources]:
  qpat_x_assum `!y. type_rank _ y < _ ==> _` kall_tac >>
  fs[exprSimPropsTheory.val_store_size_def,type_memory_size_def,type_slot_size_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >>
    simp[Once valueEncodingDefsTheory.val_in_memory_def,LET_THM]) >>
  `EVERY (\tv. 0 < type_slot_size tv) tvs` by
    (fs[listTheory.EVERY_EL,listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_x_assum `!n. n < LENGTH tys ==> _` (qspec_then `n` mp_tac) >>
     simp[listTheory.EL_MAP,listTheory.EL_ZIP] >> strip_tac >>
     metis_tac[vyperTypeSystemTheory.assignable_type_slot_size_pos]) >>
  rpt strip_tac >>
  `tuple_prefix_slot_size i tvs < type_slot_size_list tvs` by
    (simp[vyperStateTheory.tuple_prefix_slot_size_sum,vyperStorageRegionWriteTheory.type_slot_size_list_sum] >>
     irule store_slots_positive_prefix >> simp[]) >> decide_tac
QED

Resume store_slots_origin_ptr[tuple_support]:
  qpat_x_assum `encode_value _ _ = SOME writes`
    (mp_tac o SRULE [Once vyperStorageTheory.encode_value_def]) >>
  disch_then (fn th => assume_tac th) >>
  drule_at (Pat `encode_tuple _ _ _ = _`) placeStoreSlotsTheory.store_slots_tuple_support >>
  simp[] >> disch_tac >> strip_tac >>
  qexistsl_tac [`Gf`,`tf`,`u`,`ks`] >> simp[]
QED

Resume store_slots_origin_ptr[struct]:
  drule_at (Pat `evaluate_type _ _ = _`) (Q.INST [`R` |-> `\cty ctv cv.
    type_rank cenv.ce_struct_fields cty < type_rank cenv.ce_struct_fields (StructT p) /\
    evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv`]
    store_slots_struct_align_full) >>
  disch_then (qspecl_then [`tenv`,`p`,`cenv`,`cenv`,`v`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> first_assum (drule_then strip_assume_tac) >> simp[])) >>
  strip_tac >>
  qpat_x_assum `tv = StructTV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  `EVERY (\fld. assignable_type tenv (FST (SND fld))) fields` by
    (qpat_assum `evaluate_type _ (StructT _) = _`
       (strip_assume_tac o SRULE [Once vyperValueTheory.evaluate_type_def,AllCaseEqs()]) >>
     qpat_x_assum `_ = StructArgs args` SUBST_ALL_TAC >>
     `MAP (FST o SND) fields = MAP SND args` by
       (fs[loweringStateRelDefsTheory.sfields_tenv_consistent_def] >> metis_tac[optionTheory.SOME_11]) >>
     simp[listTheory.EVERY_MEM] >> rpt strip_tac >> rename1 `MEM fld fields` >>
     `MEM (FST (SND fld)) (MAP SND args)` by
       (qpat_x_assum `MAP _ fields = _` (fn th => rewrite_tac[GSYM th]) >>
        simp[listTheory.MEM_MAP] >> qexists_tac `fld` >> simp[]) >>
     pop_assum (strip_assume_tac o SRULE [listTheory.MEM_MAP]) >>
     drule_all store_slots_assignable_struct_child >> simp[]) >>
  suspend "struct_members"
QED

Resume store_slots_origin_ptr[struct_members]:
  `LIST_REL (\(ty,sz) (tv,v).
      sz = type_memory_size tv /\
      (type_rank cenv.ce_struct_fields ty < type_rank cenv.ce_struct_fields (StructT p) /\
       assignable_type tenv ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v) /\
      IS_SOME (encode_value tv v) /\ val_store_size tv v <= type_memory_size tv)
    (MAP SND fields) (ZIP (tvs,MAP SND vals))` by
    (fs[listTheory.LIST_REL_EL_EQN,listTheory.EVERY_EL] >> rpt strip_tac >>
     qpat_x_assum `!n. n < LENGTH fields ==> (\(ty,sz) (tv,v). _) _ _`
       (qspec_then `n` mp_tac) >>
     fs[listTheory.EL_MAP,listTheory.EL_ZIP] >>
     Cases_on `SND (EL n fields)` >> fs[] >>
     qpat_x_assum `!n. n < LENGTH fields ==> assignable_type _ _`
       (qspec_then `n` mp_tac) >> gvs[]) >>
  qpat_x_assum `LIST_REL (\(ty,sz) (tv,v). _ /\ (\cty ctv cv. _) ty tv v /\ _) _ _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def,LET_THM,is_abi_dynamic_def,is_bytestring_type_def] >>
  disch_tac >>
  drule_at (Pat `compile_store_slots_members _ _ _ _ _ _ _ _ = _`)
    (Q.INST [`R` |-> `\cty ctv cv.
      type_rank cenv.ce_struct_fields cty < type_rank cenv.ce_struct_fields (StructT p) /\
      assignable_type tenv cty /\ evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv`]
      store_slots_members_origin_ptr) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspecl_then [`tenv`,`p`,`cenv`,`tvs`,`MAP SND vals`,`ctx`,`lo`,`func`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        qpat_x_assum `!y. type_rank _ y < _ ==> _` (drule_then assume_tac) >>
        first_x_assum (drule_at (Pat `assignable_type _ _`)) >>
        disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
        disch_then (drule_at (Pat `value_has_type _ _`)) >>
        disch_then assume_tac >> rpt gen_tac >> strip_tac >>
        qpat_x_assum `!ctx lo root slot tr sa sb func s sw dw writes G tn. _`
          (qspecl_then [`ctx`,`lo`] mp_tac) >>
        disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
        disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
        disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
        disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
        disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
        simp[] >> (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
    suspend "struct_resources")) >>
  suspend "struct_support"
QED

Resume store_slots_origin_ptr[struct_resources]:
  qpat_x_assum `!y. type_rank _ y < _ ==> _` kall_tac >>
  fs[compileEnvTheory.get_struct_fields_def,
     exprSimPropsTheory.val_store_size_def,type_memory_size_def,type_slot_size_def,
     valueEncodingTypingTheory.type_memory_size_fields_zip,
     vyperStorageRegionWriteTheory.type_slot_size_fields_list,listTheory.MAP_ZIP] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >>
    simp[Once valueEncodingDefsTheory.val_in_memory_def,
         valueEncodingProofsTheory.fields_in_memory_tuple,listTheory.MAP_ZIP,LET_THM]) >>
  `EVERY (\tv. 0 < type_slot_size tv) tvs` by
    (fs[listTheory.EVERY_EL,listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_x_assum `!n. n < LENGTH fields ==> _` (qspec_then `n` mp_tac) >>
     simp[listTheory.EL_MAP,listTheory.EL_ZIP] >> strip_tac >>
     Cases_on `SND (EL n fields)` >> gvs[] >>
     metis_tac[vyperTypeSystemTheory.assignable_type_slot_size_pos]) >>
  gvs[listTheory.MAP_ZIP,valueEncodingTypingTheory.type_memory_size_fields_zip] >>
  rpt strip_tac >>
  `tuple_prefix_slot_size i tvs < type_slot_size_list tvs` by
    (simp[vyperStateTheory.tuple_prefix_slot_size_sum,vyperStorageRegionWriteTheory.type_slot_size_list_sum] >>
     irule store_slots_positive_prefix >> simp[]) >> decide_tac
QED

Resume store_slots_origin_ptr[struct_support]:
  qpat_x_assum `!y. type_rank _ y < _ ==> _` kall_tac >>
  qpat_x_assum `encode_value _ _ = SOME writes`
    (mp_tac o SRULE [Once vyperStorageTheory.encode_value_def]) >>
  disch_then assume_tac >>
  drule_at (Pat `encode_struct _ _ _ = _`) placeStoreSlotsTheory.store_slots_struct_support >>
  simp[listTheory.MAP_ZIP,listTheory.EL_ZIP,listTheory.EL_MAP] >>
  disch_tac >> strip_tac >>
  qexistsl_tac [`Gf`,`tf`,`u`,`ks`] >> simp[] >>
  `!i. i < LENGTH tvs ==>
     SND (EL i (ZIP (MAP FST fields,tvs))) = EL i tvs /\
     EL i (MAP SND vals) = SND (EL i vals)` by
    (rpt strip_tac >> simp[listTheory.EL_ZIP,listTheory.EL_MAP]) >>
  metis_tac[]
QED

Finalise store_slots_origin_ptr


Theorem store_slots_live_fold_state:
  !H cenv cx env ee ctx func s tr rootk region path delta tv
   dw writes v ks (sw:bytes32).
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel H ctx func cenv cx ee s /\
  MEM (tr,rootk,region) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion region path delta tv /\
  w2n dw = w2n rootk + delta /\ 0 < type_slot_size tv /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  w2n dw + type_slot_size tv <= dimword(:256) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  well_formed_type_value tv /\ val_in_memory tv v (w2n sw) s.vs_memory ==>
  stmt_state_rel H ctx func cenv cx
    (set_storage cx ee tr (apply_writes dw writes (get_storage cx ee tr)))
    (FOLDL (\q i. (if tr then tstore else sstore) (dw+n2w i)
      (mload (w2n sw+32*i) s) q) s ks)
Proof
  rpt gen_tac >> strip_tac >>
  irule (BETA_RULE o PURE_REWRITE_RULE [GSYM wordsTheory.word_add_n2w,wordsTheory.n2w_w2n] $
    (Q.INST [`start` |-> `w2n (dw:bytes32)`, `rd` |-> `\i. mload (w2n (sw:bytes32)+32*i) s`]
      (SPEC_ALL placeStoreSlotsTheory.place_store_encoded_leaf_state_sparse))) >>
  simp[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
  simp[] >> rpt strip_tac >>
  rewrite_tac[GSYM wordsTheory.word_add_n2w] >>
  drule_at (Pat `val_in_memory _ _ _ _`)
    storageCopyLiveTheory.encode_value_memory_live >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (qspecl_then [`dw`,`get_storage cx ee tr`,`i`,`b`] mp_tac) >>
  simp[valueEncodingPropsTheory.mem_word_at_eq_mload,
       GSYM wordsTheory.word_add_n2w]
QED

Theorem store_slots_encoded_endpoint:
  !ty tv v.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  assignable_type tenv ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  !ctx lo root slot tr sa sb func s sw dw writes G tn.
  compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
  not_fresh_at sa root /\ (!x. slot=Var x ==> not_fresh_at sa x) /\
  lookup_var root s=SOME sw /\ eval_operand slot s=SOME dw /\
  op_prov G slot=NONE /\ op_taint tn slot={} /\
  ptr_covers G tn root s (val_store_size tv v) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw) m) /\
  w2n sw+type_memory_size tv<dimword(:256) /\
  w2n dw+type_slot_size tv<=dimword(:256) /\
  encode_value tv v=SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb=sa.cs_current_bb /\
  s.vs_inst_idx=LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n sw+val_store_size tv v<=s.vs_alloca_next ==>
  ?Gf tf u ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u =
      FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n sw+32*k) s) q) s ks /\
    u.vs_memory=s.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (dw+n2w k)
        (mem_word_taint tn.t_mem (w2n sw+32*k)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans) /\
    (!k. MEM k ks <=> MEM k (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x u=lookup_var x s /\
      FLOOKUP Gf x=FLOOKUP G x /\ op_taint tf (Var x)=op_taint tn (Var x)) /\
    u.vs_allocas=s.vs_allocas /\ u.vs_alloca_next=s.vs_alloca_next /\
    u.vs_labels=s.vs_labels /\ u.vs_call_ctx=s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sb.cs_current_bb /\
    u.vs_inst_idx=LENGTH sb.cs_current_insts /\
    (!H cx env ee rootk region path delta.
      expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
      MEM (tr,rootk,region) (FST H) /\ regions_consistent (FST H) /\
      storage_locks_separated (FST H) (SND H) /\
      storage_subregion region path delta tv /\
      w2n dw = w2n rootk + delta /\ 0 < type_slot_size tv /\
      well_formed_type_value tv ==>
      stmt_state_rel H ctx func cenv cx
        (set_storage cx ee tr (apply_writes dw writes (get_storage cx ee tr)))
        (store_copy_normalize s u))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all store_slots_origin_ptr >>
  strip_tac >>
  qexistsl_tac [`Gf`,`tf`,`u`,`ks`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule store_slots_live_fold_state >>
  metis_tac[bodyPtrDefsTheory.mem_agree_outside_def]
QED
