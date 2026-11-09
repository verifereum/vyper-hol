(* Counted memory-safe tuple and struct sparse-store entries. *)
Theory storeSlotsCountedEntries
Ancestors
  storeSlotsCountedMembers placeStoreSlots typedCopyMetadata
  valueEncodingTyping valueEncodingProofs vyperTypeExprSoundness
  vyperTypeABI vyperStorageRegionWrite stmtSimStoreCopy
  context compileEnv fragGasMode venomState venomInst venomExecSemantics
  emitHelperProps exprLoweringProps words arithmetic list rich_list
  vyperTypeValues vyperTypeDefaults vyperTyping valueEncoding valueEncodingProps
  typedCopyDomain typedMemoryCopy vyperStorage vyperValue placeStoreStorage



Theorem store_slots_tuple_entry_mem:
  !cenv tenv ctx tys tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (TupleT tys) /\
    evaluate_type tenv (TupleT tys) = SOME tv /\ value_has_type tv v /\
    (!cty ctv cv.
      type_rank cenv.ce_struct_fields cty <
        type_rank cenv.ce_struct_fields (TupleT tys) /\
      evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
      !src slot tr sa sb func s sw dw writes.
        compile_store_slots cenv src slot cty tr sa = ((),sb) /\
        (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
        eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
        val_in_memory ctv cv (w2n sw) s.vs_memory /\
        w2n sw + type_memory_size ctv < dimword (:256) /\
        w2n sw + type_memory_size ctv <= s.vs_alloca_next /\
        w2n dw + type_slot_size ctv <= dimword (:256) /\
        encode_value ctv cv = SOME writes /\
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
          t.vs_inst_idx = LENGTH sb.cs_current_insts) ==>
    !src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot (TupleT tys) tr sa = ((),sb) /\
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
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P = \cty ctv cv.
    !src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot cty tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory ctv cv (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size ctv < dimword (:256) /\
      w2n sw + type_memory_size ctv <= s.vs_alloca_next /\
      w2n dw + type_slot_size ctv <= dimword (:256) /\
      encode_value ctv cv = SOME writes /\
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
        t.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  `!cty ctv cv. type_rank cenv.ce_struct_fields cty <
     type_rank cenv.ce_struct_fields (TupleT tys) /\
     evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==> P cty ctv cv` by
    (simp[Abbr `P`] >> gvs[]) >>
  qpat_x_assum `!cty ctv cv. _ ==> !src slot tr sa sb func s sw dw writes. _` kall_tac >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `values_have_types tvs vs` >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  `LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
       IS_SOME (encode_value tv v) /\ P ty tv v)
       (MAP (\ty. (ty,type_memory_bytes cenv ty)) tys) (ZIP (tvs,vs))` by
    suspend "alignment" >>
  suspend "execution"
QED

Resume store_slots_tuple_entry_mem[alignment]:
  gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >> rpt strip_tac >>
  rename1 `idx < LENGTH tvs` >>
  `evaluate_type tenv (EL idx tys) = SOME (EL idx tvs)` by metis_tac[] >>
  `value_has_type (EL idx tvs) (EL idx vs)` by metis_tac[] >>
  rpt conj_tac
  >- (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[])
  >- metis_tac[value_has_type_equiv] >>
  first_x_assum irule >> simp[] >> irule member_rank_lt_tuple >> simp[EL_MEM]
QED

Resume store_slots_tuple_entry_mem[execution]:
  simp[Abbr `P`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_bytestring_type_def] >> strip_tac >>
  fs[val_in_memory_def, type_memory_size_def, type_slot_size_def, encode_value_def] >>
  drule store_slots_members_run_mem >>
  disch_then (qspecl_then [`tvs`, `vs`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`func`, `s`, `sw`, `dw`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`t`, `ks`] >> simp[] >>
  drule_all store_slots_tuple_support >> simp[]
QED

Finalise store_slots_tuple_entry_mem

Theorem store_slots_struct_entry_mem:
  !cenv tenv ctx nsid tv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_abi_dynamic cenv.ce_struct_fields (StructT nsid) /\
    evaluate_type tenv (StructT nsid) = SOME tv /\ value_has_type tv v /\
    (!cty ctv cv.
      type_rank cenv.ce_struct_fields cty <
        type_rank cenv.ce_struct_fields (StructT nsid) /\
      evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==>
      !src slot tr sa sb func s sw dw writes.
        compile_store_slots cenv src slot cty tr sa = ((),sb) /\
        (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
        eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
        val_in_memory ctv cv (w2n sw) s.vs_memory /\
        w2n sw + type_memory_size ctv < dimword (:256) /\
        w2n sw + type_memory_size ctv <= s.vs_alloca_next /\
        w2n dw + type_slot_size ctv <= dimword (:256) /\
        encode_value ctv cv = SOME writes /\
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
          t.vs_inst_idx = LENGTH sb.cs_current_insts) ==>
    !src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot (StructT nsid) tr sa = ((),sb) /\
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
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P = \cty ctv cv.
    !src slot tr sa sb func s sw dw writes.
      compile_store_slots cenv src slot cty tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory ctv cv (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size ctv < dimword (:256) /\
      w2n sw + type_memory_size ctv <= s.vs_alloca_next /\
      w2n dw + type_slot_size ctv <= dimword (:256) /\
      encode_value ctv cv = SOME writes /\
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
        t.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  `!cty ctv cv. type_rank cenv.ce_struct_fields cty <
     type_rank cenv.ce_struct_fields (StructT nsid) /\
     evaluate_type tenv cty = SOME ctv /\ value_has_type ctv cv ==> P cty ctv cv` by
    (simp[Abbr `P`] >> gvs[]) >>
  qpat_x_assum `!cty ctv cv. _ ==> !src slot tr sa sb func s sw dw writes. _` kall_tac >>
  suspend "metadata"
QED

Resume store_slots_struct_entry_mem[metadata]:
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv nsid = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `struct_has_type _ vals` >>
  `fields_val_wf vals (ZIP (MAP FST args,tvs))` by
    metis_tac[cj 5 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `values_have_types tvs (MAP SND vals) /\ LENGTH vals = LENGTH tvs` by
    metis_tac[place_store_struct_tuple_values, listTheory.LENGTH_MAP] >>
  `LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
      IS_SOME (encode_value tv v) /\ P ty tv v)
      (MAP SND fields) (ZIP (tvs,MAP SND vals))` by suspend "alignment" >>
  suspend "execution"
QED

Resume store_slots_struct_entry_mem[alignment]:
  qpat_x_assum `Abbrev _` kall_tac >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    fs[evaluate_types_OPT_MMAP] >>
  drule OPT_MMAP_LIST_REL >> strip_tac >>
  `LENGTH fields = LENGTH tvs` by
    (drule OPT_MMAP_LENGTH >> simp[]) >>
  `EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields` by metis_tac[] >>
  fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[LIST_REL_EL_EQN, EL_MAP, EL_ZIP] >> rpt strip_tac >>
  rename1 `idx < LENGTH tvs` >>
  `?fname fty sz. EL idx fields = (fname,fty,sz)` by metis_tac[pairTheory.PAIR] >>
  `evaluate_type tenv fty = SOME (EL idx tvs)` by
    (qpat_x_assum `!n. _ ==> evaluate_type _ _ = _`
       (qspec_then `idx` mp_tac) >> simp[EL_MAP]) >>
  `value_has_type (EL idx tvs) (SND (EL idx vals))` by
    (qpat_x_assum `!n. _ ==> value_has_type _ _`
       (qspec_then `idx` mp_tac) >> simp[EL_MAP]) >>
  simp[] >> rpt conj_tac
  >- (fs[EVERY_MEM] >>
      qpat_x_assum `!e. MEM e fields ==> _` (qspec_then `EL idx fields` mp_tac) >>
      simp[EL_MEM])
  >- metis_tac[value_has_type_equiv] >>
  first_x_assum irule >> simp[] >>
  once_rewrite_tac[type_rank_nsid] >> irule member_rank_lt_struct >>
  simp[get_struct_fields_def] >> metis_tac[EL_MEM]
QED

Resume store_slots_struct_entry_mem[execution]:
  `LENGTH fields = LENGTH tvs` by metis_tac[LENGTH_MAP] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by simp[] >>
  simp[Abbr `P`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_bytestring_type_def, get_struct_fields_def] >>
  strip_tac >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by
    (irule (cj 2 MAP_ZIP) >> simp[]) >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) =
     type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  fs[val_in_memory_def, fields_in_memory_tuple, MAP_ZIP, LENGTH_MAP,
     type_memory_size_def, type_memory_size_fields_zip,
     type_slot_size_def, type_slot_size_fields_list] >>
  drule store_slots_members_run_mem >>
  disch_then (qspecl_then [`tvs`, `MAP SND vals`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`func`, `s`, `sw`, `dw`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`t`, `ks`] >> simp[] >>
  `!i. i < LENGTH tvs ==>
    SND (EL i (ZIP (MAP FST args,tvs))) = EL i tvs /\
    SND (EL i vals) = EL i (MAP SND vals)` by
    (rpt strip_tac >> simp[EL_ZIP, EL_MAP]) >>
  fs[encode_value_def] >> drule store_slots_struct_support >>
  simp[] >> disch_then assume_tac >>
  gen_tac >> first_x_assum (qspec_then `j` mp_tac) >>
  simp[SF CONJ_ss, ADD_COMM]
QED

Finalise store_slots_struct_entry_mem
