(* Counted memory-safe sparse array stores. *)
Theory storeSlotsCountedArrays
Ancestors
  storeSlotsCountedElements placeStoreSlots context compileEnv fragGasMode
  stmtSimStoreCopy valueEncoding valueEncodingProps valueEncodingProofs
  vyperValue vyperTyping venomState words arithmetic list rich_list finite_map

Theorem store_slots_sarray_run_mem:
  !cenv ctx elem etv n sparse src slot tr sa sb func s sw dw writes.
    compile_store_slots cenv src slot (ArrayT elem (Fixed n)) tr sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    is_abi_dynamic cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
    type_memory_bytes cenv elem = type_memory_size etv /\
    (!v src slot tr sa sb func s sw dw writes.
      value_has_type etv v /\
      compile_store_slots cenv src slot elem tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory etv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size etv < dimword (:256) /\
      w2n sw + type_memory_size etv <= s.vs_alloca_next /\
      w2n dw + type_slot_size etv <= dimword (:256) /\
      encode_value etv v = SOME writes /\
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
        t.vs_inst_idx = LENGTH sb.cs_current_insts) /\
    value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV sparse)) /\
    encode_value (ArrayTV etv (Fixed n)) (ArrayV (SArrayV sparse)) = SOME writes /\
    (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    val_in_memory (ArrayTV etv (Fixed n)) (ArrayV (SArrayV sparse)) (w2n sw) s.vs_memory /\
    n < dimword (:256) /\
    w2n sw + type_memory_size (ArrayTV etv (Fixed n)) < dimword (:256) /\
    w2n sw + type_memory_size (ArrayTV etv (Fixed n)) <= s.vs_alloca_next /\
    w2n dw + type_slot_size (ArrayTV etv (Fixed n)) <= dimword (:256) /\
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
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_bytestring_type_def] >> strip_tac >>
  `!i. i < n ==>
    value_has_type etv (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)` by
    (rpt strip_tac >> Cases_on `ALOOKUP sparse i` >>
     simp[default_value_well_typed] >>
     fs[value_has_type_def] >> metis_tac[sparse_has_type_lookup]) >>
  `!i. i < n ==>
    val_in_memory etv (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)
      (w2n sw + i * type_memory_size etv) s.vs_memory` by
    (gvs[val_in_memory_sarray] >> rpt strip_tac >>
     Cases_on `ALOOKUP sparse i` >> simp[] >> metis_tac[kvs_in_memory_lookup]) >>
  drule store_slots_elements_run_mem >>
  disch_then (qspecl_then [`ctx`, `etv`,
    `\i. case ALOOKUP sparse i of NONE => default_value etv | SOME v => v`,
    `n`, `func`, `s`, `sw`, `dw`] mp_tac) >>
  (impl_tac >-
    (simp[eval_operand_def, type_memory_size_def, type_slot_size_def] >>
     reverse conj_tac
     >- (fs[type_memory_size_def, type_slot_size_def] >> metis_tac[]) >>
     gen_tac >> strip_tac >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!v src slot tr sa sb func s sw dw writes. _`
           (qspec_then `case ALOOKUP sparse r of NONE => default_value etv | SOME v => v` mp_tac) >>
         simp[] >> disch_then irule >> simp[] >> metis_tac[]) >>
     metis_tac[value_has_type_equiv])) >>
  strip_tac >> qexistsl_tac [`t`, `ks`] >> simp[] >>
  drule_all store_slots_sarray_support >> simp[ADD_COMM]
QED
