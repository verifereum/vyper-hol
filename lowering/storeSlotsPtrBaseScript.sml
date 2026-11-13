(* Constructor assembly for sparse pointer-safe storage stores. *)
Theory storeSlotsPtrBase
Ancestors storeSlotsPtrInterface vyperValue stmtSimStoreCopy bodyMemAssignTopCopyFacts
  storeSlotsPtrReadResources storeSlotsPtrSingle storeSlotsPtrWordCopy
  storeSlotsPtrBytesCount placeStoreSlots assignBasePtrStorageExtent
  abiTypeBoundProps typedMemoryCopy vyperStorageCoverage vyperEncodeDecode
  exprSimProps exprLoweringProps loweringPosts context compileEnv loweringStateRelDefs
  bodyPtrDefs stateFrame ptrDiscipline fragGasPathPtr emitHelper emitHelperProps venomState
  valueEncoding valueEncodingDefs valueEncodingProps valueEncodingTyping vyperTyping
  list rich_list arithmetic words finite_map

Theorem store_slots_ptr_static_entry:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  store_slots_ptr_entry cenv D ctx PG ty tv v
Proof
  strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule typed_copy_memory_size >> metis_tac[]) >>
  `~vyper_is_dynamic tenv ty` by
    (drule_all abi_props_vyper_typed >> simp[]) >>
  `~is_bytestring_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     Cases_on `b` >> gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     Cases_on `b'` >> gvs[is_bytestring_type_def, is_abi_dynamic_def]) >>
  `val_store_size tv v = type_memory_size tv` by
    metis_tac[topcopy_val_store_size] >>
  rewrite_tac[store_slots_ptr_entry_def] >> rpt gen_tac >> strip_tac >>
  `!j. MEM j (MAP FST writes) <=> j < type_slot_size tv` by
    (gen_tac >> eq_tac
     >- metis_tac[CONJUNCT1 encode_writes_bounded] >>
     strip_tac >> irule encode_value_live_written >> metis_tac[]) >>
  `type_memory_bytes cenv ty DIV 32 = type_slot_size tv` by
    simp[type_memory_size_slots] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def] >>
  Cases_on `type_slot_size tv = 1`
  >- suspend "single" >>
  suspend "loop"
QED

Resume store_slots_ptr_static_entry[single]:
  gvs[] >> strip_tac >>
  `ptr_covers G tn root s 32` by
    (gvs[ptr_covers_def, type_memory_size_slots]) >>
  drule_all store_slots_single_compiled_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u`, `[0]`] >> simp[]
QED

Resume store_slots_ptr_static_entry[loop]:
  simp[compile_memory_to_transient_def, compile_memory_to_storage_def,
    compile_word_copy_loop_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `type_slot_size tv < dimword (:256) /\
   w2n sw + 32 * (type_slot_size tv - 1) < dimword (:256)` by
    (fs[type_memory_size_slots] >> decide_tac) >>
  `compile_word_copy_loop_op (Var root) slot (Lit (n2w (type_slot_size tv)))
     LocMemory (if tr then LocTransient else LocStorage) F sa = (_0,cs')` by
    (Cases_on `tr` >> gvs[compile_memory_to_transient_def,
      compile_memory_to_storage_def, compile_word_copy_loop_def]) >>
  `eval_operand (Lit (n2w (type_slot_size tv))) s =
     SOME (n2w (type_slot_size tv)) /\
   op_taint tn (Lit (n2w (type_slot_size tv))) = {} /\
   op_prov G (Lit (n2w (type_slot_size tv))) = NONE /\
   (!x. slot = Var x \/ Lit (n2w (type_slot_size tv)) = Var x ==>
     not_fresh_at sa x) /\
   32 * type_slot_size tv <= type_memory_size tv` by
    simp[eval_operand_def, op_taint_def, op_prov_def, type_memory_size_slots] >>
  drule_all store_slots_word_copy_op_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tf`, `u`, `GENLIST I (type_slot_size tv)`] >>
  simp[MEM_GENLIST]
QED

Finalise store_slots_ptr_static_entry

Theorem store_slots_ptr_bytes_entry:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  store_slots_ptr_entry cenv D ctx PG ty tv v
Proof
  strip_tac >>
  `?cap. tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[is_bytestring_type_def, evaluate_type_def]) >>
  `is_abi_dynamic cenv.ce_struct_fields ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[is_bytestring_type_def, is_abi_dynamic_def]) >>
  rewrite_tac[store_slots_ptr_entry_def] >> rpt gen_tac >> strip_tac >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    metis_tac[mem_agree_outside_def] >>
  drule_at (Pat `val_in_memory _ _ _ _`) store_slots_bytes_footprint >>
  disch_then (qspecl_then [`writes`, `cap`] mp_tac) >> simp[] >> strip_tac >>
  suspend "run"
QED

Resume store_slots_ptr_bytes_entry[run]:
  markerLib.RESUME_TAC >> (
  `val_store_size tv v = 32 * (word_size L + 1) /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     mem_word_at (w2n sw) m = n2w L)` by
    (gvs[] >> Cases_on `v` >>
     gvs[val_in_memory_def, val_store_size_def, vfmConstantsTheory.word_size_def,
       value_has_type_def] >>
     `cap < dimword (:256)` by
       (fs[type_memory_size_def, vfmConstantsTheory.word_size_def] >>
        qspec_then `cap + 31` mp_tac
          (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
        `((cap + 31) MOD 32) < 32` by simp[] >>
        simp[] >> intLib.ARITH_TAC) >>
     qmatch_asmsub_abbrev_tac `n <= cap` >>
     `n < dimword (:256)` by decide_tac >>
     gvs[Abbr `n`] >>
     gvs[wordsTheory.n2w_11, LESS_MOD] >> simp[LEFT_ADD_DISTRIB]) >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count (Var root) sa = (cnt,sm)` >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `?out. cnt = Var out /\ ci_mono sa sm /\ not_fresh_at sm out` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[compile_bytestring_word_count_def, comp_bind_def] >>
     pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >>
     imp_res_tac typed_copy_emit_op_mono >>
     qpat_assum `emit_op SHR _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[] >> simp[] >> conj_tac
     >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
     irule typed_copy_emit_op_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  rename1 `compile_word_copy_loop_op _ _ _ _ _ _ sm = (res,sb)` >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_word_copy_loop_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  suspend "count")
QED

Resume store_slots_ptr_bytes_entry[count]:
  markerLib.RESUME_TAC >> (gvs[] >>
  `32 <= 32 * (word_size L + 1)` by decide_tac >>
  drule_all store_slots_bytestring_count_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 g1 t1 (OK s1)` >>
  `lookup_var root s1 = SOME sw /\ eval_operand slot s1 = SOME dw /\
   op_taint t1 slot = {} /\ ~s1.vs_call_ctx.cc_static /\
   (!x. slot = Var x \/ Var out = Var x ==> not_fresh_at sm x)` by
    (Cases_on `slot` >> gvs[eval_operand_def, op_taint_def, execution_frame_def] >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh,
       venom_state_component_equality]) >>
  `eval_operand (Var out) s1 = SOME (n2w (word_size L + 1)) /\
   op_prov g1 (Var out) = NONE /\
   word_size L + 1 < dimword (:256) /\
   w2n sw + 32 * (word_size L + 1 - 1) < dimword (:256)` by
    (gvs[store_slots_bytestring_count_words, eval_operand_def, op_prov_def] >> decide_tac) >>
  `not_fresh_at sm root` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `32 * (word_size L + 1) <= 32 * (word_size L + 1)` by simp[] >>
  drule_all store_slots_word_copy_op_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  suspend "compose")
QED

Resume store_slots_ptr_bytes_entry[compose]:
  markerLib.RESUME_TAC >> (
  qexistsl_tac [`Gf`, `tf`, `u`, `GENLIST I (word_size L + 1)`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
     metis_tac[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_labels = s.vs_labels /\
   u.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `execution_frame s1 = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  simp[MEM_GENLIST] >> suspend "frame")
QED

Resume store_slots_ptr_bytes_entry[frame]:
  markerLib.RESUME_TAC >> (
  `store_copy_normalize s s1 = s /\ s1.vs_memory = s.vs_memory` by
    (qpat_x_assum `execution_frame s1 = _` mp_tac >>
     simp[execution_frame_def, store_copy_normalize_def,
       venom_state_component_equality]) >>
  qpat_x_assum `store_slots_ptr_frame _ _ _ _ _ _ _ _` mp_tac >>
  simp[store_slots_ptr_frame_def, store_slots_taint_def] >>
  strip_tac >> simp[] >>
  `store_copy_normalize s u = store_copy_normalize s (store_copy_normalize s1 u)` by
    simp[NoAsms, store_copy_normalize_def] >>
  pop_assum SUBST1_TAC >> asm_rewrite_tac[] >>
  `!a. mload a s1 = mload a s` by simp[mload_def] >>
  asm_rewrite_tac[] >>
  CONV_TAC (LHS_CONV (HO_REWR_CONV store_slots_normalize_fold)) >> simp[])
QED
Finalise store_slots_ptr_bytes_entry
