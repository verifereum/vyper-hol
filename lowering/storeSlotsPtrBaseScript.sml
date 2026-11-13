(* Constructor assembly for sparse pointer-safe storage stores. *)
Theory storeSlotsPtrBase
Ancestors storeSlotsPtrInterface vyperValue stmtSimStoreCopy bodyMemAssignTopCopyFacts
  storeSlotsPtrReadResources storeSlotsPtrSingle storeSlotsPtrWordCopy
  storeSlotsPtrBytesCount placeStoreSlots assignBasePtrStorageExtent
  abiTypeBoundProps typedMemoryCopy vyperStorageCoverage vyperEncodeDecode
  exprSimProps loweringPosts context compileEnv loweringStateRelDefs
  bodyPtrDefs ptrDiscipline fragGasPathPtr emitHelper emitHelperProps venomState
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
