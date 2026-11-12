Theory assignTupleStoreResourcesPtr
Ancestors
  bodyPtrIfExpLayout supportedTypes vyperTypeSystem bodyPtrDefs
  bodyPtrPopMemoryHeader typedCopyLayoutPtr valueEncodingProps
  representationCleanPtr exprSimTypedAlloc exprSimProps venomState
  loweringPosts valueEncoding valueEncodingDefs vyperTyping arithmetic
  tuplePlacePrefixCert loweringStateRelDefs

Theorem tuple_store_supported_array_layout:
  !tops et b dt.
    supported_value_type tops (ArrayT et b) /\
    arg_type_fits (ArrayT et b) dt ==>
    dt = ArrayT et b \/
    ?sc dc. b = Dynamic sc /\ dt = ArrayT et (Dynamic dc) /\
      sc <= dc /\ supported_word_type et
Proof
  rpt gen_tac >> strip_tac >> Cases_on `b` >> Cases_on `dt` >>
  gvs[supported_value_type_def, supported_scalar_type_def,
      supported_word_type_def, supported_string_type_def, arg_type_fits_def] >>
  Cases_on `b` >> gvs[arg_type_fits_def] >>
  drule_all ifexp_supported_word_fits_eq >> simp[]
QED

Theorem tuple_store_dynamic_source_resources:
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (ArrayV (DynArrayV vs)) op s /\
  ptr_val_ok cx ty (ArrayV (DynArrayV vs)) op G tn s /\
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV tv (Dynamic cap)) /\
  eval_operand op s = SOME a /\
  val_wf (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  type_memory_size tv = 32 ==>
  ?p. op = Var p /\ lookup_var p s = SOME a /\
    ptr_covers G tn p s (32+32*cap) /\
    ptr_covers G tn p s (32+32*LENGTH vs) /\
    LENGTH vs <= cap /\ LENGTH vs < dimword (:256) /\
    w2n a + 32+32*LENGTH vs < dimword (:256) /\
    mload (w2n a) s = n2w (LENGTH vs) /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `?p. op = Var p /\ ptr_covers G tn p s (32+32*cap)` by
    (irule ptr_val_ok_read_covers >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`cx`, `ArrayTV tv (Dynamic cap)`, `ty`, `ArrayV (DynArrayV vs)`] >>
     simp[val_footprint_def, type_memory_size_def]) >>
  `w2n a + (32+32*cap) < dimword (:256)` by
    (drule_all expr_val_at_bound >> simp[val_footprint_def, type_memory_size_def]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem` by
    metis_tac[ptr_val_ok_def, ptr_mem_ok_def] >>
  drule pop_robust_dynarray_header_clean >> strip_tac >>
  drule dynarray_in_memory_robust_length >>
  disch_then (qspec_then `s.vs_memory` mp_tac) >>
  simp[mem_agree_outside_def] >> strip_tac >>
  gvs[eval_operand_def, mload_def, mem_word_at_def, val_wf_def] >>
  gvs[ptr_covers_def] >> decide_tac
QED

Theorem tuple_store_bytes_source_capacity:
  !tv v cap len.
    (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
    value_has_type tv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) ==>
    len <= cap /\ 32+32*word_size len <= type_memory_size tv
Proof
  rpt strip_tac >>
  gvs[value_has_type_def, type_memory_size_def] >>
  drule exprSimHypsTheory.word_size_monotone >> decide_tac
QED

(* Caller support is on the destination local's declared type. *)
Theorem tuple_store_scalar_source_layout:
  !st dt. supported_scalar_type dt /\ arg_type_fits st dt ==>
    st = dt \/
    (?sc dc. st = BaseT (StringT sc) /\ dt = BaseT (StringT dc) /\ sc <= dc) \/
    (?sc dc. st = BaseT (BytesT (Dynamic sc)) /\
             dt = BaseT (BytesT (Dynamic dc)) /\ sc <= dc)
Proof
  Cases_on `st` >> Cases_on `dt` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def, arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT sb) (BaseT db)` >>
  Cases_on `sb` >> Cases_on `db` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def, arg_type_fits_def] >>
  rename1 `BytesT b` >> Cases_on `b` >> Cases_on `b'` >>
  simp[arg_type_fits_def]
QED

Theorem tuple_store_tuple_source_layout:
  !tops dts st.
    supported_value_type tops (TupleT dts) /\ arg_type_fits st (TupleT dts) ==>
    ?sts. st = TupleT sts /\ ~NULL dts /\ EVERY supported_scalar_type dts /\
      LIST_REL (\s d. s = d \/
        (?sc dc. s = BaseT (StringT sc) /\ d = BaseT (StringT dc) /\ sc <= dc) \/
        (?sc dc. s = BaseT (BytesT (Dynamic sc)) /\
                 d = BaseT (BytesT (Dynamic dc)) /\ sc <= dc)) sts dts
Proof
  rpt gen_tac >> Cases_on `st` >>
  simp[supported_value_tuple_depth, arg_type_fits_def] >> strip_tac >>
  qpat_x_assum `~NULL _` kall_tac >>
  rename1 `arg_types_fit sts dts` >>
  qpat_x_assum `arg_types_fit _ _` mp_tac >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  map_every qid_spec_tac [`dts`, `sts`] >>
  Induct >> gen_tac >> Cases_on `dts` >>
  simp[arg_type_fits_def] >> rpt strip_tac >>
  metis_tac[tuple_store_scalar_source_layout]
QED

(* The normalization allocation endpoint supplies both separation clauses.
   Apply this to each loaded member's subwindow of the saved tuple. *)
Theorem tuple_store_snapshot_scratch_separation:
  tuple_place_snapshot cenv cx es lo hi ats tys tvs w s /\
  ~EVERY is_word_type tys /\ type_memory_size_list tvs <> 0 /\ hi <= cut /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < cut ==>
    regions_disjoint scratch capacity b sz) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint scratch capacity b sz) /\
  w2n w <= a /\ a+n <= w2n w+type_memory_size_list tvs ==>
  regions_disjoint scratch capacity a n
Proof
  strip_tac >> gvs[tuple_place_snapshot_def] >>
  `regions_disjoint scratch capacity b sz` by metis_tac[LESS_LESS_EQ_TRANS] >>
  gvs[regions_disjoint_def] >> decide_tac
QED
