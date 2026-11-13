(* Storage copy metadata from the physical bytestring buffer. *)
Theory assignTupleBytesStorageResourcesPtr
Ancestors
  assignTuplePtrLocalCompat assignTuplePtrBytesResources exprSimBufferStore bodyPtrDefs
  exprSimProps valueTypingMemoryProps valueEncodingProps vyperTypeArgFits
  vyperTyping vyperTypeSystem compileEnv exprLowering valueEncoding valueEncodingDefs vyperValue loweringPosts words arithmetic vfmConstants
  bytestringCopyExecution vyperEncodeDecode vyperStorage

Theorem bytestring_fit_slot_bounds_ptr:
  is_bytestring_type sty /\ is_bytestring_type dty /\ arg_type_fits sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv ==>
  0 < type_slot_size stv /\ type_slot_size stv <= type_slot_size dtv
Proof
  Cases_on `sty` >> Cases_on `dty` >> gvs[is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT sb) (BaseT db)` >>
  Cases_on `sb` >> Cases_on `db` >>
  gvs[is_bytestring_type_def,arg_type_fits_def,evaluate_type_def]
  >- (strip_tac >> gvs[type_slot_size_def,word_size_def] >>
      irule DIV_LE_MONOTONE >> decide_tac) >>
  rename1 `arg_type_fits (BaseT (BytesT ss)) (BaseT (BytesT ds))` >>
  Cases_on `ss` >> Cases_on `ds` >>
  gvs[is_bytestring_type_def,arg_type_fits_def,evaluate_type_def] >>
  strip_tac >> gvs[type_slot_size_def,word_size_def] >>
  irule DIV_LE_MONOTONE >> decide_tac
QED

Theorem bytestring_live_count_bounds_ptr:
  0 < n /\ len <= 32*(n-1) /\ 32*n < dimword (:256) ==>
  (len+63) DIV 32 = 1 + word_size len /\
  0 < (len+63) DIV 32 /\ 32*((len+63) DIV 32) <= 32*n /\
  (len+63) DIV 32 < dimword (:256) /\ len+63 < dimword (:256)
Proof
  strip_tac >>
  `(len+63) DIV 32 = 1 + word_size len` by
    (mp_tac (Q.SPECL [`len+31`,`32`]
       (MATCH_MP ADD_DIV_RWT (DECIDE ``0 < 32``))) >>
     simp[word_size_def] >> decide_tac) >>
  `32*(1 + word_size len) <= 32*n` by
    (`(len+31) DIV 32 < n` by
       (simp[DIV_LT_X] >> decide_tac) >>
     fs[word_size_def] >> decide_tac) >>
  `len+63 < dimword (:256)` by
    (irule bytestring_word_count_no_wrap >> decide_tac) >>
  gvs[] >> decide_tac
QED

Theorem bytestring_live_storage_shape_ptr:
  ((?bs. dtv = BaseTV (BytesT (Dynamic cap)) /\ v = BytesV bs /\ len = LENGTH bs) \/
   (?str. dtv = BaseTV (StringT cap) /\ v = StringV str /\ len = LENGTH str)) /\
  (!mem. mem_agree_outside tm s.vs_memory mem ==>
    val_in_memory dtv v a mem) ==>
  (!mem. mem_agree_outside tm s.vs_memory mem ==>
    mload a (s with vs_memory := mem) = n2w len) /\
  (!writes. encode_value dtv v = SOME writes ==>
    !j. MEM j (MAP FST writes) <=> j < (len+63) DIV 32)
Proof
  strip_tac >>
  `(len+63) DIV 32 = 1 + word_size len` by
    (mp_tac (Q.SPECL [`len+31`,`32`]
       (MATCH_MP ADD_DIV_RWT (DECIDE ``0 < 32``))) >>
     simp[word_size_def] >> decide_tac) >>
  gvs[] >> rpt conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`cap`,`bs`,`a`,`s with vs_memory := mem`] buffer_bytes_header) >>
      simp[] >> metis_tac[])
  >- (simp[encode_value_def] >> gen_tac >> strip_tac >>
      drule (ONCE_REWRITE_RULE [ADD_COMM] encode_dyn_bytes_slots_keys) >>
      disch_then ACCEPT_TAC)
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`cap`,`str`,`a`,`s with vs_memory := mem`] buffer_string_header) >>
      simp[] >> metis_tac[]) >>
  simp[encode_value_def] >> gen_tac >> strip_tac >>
  drule (ONCE_REWRITE_RULE [ADD_COMM] encode_dyn_bytes_slots_keys) >>
  disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.LENGTH_MAP])
QED

Theorem bytestring_storage_resources_ptr:
  is_bytestring_type sty /\ is_bytestring_type dty /\ arg_type_fits sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  w2n a + type_memory_size stv < dimword (:256) /\
  (!mem. mem_agree_outside tm s.vs_memory mem ==>
    val_in_memory stv v (w2n a) mem) ==>
  ?n len cap.
    n = type_slot_size stv /\ type_memory_size stv = 32*n /\
    0 < n /\ n < dimword (:256) /\ n <= type_slot_size dtv /\
    ((?bs. dtv = BaseTV (BytesT (Dynamic cap)) /\ v = BytesV bs /\ len = LENGTH bs) \/
     (?str. dtv = BaseTV (StringT cap) /\ v = StringV str /\ len = LENGTH str)) /\
    len <= cap /\ mload (w2n a) s = n2w len /\
    len <= 32*(n-1) /\ len < dimword (:256) /\
    (!mem. mem_agree_outside tm s.vs_memory mem ==>
      val_in_memory dtv v (w2n a) mem) /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tm)
Proof
  strip_tac >>
  `0 < type_slot_size stv /\ type_slot_size stv <= type_slot_size dtv` by
    metis_tac[bytestring_fit_slot_bounds_ptr] >>
  `type_memory_size stv = 32*type_slot_size stv` by
    simp[type_memory_size_slots] >>
  `!mem. mem_agree_outside tm s.vs_memory mem ==>
    val_in_memory dtv v (w2n a) mem` by
    metis_tac[bytestring_robust_representation_compat_ptr] >>
  `val_in_memory dtv v (w2n a) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tm` by
    metis_tac[robust_bytestring_header_clean_ptr] >>
  `val_footprint stv v <= type_memory_size stv` by
    metis_tac[value_has_type_memory_wf,val_footprint_le] >>
  `(?cap. stv = BaseTV (StringT cap)) \/
   (?cap. stv = BaseTV (BytesT (Dynamic cap)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  `(?cap. dtv = BaseTV (StringT cap)) \/
   (?cap. dtv = BaseTV (BytesT (Dynamic cap)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  `?payload_len payload_cap.
    ((?bs. dtv = BaseTV (BytesT (Dynamic payload_cap)) /\ v = BytesV bs /\ payload_len = LENGTH bs) \/
     (?str. dtv = BaseTV (StringT payload_cap) /\ v = StringV str /\ payload_len = LENGTH str)) /\
    payload_len <= payload_cap /\ 32+payload_len <= type_memory_size stv /\
    mload (w2n a) s = n2w payload_len` by
    (Cases_on `v` >> gvs[value_has_type_def,val_footprint_def] >>
     metis_tac[buffer_bytes_header,buffer_string_header]) >>
  qexistsl_tac [`type_slot_size stv`,`payload_len`,`payload_cap`] >>
  gvs[] >> rpt conj_tac >> decide_tac
QED
