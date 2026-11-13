(* Only the live prefix of a dynamic array is copied to storage. *)
Theory assignStoragePrefixLivePtr
Ancestors
  assignBasePtrStorageSemantic assignBasePtrStorageLoop storageCopyLive
  valueEncodingProps valueEncodingDefs loweringStateRelDefs venomState
  storageDynPrefixLive accountsRelProps valueEncoding vyperTyping vyperValue
  words arithmetic list byte vfmTypes

Theorem assign_base_store_frame_live_prefix:
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 copied s tn /\ copied <= type_slot_size tv /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n b) s0.vs_memory /\
  encode_value tv v = SOME writes /\
  w2n k+type_slot_size tv <= dimword (:256) /\
  w2n b+32*(copied-1) < dimword (:256) /\
  w2n k <= x /\ x < w2n k+copied /\ c < 32 /\
  ~dead_bytes (apply_writes k writes st) (w2n k) tv x c ==>
  EL c (word_to_bytes
    (lookup_storage (n2w x) (if tr then contract_transient s else contract_storage s)) T) =
  EL c (word_to_bytes (lookup_storage (n2w x) (apply_writes k writes st)) T)
Proof
  strip_tac >>
  `x < dimword (:256) /\ x-w2n k < copied /\
   x-w2n k < type_slot_size tv /\ w2n k+(x-w2n k) = x /\
   w2n k+copied <= dimword (:256) /\
   x < w2n k+type_slot_size tv` by decide_tac >>
  drule_all assign_base_store_frame_lookup >>
  disch_then (qspec_then `n2w x` mp_tac) >>
  simp[w2n_n2w, LESS_MOD] >> disch_then SUBST1_TAC >>
  `mload (w2n (b+n2w (x-w2n k)*32w)) s0 =
   mem_word_at (w2n b+32*(x-w2n k)) s0.vs_memory` by
    (irule assign_base_store_source_word >> qexists_tac `copied` >> simp[]) >>
  simp[] >> metis_tac[encode_value_memory_live]
QED

Theorem assign_store_encoding_first_word:
  !tv v off mem k writes st.
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
    w2n k+type_slot_size tv <= dimword (:256) /\ 0 < type_slot_size tv ==>
    lookup_storage k (apply_writes k writes st) = mem_word_at off mem
Proof
  rpt gen_tac >> strip_tac >>
  `!c. c < 32 ==>
    EL c (word_to_bytes (lookup_storage k (apply_writes k writes st)) T) =
    EL c (word_to_bytes (mem_word_at off mem) T)` by
    (rpt gen_tac >> strip_tac >>
     `~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k) c` by
       (strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]) >>
     mp_tac (Q.SPECL [`tv`,`v`,`off`,`mem`,`k`,`writes`,`st`,`0`,`c`]
       encode_value_memory_live) >> simp[]) >>
  `word_to_bytes (lookup_storage k (apply_writes k writes st)) T =
    word_to_bytes (mem_word_at off mem) T` by
    (irule LIST_EQ >> simp[]) >>
  pop_assum (mp_tac o AP_TERM ``word_of_bytes T (0w:bytes32)``) >> simp[]
QED

Theorem assign_store_dynarray_live_prefix:
  well_formed_type_value (ArrayTV et (Dynamic cap)) /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem /\
  encode_value (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
  w2n k+type_slot_size (ArrayTV et (Dynamic cap)) <= dimword (:256) ==>
  !i c. w2n k <= i /\ i < w2n k+type_slot_size (ArrayTV et (Dynamic cap)) /\ c<32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) (ArrayTV et (Dynamic cap)) i c ==>
    i < w2n k+1+LENGTH vs*type_slot_size et
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `lookup_storage k (apply_writes k writes st) = mem_word_at off mem` by
    (mp_tac (Q.SPECL [`ArrayTV et (Dynamic cap)`,`ArrayV (DynArrayV vs)`,
       `off`,`mem`,`k`,`writes`,`st`] assign_store_encoding_first_word) >>
     simp[type_slot_size_def]) >>
  `mem_word_at off mem = n2w (LENGTH vs)` by fs[val_in_memory_def] >>
  `LENGTH vs < dimword (:256)` by
    (fs[value_has_type_def,well_formed_type_value_def] >> decide_tac) >>
  `i < w2n (k:bytes32)+1+cap*type_slot_size et` by
    (qpat_assum `i < w2n k+type_slot_size (ArrayTV et (Dynamic cap))`
       (mp_tac o PURE_REWRITE_RULE [type_slot_size_def]) >> decide_tac) >>
  mp_tac (Q.SPECL [`apply_writes k writes st`,`w2n (k:bytes32)`,`et`,`cap`,`i`,`c`]
    dynarray_live_prefix) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[w2n_n2w,LESS_MOD]
QED
