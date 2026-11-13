(* Bytestring stores may leave destination capacity beyond the source buffer. *)
Theory assignStorageBytesPrefixPtr
Ancestors
  assignStoragePrefixLivePtr assignBasePtrStorageTaint accountsRelProps
  valueEncoding valueEncodingDefs vyperValue vyperTyping
  loweringStateRelDefs words arithmetic

Theorem assign_store_bytes_live_prefix:
  (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
  mem_word_at off mem = n2w len /\ len < dimword (:256) /\
  0 < copied /\ len <= 32*(copied-1) /\
  w2n k+type_slot_size tv <= dimword (:256) ==>
  !i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
    i < w2n k+copied
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_slot_size tv = 1+word_size cap` by
    (Cases_on `tv = BaseTV (BytesT (Dynamic cap))` >>
     gvs[type_slot_size_def]) >>
  `lookup_storage k (apply_writes k writes st) = mem_word_at off mem` by
    (mp_tac (Q.SPECL [`tv`,`v`,`off`,`mem`,`k`,`writes`,`st`]
       assign_store_encoding_first_word) >> simp[]) >>
  `w2n (lookup_storage k (apply_writes k writes st)) = len` by
    simp[w2n_n2w,LESS_MOD] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i < w2n k+copied` >- simp[] >>
  `w2n k < i /\ i <= w2n k+word_size cap /\
   len <= 32*(i-(w2n k+1))+c` by (fs[] >> decide_tac) >>
  `dead_bytes (apply_writes k writes st) (w2n k) tv i c` suffices_by simp[] >>
  irule bytestring_storage_tail_dead >>
  simp[] >> qexists_tac `cap` >> simp[]
QED

Theorem assign_store_bytes_retained_tail_dead:
  (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
  lookup_storage (n2w start) final = n2w len /\ len < dimword (:256) /\
  0 < copied /\ len <= 32*(copied-1) /\
  (!q c. (q,c) IN old ==> storage_dead cx tr initial (w2n q) c) ==>
  !q c. (q,c) IN old /\ start+copied <= w2n q /\
    w2n q < start+type_slot_size tv ==>
    dead_bytes final start tv (w2n q) c
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `type_slot_size tv = 1+word_size cap` by
    (Cases_on `tv = BaseTV (BytesT (Dynamic cap))` >>
     gvs[type_slot_size_def]) >>
  `storage_dead cx tr initial (w2n q) c` by metis_tac[] >>
  `c<32` by
    (qpat_x_assum `storage_dead cx tr initial (w2n q) c`
       (strip_assume_tac o PURE_REWRITE_RULE [storage_dead_def]) >>
     drule (cj 1 dead_bytes_range) >> simp[]) >>
  `start < w2n q /\ w2n q <= start+word_size cap /\
   len <= 32*(w2n q-(start+1))+c` by (fs[] >> decide_tac) >>
  irule bytestring_storage_tail_dead >> simp[w2n_n2w,LESS_MOD] >>
  qexists_tac `cap` >> simp[]
QED
