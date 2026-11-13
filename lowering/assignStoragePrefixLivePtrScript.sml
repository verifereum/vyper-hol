(* Only the live prefix of a dynamic array is copied to storage. *)
Theory assignStoragePrefixLivePtr
Ancestors
  assignBasePtrStorageSemantic assignBasePtrStorageLoop storageCopyLive
  valueEncodingProps valueEncodingDefs loweringStateRelDefs venomState
  words arithmetic

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
