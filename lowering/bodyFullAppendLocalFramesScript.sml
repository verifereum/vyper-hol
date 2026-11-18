(* Live encoded storage bytes of robust staged values are untainted. *)
Theory bodyFullAppendLocalFrames
Ancestors
  storageCopyLive representationCleanPtr valueEncodingProofs list arithmetic words

Theorem append_encoded_live_byte_clean:
  !tv v off mem M k writes st j b.
    well_formed_type_value tv /\ value_has_type tv v /\
    (!mem'. mem_agree_outside M mem mem' ==> val_in_memory tv v off mem') /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    j < type_slot_size tv /\ b < 32 /\ MEM j (MAP FST writes) /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b
    ==> off + 32*j + b NOTIN M
Proof
  rpt strip_tac >>
  `!mem'. mem_agree_outside M mem mem' ==>
     mem_bytes_at (off + 32*j + b) 1 mem' =
       [EL b (word_to_bytes
         (lookup_storage (n2w (w2n k+j)) (apply_writes k writes st)) T)]` by
    (rpt strip_tac >>
     `val_in_memory tv v off mem'` by metis_tac[] >>
     drule_all encode_value_memory_live >>
     pure_rewrite_tac[GSYM mem_bytes_at_word] >>
     simp[EL_mem_bytes_at] >> strip_tac >>
     irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >>
     rpt strip_tac >> gvs[EL_mem_bytes_at] >>
     qspecl_then [`b + (32*j + off)`, `1`, `mem'`, `0`] mp_tac
       EL_mem_bytes_at >> simp[]) >>
  drule robust_mem_bytes_at_clean >>
  disch_then (qspec_then `off + 32*j + b` mp_tac) >> simp[]
QED
