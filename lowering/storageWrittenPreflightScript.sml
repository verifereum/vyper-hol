Theory storageWrittenPreflight
Ancestors
  valueEncodingProps list rich_list arithmetic words byte vfmTypes vfmState
  valueEncodingProofs compileEnv valueEncoding accountsRelProps exprSimAttributeFields
  vyperStorageLayoutSafety vyperStorageFrame vyperEncodeDecode vyperTyping
  vyperStorage vyperValue storageDecodeMemory

(* Parse and typecheck the obligations without asserting either proposition. *)
val _ = ``!tv v off mem k writes st j b.
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    j < type_slot_size tv /\ b < 32 /\
    MEM j (MAP FST writes) /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k + j) b ==>
    EL b (word_to_bytes
            (lookup_storage (n2w (w2n k + j)) (apply_writes k writes st)) T) =
    EL b (word_to_bytes (mem_word_at (off + 32 * j) mem) T)``;

val _ = ``!cx tr mid n subs k tv v writes off mem ws st1 st2.
    declared_storage_region cx mid n subs = SOME (tr, k, tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (k, tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\
    encode_value tv v = SOME writes /\
    (!i b. i < type_slot_size tv /\ b < 32 /\
       ~dead_bytes (apply_writes k writes st1) (w2n k) tv (w2n k + i) b ==>
       MEM i (MAP FST writes)) /\
    (!i. i < type_slot_size tv /\
         (?b. b < 32 /\
              ~dead_bytes (apply_writes k writes st1) (w2n k) tv (w2n k + i) b) ==>
         ws i = mem_word_at (off + 32 * i) mem) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes k writes st1))
      (apply_writes k writes st1)
      (FOLDL (\t i. update_storage (k + n2w i) (ws i) t)
             st2 (COUNT_LIST (type_slot_size tv)))``;
