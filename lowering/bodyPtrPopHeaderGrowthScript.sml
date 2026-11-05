Theory bodyPtrPopHeaderGrowth
Ancestors
  bodyPtrPopWriteCompatibility ptrDiscipline compileEnv vyperValue vfmState words pred_set

Theorem pop_empty_payload_taint_dead:
  lookup_storage 0w st = 0w ==>
  !k b. (k,b) IN {(1w:bytes32,0:num)} /\
        0 <= w2n k /\
        w2n k < 0 + type_slot_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) ==>
    dead_bytes st 0 (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (w2n k) b
Proof
  simp[dead_bytes_def, type_slot_size_def]
QED

Theorem pop_growth_exposes_retained_taint:
  ~(!k b. (k,b) IN key_update {(1w:bytes32,0:num)} 0w {} /\
          0 <= w2n k /\
          w2n k < 0 + type_slot_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) ==>
     dead_bytes (update_storage 0w 1w st) 0
       (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (w2n k) b)
Proof
  simp[key_update_def, dead_bytes_def, type_slot_size_def,
       lookup_storage_def, update_storage_def]
QED

Theorem pop_growth_after_payload_clear:
  !k b. (k,b) IN key_update (key_update {(1w:bytes32,0:num)} 1w {}) 0w {} /\
        0 <= w2n k /\
        w2n k < 0 + type_slot_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) ==>
    dead_bytes (update_storage 0w 1w st) 0
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (w2n k) b
Proof
  simp[key_update_def]
QED
