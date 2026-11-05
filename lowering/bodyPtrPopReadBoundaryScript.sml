Theory bodyPtrPopReadBoundary
Ancestors
  vyperState vyperStorageBackend vyperLookupStorage vyperStorage
  vyperValue vfmState words finite_map integer_word

(* The real storage Pop branch checks positivity, not the declared
   capacity.  These are source-operation probes, not target counterexamples. *)
Theorem pop_overcapacity_slots_probe:
  ~slots_in_range ((0w:bytes32 =+ 2w:bytes32) (K 0w)) 0
    (ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
Proof
  EVAL_TAC >> simp[dimword_def, SF wordsLib.SIZES_ss]
QED

Theorem pop_overcapacity_source_probe:
  !cx es. ~cx.txn.is_static ==>
    pop_place cx (StoragePlace F 0w
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))
      (set_storage cx es F ((0w =+ 2w) (K 0w))) =
    (INL (PlaceR (StoragePlace F 2w (BaseTV (UintT 256)))),
     set_storage cx (set_storage cx es F ((0w =+ 2w) (K 0w))) F
       (apply_writes 0w [(0,1w)] ((0w =+ 2w) (K 0w))))
Proof
  rpt strip_tac >>
  simp[pop_place_def, get_storage_backend_eq, get_storage_after_set,
       bind_def, ignore_bind_def, check_def, assert_def, return_def,
       lookup_storage_def, type_slot_size_def, write_storage_slot_def,
       check_not_static_def, encode_value_def, set_storage_backend_eq,
       encode_base_to_slot_def, lift_option_type_def, dimword_def, i2w_def,
       SF wordsLib.SIZES_ss]
QED

Theorem pop_singleton_source_probe:
  !cx es. ~cx.txn.is_static ==>
    pop_place cx (StoragePlace F 0w
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))
      (set_storage cx es F ((0w =+ 1w) (K 0w))) =
    (INL (PlaceR (StoragePlace F 1w (BaseTV (UintT 256)))),
     set_storage cx (set_storage cx es F ((0w =+ 1w) (K 0w))) F
       (apply_writes 0w [(0,0w)] ((0w =+ 1w) (K 0w))))
Proof
  rpt strip_tac >>
  simp[pop_place_def, get_storage_backend_eq, get_storage_after_set,
       bind_def, ignore_bind_def, check_def, assert_def, return_def,
       lookup_storage_def, type_slot_size_def, write_storage_slot_def,
       check_not_static_def, encode_value_def, set_storage_backend_eq,
       encode_base_to_slot_def, lift_option_type_def, dimword_def, i2w_def,
       SF wordsLib.SIZES_ss]
QED
