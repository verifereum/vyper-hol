(* Finite compatibility check, not a universal Pop invariant.
   compile_dynarray_pop_def stores new_len at base_op; context's
   compile_ptr_store_def uses MSTORE for LocMemory. *)
Theory bodyPtrSubscriptHistoryLayoutProbe
Ancestors
  bodyPtrSubscriptHistoryBoundary bodyPtrSubscriptPopAppendProbe
  valueEncoding valueEncodingDefs valueEncodingProps vyperValue loweringPosts arithmetic

Theorem shortened_history_layout:
  !b mem.
    mem_word_at b mem = 1w /\
    mem_word_at (b + 32) mem = 2w /\
    mem_word_at (b + 64) mem = 7w /\
    mem_word_at (b + 96) mem = 8w /\
    mem_word_at (b + 128) mem = 1w /\
    mem_word_at (b + 160) mem = 9w /\
    mem_word_at (b + 192) mem = 10w ==>
    val_in_memory
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2))
      (ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8])])) b mem /\
    val_in_memory (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
      (ArrayV (DynArrayV [IntV 9])) (b + 128) mem /\
    val_in_memory (BaseTV (UintT 256)) (IntV 10) (b + 192) mem
Proof
  simp[val_in_memory_def, type_memory_size_def, val_to_w256_def,
       ADD_ASSOC, integer_wordTheory.i2w_pos]
QED

Theorem historical_path_offsets:
  mem_path_offset
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2))
    [ValueSubscript (IntV 1)] =
    SOME (128, ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) /\
  mem_path_offset
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2))
    [ValueSubscript (IntV 1); ValueSubscript (IntV 1)] =
    SOME (192, BaseTV (UintT 256))
Proof
  simp[mem_path_offset_def, mem_step_offset_def, type_memory_size_def]
QED

Theorem first_pop_history_layout:
  !b mem.
    mem_word_at b mem = 1w /\
    mem_word_at (b + 32) mem = 2w /\
    mem_word_at (b + 64) mem = 7w /\
    mem_word_at (b + 96) mem = 8w /\
    mem_word_at (b + 128) mem = 2w /\
    mem_word_at (b + 160) mem = 9w /\
    mem_word_at (b + 192) mem = 10w ==>
    val_in_memory
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2))
      (ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8])])) b mem /\
    val_in_memory (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
      (ArrayV (DynArrayV [IntV 9; IntV 10])) (b + 128) mem
Proof
  simp[val_in_memory_def, type_memory_size_def, val_to_w256_def,
       ADD_ASSOC, integer_wordTheory.i2w_pos]
QED

Theorem pop_header_store_observations:
  !b s.
    mem_word_at (b + 32) s.vs_memory = 2w /\
    mem_word_at (b + 64) s.vs_memory = 7w /\
    mem_word_at (b + 96) s.vs_memory = 8w /\
    mem_word_at (b + 160) s.vs_memory = 9w /\
    mem_word_at (b + 192) s.vs_memory = 10w ==>
    mem_word_at b (mstore (b + 128) 1w (mstore b 1w s)).vs_memory = 1w /\
    mem_word_at (b + 32) (mstore (b + 128) 1w (mstore b 1w s)).vs_memory = 2w /\
    mem_word_at (b + 64) (mstore (b + 128) 1w (mstore b 1w s)).vs_memory = 7w /\
    mem_word_at (b + 96) (mstore (b + 128) 1w (mstore b 1w s)).vs_memory = 8w /\
    mem_word_at (b + 128) (mstore (b + 128) 1w (mstore b 1w s)).vs_memory = 1w /\
    mem_word_at (b + 160) (mstore (b + 128) 1w (mstore b 1w s)).vs_memory = 9w /\
    mem_word_at (b + 192) (mstore (b + 128) 1w (mstore b 1w s)).vs_memory = 10w
Proof
  simp[mstore_mem_word_at_same, mstore_mem_word_at_disjoint]
QED

Theorem first_pop_header_observations:
  !b s.
    mem_word_at (b + 32) s.vs_memory = 2w /\
    mem_word_at (b + 64) s.vs_memory = 7w /\
    mem_word_at (b + 96) s.vs_memory = 8w /\
    mem_word_at (b + 128) s.vs_memory = 2w /\
    mem_word_at (b + 160) s.vs_memory = 9w /\
    mem_word_at (b + 192) s.vs_memory = 10w ==>
    mem_word_at b (mstore b 1w s).vs_memory = 1w /\
    mem_word_at (b + 32) (mstore b 1w s).vs_memory = 2w /\
    mem_word_at (b + 64) (mstore b 1w s).vs_memory = 7w /\
    mem_word_at (b + 96) (mstore b 1w s).vs_memory = 8w /\
    mem_word_at (b + 128) (mstore b 1w s).vs_memory = 2w /\
    mem_word_at (b + 160) (mstore b 1w s).vs_memory = 9w /\
    mem_word_at (b + 192) (mstore b 1w s).vs_memory = 10w
Proof
  simp[mstore_mem_word_at_same, mstore_mem_word_at_disjoint]
QED

(* historical_row_pop_history supplies exactly the shortened owner [9]
   and child 10 at these offsets. The old [9,10] snapshot is incompatible
   with the decremented header; live elements, not whole reserved capacity,
   are constrained by elems_in_memory. These probes assert no reachability
   invariant for arbitrary histories or counted target callbacks. *)
Theorem historical_row_not_immutable:
  !b mem. mem_word_at (b + 128) mem = 1w ==>
    ~val_in_memory (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
      (ArrayV (DynArrayV [IntV 9; IntV 10])) (b + 128) mem
Proof
  simp[val_in_memory_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256]
QED
