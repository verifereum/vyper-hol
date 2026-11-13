Theory calldataExactBulkPack
Ancestors
  calldataExactStatic calldataReconstruction abiEncoderInputFrame
  vyperCalldata vyperCalldataProps vyperValue valueEncodingTyping valueEncodingDefs
  valueEncoding words list arithmetic

Theorem calldata_exact_bulk_pack:
  (!pos d mem. mem_bytes_at d (type_memory_size etv) mem =
    mem_bytes_at pos (type_memory_size etv) cd ==>
    ?x. cd_decode T cd etv pos = SOME x /\ value_has_type etv x /\
      val_wf etv x /\ val_in_memory etv x d mem) /\
  ~tv_abi_dynamic etv /\ ~tv_needs_clamp etv /\
  tv_abi_size etv = type_memory_size etv /\
  n = w2n (cd_word cd pos) /\ n <= maxn /\
  mem_word_at d mem = n2w n /\
  mem_bytes_at (d+32) (n*type_memory_size etv) mem =
    mem_bytes_at (cd_at F pos 32) (n*type_memory_size etv) cd ==>
  ?x. cd_decode F cd (ArrayTV etv (Dynamic maxn)) pos = SOME x /\
    value_has_type (ArrayTV etv (Dynamic maxn)) x /\
    val_wf (ArrayTV etv (Dynamic maxn)) x /\
    val_in_memory (ArrayTV etv (Dynamic maxn)) x d mem
Proof
  strip_tac >>
  `?vs. cd_decode_elems T cd etv (cd_at F pos 32) 0 n = SOME vs /\
    LENGTH vs = n /\ EVERY (value_has_type etv) vs /\
    elems_in_memory vs (d+32) etv mem` by
    (irule calldata_exact_static_elems >> simp[] >> rpt strip_tac >>
     `mem_bytes_at (d+32+j*type_memory_size etv) (type_memory_size etv) mem =
      mem_bytes_at (cd_at F pos 32+j*type_memory_size etv)
        (type_memory_size etv) cd` by
       (drule abi_encoder_window_slice >>
        disch_then (qspecl_then [`j*type_memory_size etv`,`type_memory_size etv`] mp_tac) >>
        impl_tac
        >- (irule LESS_EQ_TRANS >> qexists_tac `(j+1)*type_memory_size etv` >>
            simp[RIGHT_ADD_DISTRIB] >> irule LESS_MONO_MULT >> decide_tac) >>
        metis_tac[]) >>
     first_x_assum drule >> simp[] >> metis_tac[]) >>
  `value_has_type (ArrayTV etv (Dynamic maxn))
      (ArrayV (make_array_value etv (Dynamic maxn) vs)) /\
   val_wf (ArrayTV etv (Dynamic maxn))
      (ArrayV (make_array_value etv (Dynamic maxn) vs)) /\
   val_in_memory (ArrayTV etv (Dynamic maxn))
      (ArrayV (make_array_value etv (Dynamic maxn) vs)) d mem` by
    (irule calldata_dynamic_values_typed_memory >> simp[]) >>
  qexists_tac `ArrayV (make_array_value etv (Dynamic maxn) vs)` >>
  gvs[] >> simp[cd_decode_def, make_array_value_def]
QED
