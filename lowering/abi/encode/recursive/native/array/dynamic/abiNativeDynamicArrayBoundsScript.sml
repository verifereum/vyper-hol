(* TOP-LEVEL: live dynamic-array children stay within the owned source and
   packed output arenas. Head and tail addresses do not wrap, even when
   source strides and encoded child sizes differ. *)
Theory abiNativeDynamicArrayBounds
Ancestors
  abiNativeDynamicArraySource abiNativeDynamicArrayState abiNativeArrayBounds abiNativeEncodingDefs
  abiMemoryEncoding abiFieldLayoutDefs abiFieldBytesPath compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_extents:
  !func cs after source_id target_id root_addr source_capacity dst_addr info width stride fields mem initial.
    abi_native_memory_ready func cs after source_id target_id (root_addr:bytes32) source_capacity ((dst_addr:bytes32) + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\ 32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T))
      (w2n root_addr + 32) (source_capacity - 32) mem fields /\
    w2n (dst_addr + 32w) = w2n dst_addr + 32 ==>
    abi_field_head_size fields = LENGTH fields * width /\ 32 + LENGTH fields * stride <= source_capacity /\
    w2n root_addr + 32 + LENGTH fields * stride < dimword (:256) /\
    w2n dst_addr + 32 + LENGTH fields * width < dimword (:256) /\
    w2n (dst_addr + 32w) + abi_field_head_size fields + abi_field_tail_size fields < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >> drule abi_memory_fields_source_size >> simp[] >> DISCH_TAC >>
  drule abi_native_dynamic_array_shape >> strip_tac >> drule abi_native_memory_bounds >> strip_tac >>
  `w2n (dst_addr + 32w) + abi_field_head_size fields + abi_field_tail_size fields < dimword (:256)` by
    fs[abi_field_bytes_length] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem abi_native_dynamic_array_element_bounds:
  !func cs after source_id target_id root_addr source_capacity dst_addr info width stride fields mem initial index.
    abi_native_memory_ready func cs after source_id target_id (root_addr:bytes32) source_capacity ((dst_addr:bytes32) + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\ 32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T))
      (w2n root_addr + 32) (source_capacity - 32) mem fields /\
    w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields ==>
    width = 32 /\
    w2n (root_addr + 32w + n2w index * n2w stride) = w2n root_addr + 32 + index * stride /\
    32 + index * stride + stride <= source_capacity /\
    w2n (dst_addr + 32w + n2w index * n2w width) = w2n (dst_addr + 32w) + index * width /\
    index * width + 32 <= abi_field_head_size fields /\
    abi_field_head_size (TAKE index fields) = index * width
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_extents >> strip_tac >>
  drule_all abi_native_dynamic_array_take_step >> strip_tac >>
  qspecl_then [`root_addr`, `index`, `LENGTH fields`, `stride`] mp_tac abi_native_array_index_bounds >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`dst_addr`, `index`, `LENGTH fields`, `width`] mp_tac abi_native_array_index_bounds >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_native_dynamic_array_shape >> disch_then (CONJUNCTS_THEN2 ASSUME_TAC (qspec_then `index` ASSUME_TAC)) >>
  `MIN index (LENGTH fields) = index` by (simp[MIN_DEF] >> decide_tac) >>
  `32 + index * stride + stride <= source_capacity` by
    (irule LESS_EQ_TRANS >> qexists_tac `32 + LENGTH fields * stride` >> conj_tac
     >- (qpat_assum `w2n root_addr + 32 + index * stride + stride <= _` mp_tac >>
         simp_tac arith_ss [GSYM ADD_ASSOC]) >> first_assum MATCH_ACCEPT_TAC) >>
  `index * width + 32 <= abi_field_head_size fields` by
    (qpat_assum `w2n dst_addr + 32 + index * width + width <= _` mp_tac >>
     asm_simp_tac arith_ss [GSYM ADD_ASSOC]) >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, asm_simp_tac bool_ss [] >> decide_tac]
QED

Theorem abi_native_dynamic_array_tail_bounds:
  !func cs after source_id target_id root_addr source_capacity dst_addr info width stride fields initial ss index counter_addr dyn_addr.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields ==>
    mload (w2n dyn_addr) ss = n2w (abi_field_head_size fields + abi_field_tail_size (TAKE index fields)) /\
    w2n (dst_addr + 32w + mload (w2n dyn_addr) ss) =
      w2n (dst_addr + 32w) + abi_field_head_size fields + abi_field_tail_size (TAKE index fields) /\
    w2n (dst_addr + 32w) <= w2n (dst_addr + 32w + mload (w2n dyn_addr) ss) /\
    w2n (dst_addr + 32w + mload (w2n dyn_addr) ss) + LENGTH (SND (EL index fields)) <=
      w2n (dst_addr + 32w) + LENGTH (abi_field_bytes (abi_field_head_size fields) fields)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_data_def]) >>
  drule_all abi_native_dynamic_array_extents >> strip_tac >>
  drule_all abi_native_dynamic_array_ranges >> strip_tac >>
  `abi_field_tail_size (TAKE index fields) <= abi_field_tail_size fields` by decide_tac >>
  `w2n (dst_addr + 32w) + (abi_field_head_size fields + abi_field_tail_size (TAKE index fields)) < dimword (:256)` by decide_tac >>
  qspecl_then [`dst_addr + 32w`, `abi_field_head_size fields + abi_field_tail_size (TAKE index fields)`]
    mp_tac abi_field_word_address >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  `w2n (dst_addr + 32w + mload (w2n dyn_addr) ss) =
    w2n (dst_addr + 32w) + abi_field_head_size fields + abi_field_tail_size (TAKE index fields)` by
    (qpat_assum `mload (w2n dyn_addr) ss = _` (fn th => PURE_REWRITE_TAC [th]) >>
     PURE_REWRITE_TAC [GSYM ADD_ASSOC] >> first_assum MATCH_ACCEPT_TAC) >>
  PURE_REWRITE_TAC [abi_field_bytes_length] >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    qpat_assum `w2n (dst_addr + 32w + mload (w2n dyn_addr) ss) = _` (fn th => PURE_REWRITE_TAC [th]) >>
    qpat_assum `abi_field_tail_size (TAKE index fields) + LENGTH (SND (EL index fields)) <= _` mp_tac >>
    simp_tac arith_ss [GSYM ADD_ASSOC]]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-child array source and output bounds: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayBounds")
