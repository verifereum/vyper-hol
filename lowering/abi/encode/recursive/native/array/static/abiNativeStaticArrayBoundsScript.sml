(* TOP-LEVEL: raw static-array metadata and native root resources bound
   live source and packed output elements at their respective strides. *)
Theory abiNativeStaticArrayBounds
Ancestors
  abiNativeArrayBounds abiNativeStaticArraySource abiNativeEncodingDefs abiMemoryEncoding abiFieldLayoutDefs
  valueEncoding compileEnv venomState list words arithmetic

Theorem abi_native_static_array_extents:
  !func cs after source_id target_id root_addr source_capacity dst_addr info width stride fields mem ss.
    32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F))
      (w2n root_addr + 32) (source_capacity - 32) mem fields /\
    abi_native_memory_ready func cs after source_id target_id (root_addr:bytes32) source_capacity (dst_addr:bytes32)
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss ==>
    32 + LENGTH fields * stride <= source_capacity /\
    LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
      abi_field_bytes (abi_field_head_size fields) fields) = 32 + LENGTH fields * width /\
    w2n root_addr + 32 + LENGTH fields * stride < dimword (:256) /\
    w2n dst_addr + 32 + LENGTH fields * width < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >> drule abi_memory_fields_source_size >> simp[] >> DISCH_TAC >>
  drule abi_native_static_array_shape >> disch_then (qspec_then `abi_field_head_size fields` strip_assume_tac) >>
  drule abi_native_memory_bounds >> strip_tac >>
  `LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
    abi_field_bytes (abi_field_head_size fields) fields) = 32 + LENGTH fields * width` by simp[] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem abi_native_static_array_element_bounds:
  !func cs after source_id target_id root_addr source_capacity dst_addr info width stride fields mem ss index.
    32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F))
      (w2n root_addr + 32) (source_capacity - 32) mem fields /\
    abi_native_memory_ready func cs after source_id target_id (root_addr:bytes32) source_capacity (dst_addr:bytes32)
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    index < LENGTH fields ==>
    width < dimword (:256) /\
    w2n (root_addr + 32w + n2w index * n2w stride) = w2n root_addr + 32 + index * stride /\
    w2n (dst_addr + 32w + n2w index * n2w width) = w2n dst_addr + 32 + index * width /\
    w2n root_addr <= w2n (root_addr + 32w + n2w index * n2w stride) /\
    w2n (root_addr + 32w + n2w index * n2w stride) + stride <= w2n root_addr + source_capacity /\
    w2n dst_addr <= w2n (dst_addr + 32w + n2w index * n2w width) /\
    w2n (dst_addr + 32w + n2w index * n2w width) + width <=
      w2n dst_addr + LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_static_array_extents >> strip_tac >>
  qspecl_then [`root_addr`, `index`, `LENGTH fields`, `stride`] mp_tac abi_native_array_index_bounds >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`dst_addr`, `index`, `LENGTH fields`, `width`] mp_tac abi_native_array_index_bounds >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `1 * width <= LENGTH fields * width` by
    (simp_tac bool_ss [LE_MULT_RCANCEL] >> decide_tac) >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed raw static array source/output bounds: " ^ name)
  end) (DB.thms "abiNativeStaticArrayBounds")
