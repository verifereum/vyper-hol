(* TOP-LEVEL: whole aggregate output ownership entails each field's actual
   smaller head/tail geometry and covers its writes by two fixed arenas. *)
Theory abiFlatGeometry
Ancestors
  loweringStateRelDefs abiFlatFieldsDefs abiStaticFieldStep abiBytesFieldReady abiFieldBytesPath
  abiFieldMemory abiFieldLayoutDefs abiMemoryFrame abiMemoryFrameCover
  compileEnv venomState list pair words arithmetic

Theorem abi_flat_static_pre:
  !fields rest info mem_size payload tail_offset dst_addr dyn_addr capacity (src_addr:bytes32) ss.
    abi_flat_geometry fields (AbiFlatStatic info mem_size payload::rest)
      tail_offset dst_addr dyn_addr capacity /\
    read_memory (w2n src_addr) (LENGTH payload) ss = payload /\
    abi_fields_layout fields (w2n dst_addr) 0 tail_offset ss ==>
    abi_static_field_pre fields tail_offset dst_addr dyn_addr src_addr payload ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_flat_geometry _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_flat_geometry_def, abi_flat_output_def, abi_field_head_size_def,
    abi_field_tail_def] >> strip_tac >>
  `w2n dst_addr + abi_field_head_size fields < dimword(:256)` by decide_tac >>
  `w2n (dst_addr + n2w (abi_field_head_size fields)) = w2n dst_addr + abi_field_head_size fields` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  fs[abi_static_field_pre_def, abi_window_separated_def, regions_disjoint_def] >> decide_tac
QED

Theorem abi_flat_bytes_geometry:
  !fields rest cap mem_size bs tail_offset dst_addr dyn_addr capacity.
    abi_flat_geometry fields (AbiFlatBytes cap mem_size bs::rest)
      tail_offset dst_addr dyn_addr capacity ==>
    abi_bytes_field_geometry fields tail_offset dst_addr dyn_addr bs
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_flat_geometry_def, abi_flat_output_def,
    abi_field_head_size_def, abi_field_tail_def] >> strip_tac >>
  `w2n dst_addr + abi_field_head_size fields < dimword(:256)` by decide_tac >>
  `w2n dst_addr + (tail_offset + abi_field_tail_size fields) < dimword(:256)` by decide_tac >>
  `w2n (dst_addr + n2w (abi_field_head_size fields)) = w2n dst_addr + abi_field_head_size fields` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  `w2n (dst_addr + n2w (tail_offset + abi_field_tail_size fields)) =
      w2n dst_addr + (tail_offset + abi_field_tail_size fields)` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  fs[abi_bytes_field_geometry_def, LET_THM, abi_window_separated_def, regions_disjoint_def] >> decide_tac
QED

Theorem abi_writes_cover_window:
  !arena capacity cell offset count.
    arena <= offset /\ offset + count <= arena + capacity ==>
    abi_writes_cover [(arena,capacity);(cell,32)] [(offset,count)]
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [abi_writes_cover_def] >>
  qexistsl_tac [`arena`, `capacity`] >> simp[]
QED

Theorem abi_flat_static_cover:
  !fields rest info mem_size payload tail_offset dst_addr dyn_addr capacity.
    abi_flat_geometry fields (AbiFlatStatic info mem_size payload::rest)
      tail_offset dst_addr dyn_addr capacity ==>
    abi_writes_cover [(w2n dst_addr,capacity);(w2n dyn_addr,32)]
      [(w2n (dst_addr + n2w (abi_field_head_size fields)),LENGTH payload)]
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_flat_geometry_def, abi_flat_output_def,
    abi_field_head_size_def, abi_field_tail_def] >> strip_tac >>
  `w2n dst_addr + abi_field_head_size fields < dimword(:256)` by decide_tac >>
  `w2n (dst_addr + n2w (abi_field_head_size fields)) = w2n dst_addr + abi_field_head_size fields` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  irule abi_writes_cover_window >> simp[] >> decide_tac
QED

Theorem abi_flat_bytes_cover:
  !fields rest cap mem_size bs tail_offset dst_addr dyn_addr capacity.
    abi_flat_geometry fields (AbiFlatBytes cap mem_size bs::rest)
      tail_offset dst_addr dyn_addr capacity ==>
    abi_writes_cover [(w2n dst_addr,capacity);(w2n dyn_addr,32)]
      [(w2n (dst_addr + n2w (tail_offset + abi_field_tail_size fields)),
          LENGTH (contractABI$enc (Bytes NONE) (contractABI$BytesV bs)));
       (w2n (dst_addr + n2w (abi_field_head_size fields)),32);(w2n dyn_addr,32)]
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_flat_geometry_def, abi_flat_output_def,
    abi_field_head_size_def, abi_field_tail_def] >> strip_tac >>
  `w2n dst_addr + abi_field_head_size fields < dimword(:256)` by decide_tac >>
  `w2n dst_addr + (tail_offset + abi_field_tail_size fields) < dimword(:256)` by decide_tac >>
  `w2n (dst_addr + n2w (abi_field_head_size fields)) = w2n dst_addr + abi_field_head_size fields` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  `w2n (dst_addr + n2w (tail_offset + abi_field_tail_size fields)) =
      w2n dst_addr + (tail_offset + abi_field_tail_size fields)` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  simp_tac (srw_ss()) [abi_writes_cover_def] >> rpt gen_tac >> strip_tac >>
  FIRST [qexistsl_tac [`w2n dst_addr`, `capacity`] >> gvs[] >> decide_tac,
    qexistsl_tac [`w2n dyn_addr`, `32`] >> gvs[]]
QED

Theorem abi_flat_geometry_advance:
  !fields row rest tail_offset dst_addr dyn_addr capacity.
    abi_flat_geometry fields (row::rest) tail_offset dst_addr dyn_addr capacity ==>
    abi_flat_geometry (fields ++ [abi_flat_output row]) rest tail_offset dst_addr dyn_addr capacity
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_flat_geometry_def, abi_field_head_size_append,
    abi_field_tail_size_append, abi_field_head_size_def] >>
  Cases_on `abi_flat_output row` >> simp[abi_field_head_size_def, abi_field_tail_def] >> decide_tac
QED
