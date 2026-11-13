(* TOP-LEVEL: prepare a dynamic field after preceding fields have executed.
   The byte source is observed only in the original state; an actual memory
   frame transports it. Output geometry is independent of execution. *)
Theory abiBytesFieldReady
Ancestors
  abiBytesFieldPre abiComplexMemory abiFieldMemory abiFieldLayoutDefs abiMemoryFrame
  abiBytestringCorrect contractABI compileEnv venomState list pair words arithmetic

Definition abi_bytes_field_geometry_def:
  abi_bytes_field_geometry fields tail_offset (dst_addr:bytes32) (dyn_addr:bytes32) bs <=>
    let tail_addr = dst_addr + n2w (tail_offset + abi_field_tail_size fields) in
    regions_disjoint (w2n (dst_addr + n2w (abi_field_head_size fields))) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n tail_addr) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
      (w2n (dst_addr + n2w (abi_field_head_size fields))) 32 /\
    regions_disjoint (w2n tail_addr) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) (w2n dyn_addr) 32 /\
    w2n dst_addr + abi_field_head_size fields < dimword(:256) /\
    w2n dst_addr + tail_offset + abi_field_tail_size fields < dimword(:256) /\
    EVERY (\(offset,byte_count).
      abi_window_separated (w2n dst_addr) (abi_field_head_size fields) offset byte_count /\
      abi_window_separated (w2n dst_addr + tail_offset) (abi_field_tail_size fields) offset byte_count)
      [(w2n tail_addr,LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
       (w2n (dst_addr + n2w (abi_field_head_size fields)),32);(w2n dyn_addr,32)]
End

Theorem abi_bytes_field_ready:
  !fields tail_offset dst_addr dyn_addr src_addr bs ss.
    abi_bytes_field_geometry fields tail_offset dst_addr dyn_addr bs /\
    bytestring_abi_pre (dst_addr + n2w (tail_offset + abi_field_tail_size fields)) src_addr bs ss /\
    abi_fields_layout fields (w2n dst_addr) 0 tail_offset ss /\
    mload (w2n dyn_addr) ss = n2w (tail_offset + abi_field_tail_size fields) ==>
    abi_bytes_field_pre fields tail_offset dst_addr dyn_addr src_addr bs ss
Proof
  simp_tac bool_ss [abi_bytes_field_geometry_def, LET_THM, abi_bytes_field_pre_def] >>
  rpt strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_bytes_field_ready_frame:
  !fields tail_offset dst_addr dyn_addr src_addr bs writes before after.
    abi_bytes_field_geometry fields tail_offset dst_addr dyn_addr bs /\
    bytestring_abi_pre (dst_addr + n2w (tail_offset + abi_field_tail_size fields)) src_addr bs before /\
    abi_memory_frame writes before after /\
    EVERY (\(offset,byte_count).
      abi_window_separated (w2n src_addr) (32 + LENGTH bs) offset byte_count) writes /\
    abi_fields_layout fields (w2n dst_addr) 0 tail_offset after /\
    mload (w2n dyn_addr) after = n2w (tail_offset + abi_field_tail_size fields) ==>
    abi_bytes_field_pre fields tail_offset dst_addr dyn_addr src_addr bs after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`writes`, `before`, `after`, `w2n (src_addr:bytes32)`, `32 + LENGTH (bs:word8 list)`]
    abi_memory_frame_read) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst_addr + n2w (tail_offset + abi_field_tail_size fields)`, `src_addr`, `bs`, `before`, `after`]
    bytestring_abi_pre_read_frame) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  irule abi_bytes_field_ready >> asm_simp_tac bool_ss []
QED
