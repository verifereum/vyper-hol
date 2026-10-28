(* TOP-LEVEL: concrete bytestring field safety combines its source snapshot,
   counter, output geometry and preservation of all completed field bytes. *)
Theory abiBytesFieldPre
Ancestors
  abiFieldBytesPath abiFieldAddress abiFieldMemory abiFieldLayoutDefs abiMemoryFrame
  abiBytestringCorrect abiStaticLoopCode contractABI compileEnv venomState list pair words arithmetic

Definition abi_bytes_field_pre_def:
  abi_bytes_field_pre fields tail_offset (dst_addr:bytes32) (dyn_addr:bytes32) src_addr bs ss <=>
    bytestring_abi_pre (dst_addr + mload (w2n dyn_addr) ss) src_addr bs ss /\
    regions_disjoint (w2n (dst_addr + n2w (abi_field_head_size fields))) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss))
      (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
      (w2n (dst_addr + n2w (abi_field_head_size fields))) 32 /\
    regions_disjoint (w2n (dst_addr + mload (w2n dyn_addr) ss))
      (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) (w2n dyn_addr) 32 /\
    abi_fields_layout fields (w2n dst_addr) 0 tail_offset ss /\
    mload (w2n dyn_addr) ss = n2w (tail_offset + abi_field_tail_size fields) /\
    w2n dst_addr + abi_field_head_size fields < dimword(:256) /\
    w2n dst_addr + tail_offset + abi_field_tail_size fields < dimword(:256) /\
    EVERY (\(offset,byte_count).
      abi_window_separated (w2n dst_addr) (abi_field_head_size fields) offset byte_count /\
      abi_window_separated (w2n dst_addr + tail_offset) (abi_field_tail_size fields) offset byte_count)
      [(w2n (dst_addr + mload (w2n dyn_addr) ss), LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)));
       (w2n (dst_addr + n2w (abi_field_head_size fields)),32);(w2n dyn_addr,32)]
End

Theorem abi_bytes_field_pre_address:
  !fields tail_offset dst_addr dyn_addr src_addr bs cs source_offset root_addr ss.
    abi_bytes_field_pre fields tail_offset dst_addr dyn_addr src_addr bs
      (abi_field_address_state cs source_offset root_addr ss) =
    abi_bytes_field_pre fields tail_offset dst_addr dyn_addr src_addr bs ss
Proof
  simp[abi_bytes_field_pre_def, bytestring_abi_pre_def, abi_fields_layout_def,
    mload_def, read_memory_def, abi_field_address_state_frame]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed bytestring ABI field traversal precondition: " ^ name)
  end) (DB.thms "abiBytesFieldPre")
