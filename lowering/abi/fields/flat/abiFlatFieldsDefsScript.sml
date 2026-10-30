(* TOP-LEVEL: concrete field observations for arbitrary static/bytes/string
   aggregate traversals. These describe actual compiler metadata and initial
   source reads; they contain no execution contracts or future-state premises. *)
Theory abiFlatFieldsDefs
Ancestors
  abiFieldLayoutDefs abiFieldMemory abiMemoryFrame abiBytestringCorrect abiEncoder
  contractABI compileEnv venomState list pair words arithmetic

Datatype:
  abi_flat_field = AbiFlatStatic abi_enc_info num (word8 list)
                 | AbiFlatBytes num num (word8 list)
End

Definition abi_flat_entry_def:
  abi_flat_entry (AbiFlatStatic info mem_size payload) = (info,LENGTH payload,mem_size,F) /\
  abi_flat_entry (AbiFlatBytes cap mem_size bs) = (AbiBytestring cap,32,mem_size,T)
End

Definition abi_flat_output_def:
  abi_flat_output (AbiFlatStatic info mem_size payload) = (F,payload) /\
  abi_flat_output (AbiFlatBytes cap mem_size bs) = (T,enc (Bytes NONE) (contractABI$BytesV bs))
End

Definition abi_flat_mem_size_def:
  abi_flat_mem_size (AbiFlatStatic info mem_size payload) = mem_size /\
  abi_flat_mem_size (AbiFlatBytes cap mem_size bs) = mem_size
End

Definition abi_flat_source_count_def:
  abi_flat_source_count (AbiFlatStatic info mem_size payload) = LENGTH payload /\
  abi_flat_source_count (AbiFlatBytes cap mem_size bs) = 32 + LENGTH bs
End

Definition abi_flat_valid_def:
  (abi_flat_valid (AbiFlatStatic info mem_size payload) <=>
    (info = AbiPrimWord /\ LENGTH payload = 32) \/ info = AbiCopy (LENGTH payload) \/
    (info = AbiComplex [] /\ LENGTH payload = 0)) /\
  (abi_flat_valid (AbiFlatBytes cap mem_size bs) <=> T)
End

Definition abi_flat_source_def:
  (abi_flat_source (AbiFlatStatic info mem_size payload) (src_addr:bytes32) tail_addr ss <=>
    read_memory (w2n src_addr) (LENGTH payload) ss = payload) /\
  (abi_flat_source (AbiFlatBytes cap mem_size bs) src_addr tail_addr ss <=>
    bytestring_abi_pre tail_addr src_addr bs ss)
End

Definition abi_flat_sources_def:
  (abi_flat_sources [] root_addr source_offset dst_addr tail_cursor writes ss <=> T) /\
  (abi_flat_sources (row::rest) root_addr source_offset dst_addr tail_cursor writes ss <=>
    abi_flat_source row (root_addr + n2w source_offset) (dst_addr + n2w tail_cursor) ss /\
    EVERY (\(offset,count). abi_window_separated (w2n (root_addr + n2w source_offset))
      (abi_flat_source_count row) offset count) writes /\
    abi_flat_sources rest root_addr (source_offset + abi_flat_mem_size row) dst_addr
      (tail_cursor + abi_field_tail_size [abi_flat_output row]) writes ss)
End

Definition abi_flat_geometry_def:
  abi_flat_geometry fields rows tail_offset (dst_addr:bytes32) (dyn_addr:bytes32) capacity <=>
    abi_field_head_size fields + abi_field_head_size (MAP abi_flat_output rows) <= tail_offset /\
    tail_offset + abi_field_tail_size fields + abi_field_tail_size (MAP abi_flat_output rows) <= capacity /\
    w2n dst_addr + capacity < dimword(:256) /\
    regions_disjoint (w2n dst_addr) capacity (w2n dyn_addr) 32
End

Definition abi_flat_state_def:
  abi_flat_state fields rows tail_offset dst_addr dyn_addr root_addr source_offset capacity ss <=>
    abi_flat_geometry fields rows tail_offset dst_addr dyn_addr capacity /\
    abi_fields_layout fields (w2n dst_addr) 0 tail_offset ss /\
    mload (w2n dyn_addr) ss = n2w (tail_offset + abi_field_tail_size fields) /\
    abi_flat_sources rows root_addr source_offset dst_addr (tail_offset + abi_field_tail_size fields)
      [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss
End
