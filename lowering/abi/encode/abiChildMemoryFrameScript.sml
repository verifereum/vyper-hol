(* TOP-LEVEL: actual dynamic-child memory frames cover the encoded payload,
   head word and counter word. Prefix register writes preserve every read. *)
Theory abiChildMemoryFrame
Ancestors
  loweringStateRelDefs abiMemoryFrame abiChildPrefix abiChildSuffix abiChildFrames abiBytestringMemory
  contractABI memoryReadProps compileEnv venomState list pair words arithmetic

Theorem abi_child_prefix_read_memory:
  !var_base head_offset dst_addr dyn_addr ss offset read_len index.
    read_memory offset read_len
      ((abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) with vs_inst_idx := index) =
    read_memory offset read_len ss
Proof
  simp[read_memory_def, abi_child_prefix_frame]
QED

Theorem abi_bytestring_read_memory_frame:
  !dst_addr bs before after.
    (!offset read_len.
      offset + read_len <= w2n (dst_addr:bytes32) \/
      w2n dst_addr + contractABI$ceil32 (LENGTH (bs:word8 list)) + 32 <= offset ==>
      read_memory offset read_len (after:venom_state) = read_memory offset read_len before) ==>
    abi_memory_frame [(w2n dst_addr,LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))] before after
Proof
  rpt gen_tac >> DISCH_TAC >>
  PURE_REWRITE_TAC [bytestring_encoded_size] >>
  simp_tac (srw_ss()) [abi_memory_frame_def, abi_window_separated_def,
    bytestring_encoded_size, regions_disjoint_def] >> rpt gen_tac >> strip_tac
  >- simp[read_memory_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem abi_child_bytes_read_memory_frame:
  !dst_addr bs var_base head_offset parent_addr dyn_addr ss index after.
    (!offset read_len.
      offset + read_len <= w2n (dst_addr:bytes32) \/
      w2n dst_addr + contractABI$ceil32 (LENGTH (bs:word8 list)) + 32 <= offset ==>
      read_memory offset read_len (after:venom_state) =
      read_memory offset read_len
        ((abi_child_prefix_state var_base head_offset parent_addr dyn_addr ss) with vs_inst_idx := index)) ==>
    abi_memory_frame [(w2n dst_addr,LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))] ss after
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [abi_child_prefix_read_memory] >>
  MATCH_ACCEPT_TAC abi_bytestring_read_memory_frame
QED

Theorem abi_child_suffix_written_frame:
  !var_base head_addr dyn_addr tail_offset child_len ss.
    abi_memory_frame [(w2n head_addr,32);(w2n dyn_addr,32)] ss
      (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_memory_frame_def] >>
  rpt gen_tac >> DISCH_TAC >> Cases_on `read_len = 0`
  >- simp[read_memory_def] >>
  irule abi_child_suffix_read_frame >> fs[abi_window_separated_def, regions_disjoint_def]
QED
