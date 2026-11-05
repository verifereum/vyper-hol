(* Transport the exact bytes encoder writes through read-only phases. *)
Theory bodyPtrAbiEncodeBytesMemory
Ancestors
  bodyPtrAbiEncodeCursorFrame abiEncoderMemory abiEncoderBytes abiEncoderRounding
  venomExecSemantics venomState ptrDiscipline words arithmetic

Theorem abi_encode_read_frame_bytes_write:
  abi_encode_read_frame st s G tn t H un ==>
  abi_encode_read_frame st
    (mcopy db sb n (mstore lp 0w s)) G
    (tn with t_mem := tn.t_mem DIFF pad DIFF copied)
    (mcopy db sb n (mstore lp 0w t)) H
    (un with t_mem := un.t_mem DIFF pad DIFF copied)
Proof
  simp_tac (srw_ss()) [abi_encode_read_frame_def] >> strip_tac >>
  simp_tac (srw_ss()) [mcopy_def, mstore_def, LET_THM,
    write_memory_with_expansion_def, lookup_var_def, op_taint_def] >>
  fs[lookup_var_def, op_taint_def]
QED

Theorem abi_encode_bytes_memory_result:
  abi_encode_read_frame st
    (mcopy db sb (32+LENGTH bs)
      (mstore (db+contractABI$ceil32 (LENGTH bs)) 0w s)) G tn t H un /\
  abi_encoder_input (AbiBytestring maxlen) at (contractABI$BytesV bs) sb cap s.vs_memory /\
  (sb+(32+LENGTH bs) <= db \/ db+(32+contractABI$ceil32 (LENGTH bs)) <= sb) ==>
  mem_bytes_at db (LENGTH (enc at (contractABI$BytesV bs))) t.vs_memory =
    enc at (contractABI$BytesV bs) /\
  abi_decode_frame db (32+contractABI$ceil32 (LENGTH bs)) s t
Proof
  strip_tac >>
  drule abi_encoder_bytes_input_memory >>
  disch_then (qspec_then `db` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs)` by simp[abi_encoder_ceil32_bounds] >>
  drule abi_encoder_bytes_write_frame >> disch_then (qspecl_then [`sb`, `s`, `db`] assume_tac) >>
  fs[abi_encode_read_frame_def] >>
  irule abi_encoder_frame_memory >> metis_tac[]
QED

Theorem abi_encode_bytes_write_frame_then:
  abi_encode_read_frame st s G tn t H un /\
  abi_encode_read_frame mid (mcopy db sb n (mstore lp 0w t)) H
    (un with t_mem := un.t_mem DIFF pad DIFF copied) u J vn /\
  st.cs_next_var <= mid.cs_next_var ==>
  abi_encode_read_frame st (mcopy db sb n (mstore lp 0w s)) G
    (tn with t_mem := tn.t_mem DIFF pad DIFF copied) u J vn
Proof
  metis_tac[abi_encode_read_frame_bytes_write, abi_encode_read_frame_then]
QED
