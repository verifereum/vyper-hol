(* Composition and source transport for the decoder's byte-observation frames. *)
Theory abiDecoderFrameCompose
Ancestors
  abiDecoderFrame abiDecoderContract valueEncodingProps valueEncoding
  venomState list arithmetic

Theorem abi_decode_frame_footprint:
  abi_decode_frame d sz s t <=>
  abi_decode_footprint_frame [(d,sz)] s t
Proof
  simp[abi_decode_frame_def, abi_decode_footprint_frame_def,
       abi_footprint_disjoint_def]
QED

Theorem abi_decode_frame_widen:
  abi_decode_frame d sz s t /\ b <= d /\ d + sz <= b + cap ==>
  abi_decode_frame b cap s t
Proof
  rw[abi_decode_frame_def] >> first_x_assum irule >> decide_tac
QED

Theorem abi_decode_frame_trans:
  abi_decode_frame d sz s t /\ abi_decode_frame d sz t u ==>
  abi_decode_frame d sz s u
Proof
  simp[abi_decode_frame_footprint] >>
  metis_tac[abi_decode_footprint_frame_trans]
QED

Theorem abi_decode_frame_adjacent:
  abi_decode_frame d n s t /\ abi_decode_frame (d + n) sz t u ==>
  abi_decode_frame d (n + sz) s u
Proof
  strip_tac >> irule abi_decode_frame_trans >> qexists_tac `t` >>
  conj_tac >> irule abi_decode_frame_widen
  >- (qexistsl_tac [`d`, `n`] >> simp[]) >>
  qexistsl_tac [`d + n`, `sz`] >> simp[]
QED

Theorem abi_decode_frame_mem_word:
  abi_decode_frame d sz s t /\ (p + 32 <= d \/ d + sz <= p) ==>
  mem_word_at p t.vs_memory = mem_word_at p s.vs_memory
Proof
  simp[abi_decode_frame_footprint, mem_word_at_eq_mload] >> strip_tac >>
  irule abi_decode_footprint_frame_mload >>
  qexists_tac `[(d,sz)]` >> simp[abi_footprint_disjoint_def]
QED

Theorem abi_decode_frame_source_window:
  abi_decode_frame d sz s t /\ abi_decode_source_opcode opc /\
  (opc = MLOAD ==> p + n <= d \/ d + sz <= p) ==>
  mem_bytes_at p n (abi_decode_source opc t) =
  mem_bytes_at p n (abi_decode_source opc s)
Proof
  rw[abi_decode_source_opcode_def, abi_decode_source_def,
     abi_decode_frame_def] >> first_x_assum irule >> simp[]
QED
