(* Scratch-aware observational frames; no decoder execution assumption. *)
Theory abiDecoderFrame
Ancestors
  abiDecoderContract valueEncodingProps valueEncoding venomState words list arithmetic

Definition abi_footprint_disjoint_def:
  abi_footprint_disjoint p n (fp : (num # num) list) <=>
    !d sz. MEM (d,sz) fp ==> p + n <= d \/ d + sz <= p
End

Definition abi_decode_footprint_frame_def:
  abi_decode_footprint_frame fp before after <=>
    (!p n. abi_footprint_disjoint p n fp ==>
      mem_bytes_at p n after.vs_memory = mem_bytes_at p n before.vs_memory) /\
    after.vs_call_ctx = before.vs_call_ctx /\
    after.vs_data_section = before.vs_data_section
End

Theorem abi_decode_footprint_frame_refl:
  abi_decode_footprint_frame fp s s
Proof
  simp[abi_decode_footprint_frame_def]
QED

Theorem abi_decode_footprint_frame_trans:
  abi_decode_footprint_frame fp s t /\
  abi_decode_footprint_frame fp t u ==>
  abi_decode_footprint_frame fp s u
Proof
  simp[abi_decode_footprint_frame_def] >> metis_tac[]
QED

(* Larger intervals, as well as additional scratch intervals, are allowed. *)
Theorem abi_decode_footprint_frame_weaken:
  abi_decode_footprint_frame small s t /\
  (!d sz. MEM (d,sz) small ==>
    ?b len. MEM (b,len) big /\ b <= d /\ d + sz <= b + len) ==>
  abi_decode_footprint_frame big s t
Proof
  rw[abi_decode_footprint_frame_def] >>
  first_x_assum irule >>
  gvs[abi_footprint_disjoint_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem abi_decode_footprint_frame_write:
  MEM (b,len) fp /\ b <= dst /\ dst + LENGTH bs <= b + len ==>
  abi_decode_footprint_frame fp s (write_memory_with_expansion dst bs s)
Proof
  strip_tac >> simp[abi_decode_footprint_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      irule write_memory_mem_bytes_at_disjoint >>
      gvs[abi_footprint_disjoint_def] >>
      first_x_assum drule >> decide_tac) >>
  simp[write_memory_with_expansion_def]
QED

Theorem abi_decode_footprint_frame_slice:
  abi_decode_footprint_frame fp s t /\ abi_footprint_disjoint p n fp ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  simp[abi_decode_footprint_frame_def]
QED

Theorem abi_decode_footprint_frame_mload:
  abi_decode_footprint_frame fp s t /\ abi_footprint_disjoint p 32 fp ==>
  mload p t = mload p s
Proof
  strip_tac >> drule_all abi_decode_footprint_frame_slice >>
  simp[mem_bytes_at_def, mload_def]
QED

Theorem abi_decode_footprint_frame_immutable_load:
  abi_decode_footprint_frame fp s t /\
  (opc = CALLDATALOAD \/ opc = DLOAD) ==>
  abi_decode_load opc p t = abi_decode_load opc p s
Proof
  rw[abi_decode_footprint_frame_def, abi_decode_load_def,
     abi_decode_source_def]
QED

Theorem abi_decode_loop_increment_word:
  (i:num) < ncount /\ ncount < dimword(:256) ==>
  (n2w i : bytes32) + 1w = n2w (SUC i) /\
  SUC i <= ncount /\ w2n (n2w i : bytes32) = i /\
  w2n (n2w (SUC i) : bytes32) = SUC i
Proof
  strip_tac >> simp[GSYM word_add_n2w, ADD1] >>
  simp[w2n_n2w] >> decide_tac
QED

(* The child footprint excludes both protected slots. An outer index write
   has a different footprint: it need only exclude the count slot. *)
Theorem abi_decode_child_preserves_loop_slots:
  abi_decode_footprint_frame fp s t /\
  abi_footprint_disjoint count_slot 32 fp /\
  abi_footprint_disjoint index_slot 32 fp ==>
  mload count_slot t = mload count_slot s /\
  mload index_slot t = mload index_slot s
Proof
  metis_tac[abi_decode_footprint_frame_mload]
QED

Theorem abi_decode_index_write_preserves_count:
  count_slot + 32 <= index_slot \/ index_slot + LENGTH bs <= count_slot ==>
  mload count_slot (write_memory_with_expansion index_slot bs s) =
  mload count_slot s
Proof
  strip_tac >> irule abi_decode_footprint_frame_mload >>
  qexists_tac `[(index_slot,LENGTH bs)]` >>
  simp[abi_footprint_disjoint_def] >>
  irule abi_decode_footprint_frame_write >> simp[]
QED

Theorem abi_footprint_disjoint_append:
  abi_footprint_disjoint p n (output ++ scratch) <=>
  abi_footprint_disjoint p n output /\ abi_footprint_disjoint p n scratch
Proof
  simp[abi_footprint_disjoint_def, MEM_APPEND] >> metis_tac[]
QED
