(* Byte-string encoder inputs observe only their count and active bytes.
   Unused semantic capacity need not be protected or copied. *)
Theory abiEncoderBytesActive
Ancestors
  abiEncoderInput abiEncoderInputFrame abiDecoderFrame abiDecoderContract
  valueEncoding valueEncodingProofs venomState contractABI words list arithmetic

Theorem abi_encoder_bytes_active:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap mem ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb (32+LENGTH bs) mem
Proof
  simp[abi_encoder_input_bytes_iff]
QED

Theorem abi_encoder_bytes_active_relocate:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap mem /\
  mem_bytes_at sb (32+LENGTH bs) mem = mem_bytes_at db (32+LENGTH bs) mem' /\
  32+LENGTH bs <= outcap ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) db outcap mem'
Proof
  strip_tac >> drule abi_encoder_bytes_active >> strip_tac >>
  drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`db`, `mem'`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  irule abi_encoder_input_capacity >> qexists_tac `32+LENGTH bs` >> simp[]
QED

Theorem abi_encoder_bytes_active_frame:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap s.vs_memory /\
  abi_decode_footprint_frame fp s t /\ abi_footprint_disjoint sb (32+LENGTH bs) fp ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap t.vs_memory
Proof
  strip_tac >>
  `32+LENGTH bs <= cap` by fs[abi_encoder_input_bytes_iff] >>
  `mem_bytes_at sb (32+LENGTH bs) s.vs_memory =
     mem_bytes_at sb (32+LENGTH bs) t.vs_memory` by
    (drule_all abi_decode_footprint_frame_slice >> simp[EQ_SYM_EQ]) >>
  drule_all abi_encoder_bytes_active_relocate >> simp[]
QED

Theorem abi_encoder_bytes_mcopy_prefix:
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap s.vs_memory /\
  32+LENGTH bs <= copied /\ 32+LENGTH bs <= outcap ==>
  abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) db outcap
    (mcopy db sb copied s).vs_memory
Proof
  strip_tac >>
  `mem_bytes_at sb (32+LENGTH bs) s.vs_memory =
     mem_bytes_at db (32+LENGTH bs) (mcopy db sb copied s).vs_memory` by
    (mp_tac (Q.INST [`sb` |-> `sb`, `db` |-> `db`, `cap` |-> `copied`,
      `mem` |-> `s.vs_memory`, `mem'` |-> `(mcopy db sb copied s).vs_memory`,
      `off` |-> `0`, `len` |-> `32+LENGTH (bs:word8 list)`] abi_encoder_window_slice) >>
     simp[mcopy_mem_bytes_at_same]) >>
  drule_all abi_encoder_bytes_active_relocate >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_BYTES_ACTIVE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder active byte prefix not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderBytesActive");
