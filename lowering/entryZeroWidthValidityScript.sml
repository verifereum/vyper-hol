(* Public decoder validity retains a cardinality guard absent from its worker. *)
Theory entryZeroWidthValidity
Ancestors
  abiDecoderValidContract entryZeroWidthCodec vyperABI contractABI
  words list rich_list arithmetic

Theorem entry_zero_width_tuple_worker:
  !n bs hds. vyper_decode_valid_enc_tuple (REPLICATE n (Tuple [])) bs hds
Proof
  Induct >> simp[REPLICATE, vyper_decode_valid_enc_def,
    is_dynamic_def, static_length_def]
QED

Theorem entry_zero_width_tuple_validity:
  !n bs. vyper_decode_valid_enc (Tuple (REPLICATE n (Tuple []))) bs <=>
    n < dimword (:256)
Proof
  simp[Once vyper_decode_valid_enc_def, entry_zero_width_tuple_worker]
QED

Theorem entry_zero_width_valid_pre_exclusion:
  vyper_to_abi_type env ty = Tuple (REPLICATE n (Tuple [])) /\
  dimword (:256) <= n ==>
  ~abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d b cap s
Proof
  strip_tac >> simp[abi_decoder_valid_pre_def, entry_zero_width_tuple_validity]
QED

Theorem entry_zero_width_validity_counterinstance[local]:
  ~vyper_decode_valid_enc
    (Tuple (REPLICATE (dimword (:256)) (Tuple []))) []
Proof
  simp[entry_zero_width_tuple_validity]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "zero width validity inherited admission"
  end)
  [entry_zero_width_tuple_worker, entry_zero_width_tuple_validity,
   entry_zero_width_valid_pre_exclusion, entry_zero_width_validity_counterinstance];
