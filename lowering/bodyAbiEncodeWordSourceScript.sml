(* Canonical static ABI representative for a typed word source. *)
Theory bodyAbiEncodeWordSource
Ancestors
  abiEncoderStaticRepresentative entryDecodeProps exprBopSimProps
  loweringPosts vyperABI vyperTyping contractABI valueEncoding words venomState

Theorem abi_encode_word_source_rep:
  expr_val_rel cx ty v op s /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av ==>
  ?w at rv. eval_operand op s = SOME w /\ has_type at rv /\
    ~is_dynamic at /\ static_length at = 32 /\
    word_to_bytes w T = enc at rv /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) ty) av
Proof
  strip_tac >> drule_all expr_val_rel_typed >> strip_tac >>
  drule_all vyper_to_abi_word_enc >> strip_tac >>
  `LENGTH (word_to_bytes (typed_val_to_w256 tv v) T) = 32` by simp[] >>
  drule abi_encoder_bytes32_representative >> strip_tac >>
  qexistsl [`typed_val_to_w256 tv v`, `Bytes (SOME 32)`,
    `contractABI$BytesV (word_to_bytes (typed_val_to_w256 tv v) T)`] >> simp[]
QED
