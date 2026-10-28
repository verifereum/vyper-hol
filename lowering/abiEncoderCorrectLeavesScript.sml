(* Concrete encoder leaves satisfy the recursive containing-function contract. *)
Theory abiEncoderCorrectLeaves
Ancestors
  abiEncoderSharedLeaves abiEncoderEnvelopeAdapter
  abiEncoderCorrect abiEncoderSequence abiEncoderLeafCode abiEncoderAdmissible
  abiEncoderReentryLeaves abiEncoderBytes abiEncoderBytesCode abiEncoderInput abiDecoderEffect
  abiDecoderAllocation abiDecoderLoop abiDecoderReentry abiDecoderContract abiEncoder compileEnv
  emitHelper valueEncoding contractABI venomState venomExecSemantics emitHelperProps words list
  rich_list arithmetic

Theorem abi_encoder_correct_word:
  abi_encoder_correct AbiPrimWord
Proof
  irule abi_encoder_shared_correct >> irule abi_encoder_shared_word
QED

Theorem abi_encoder_correct_copy:
  abi_encoder_correct (AbiCopy sz)
Proof
  irule abi_encoder_shared_correct >> irule abi_encoder_shared_copy
QED

Theorem abi_encoder_correct_bytes:
  abi_encoder_correct (AbiBytestring maxlen)
Proof
  irule abi_encoder_shared_correct >> irule abi_encoder_shared_bytes
QED

Theorem abi_encoder_empty_input:
  abi_encoder_input (AbiComplex []) at av sb source_cap mem ==>
  av = ListV [] /\ enc at av = []
Proof
  gvs[abi_encoder_complex_input_iff, abi_encoder_tuple_type_def, abi_encoder_member_span_def,
    enc_def, LET_THM] >> strip_tac >> gvs[enc_def, LET_THM, REV_DEF]
QED

Theorem abi_encoder_correct_empty:
  abi_encoder_correct (AbiComplex [])
Proof
  irule abi_encoder_shared_correct >> irule abi_encoder_shared_empty
QED
