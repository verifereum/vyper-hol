(* Concrete leaves project the single shared execution endpoint. *)
Theory abiScratchEncoderLeaves
Ancestors
  abiEncoderSharedLeaves abiEncoderSharedContract abiScratchEncoderContract

Theorem abi_scratch_encoder_word:
  abi_scratch_encoder AbiPrimWord
Proof
  irule abi_encoder_shared_scratch >> irule abi_encoder_shared_word
QED

Theorem abi_scratch_encoder_copy:
  abi_scratch_encoder (AbiCopy sz)
Proof
  irule abi_encoder_shared_scratch >> irule abi_encoder_shared_copy
QED

Theorem abi_scratch_encoder_bytes:
  abi_scratch_encoder (AbiBytestring maxlen)
Proof
  irule abi_encoder_shared_scratch >> irule abi_encoder_shared_bytes
QED

Theorem abi_scratch_encoder_empty:
  abi_scratch_encoder (AbiComplex [])
Proof
  irule abi_encoder_shared_scratch >> irule abi_encoder_shared_empty
QED
