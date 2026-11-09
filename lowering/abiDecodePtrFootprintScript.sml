Theory abiDecodePtrFootprint
Ancestors
  abiEncoder venomState contractABI words arithmetic

Definition abi_decode_runtime_footprint_def:
  abi_decode_runtime_footprint ei p s =
    case ei of
      DecPrimWord w => 32
    | DecBytestring n => 32+contractABI$ceil32 (w2n (mload p s))
    | _ => 0
End

Theorem abi_decode_runtime_footprint_word[simp]:
  abi_decode_runtime_footprint (DecPrimWord w) p s = 32
Proof
  simp[abi_decode_runtime_footprint_def]
QED

Theorem abi_decode_runtime_footprint_bytes[simp]:
  abi_decode_runtime_footprint (DecBytestring n) p s =
    32+contractABI$ceil32 (w2n (mload p s))
Proof
  simp[abi_decode_runtime_footprint_def]
QED
