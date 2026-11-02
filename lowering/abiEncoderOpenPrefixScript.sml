(* Prefix arithmetic independent of ABI value typedness. *)
Theory abiEncoderOpenPrefix
Ancestors abiEncoderMembersDefs abiEncoderTuple abiCanonicalWindows valueEncoding contractABI list arithmetic

Theorem abi_encoder_open_prefix_tail_advance:
  LENGTH pre = LENGTH pvs ==>
  LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) =
  LENGTH (FLAT (abi_tuple_tails pre pvs)) +
    (if is_dynamic ty then LENGTH (enc ty av) else 0)
Proof
  strip_tac >> simp[abi_tuple_tails_append, abi_tuple_tails_def, FLAT_APPEND] >>
  Cases_on `is_dynamic ty` >> simp[]
QED

Theorem abi_encoder_open_prefix_head_advance:
  SUM (MAP abi_member_head_size (pre++[ty])) =
  SUM (MAP abi_member_head_size pre) + abi_member_head_size ty
Proof
  simp[MAP_APPEND, SUM_APPEND]
QED
