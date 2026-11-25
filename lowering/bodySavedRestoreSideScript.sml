Theory bodySavedRestoreSide
Ancestors
  bodyFullExtCallDirectMaterialize

(* The side post and all semantic posts refer to one selected state and
   ghost pair.  Its suppliers are the three physical-copy replay laws. *)
Theorem abi_encode_saved_restore_row_from_side:
  ^(concl abi_encode_saved_restore_row_side_core)
Proof
  ACCEPT_TAC abi_encode_saved_restore_row_side_core
QED
