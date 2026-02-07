(*
 * Address Space Definitions (memory/storage/transient)
 *)

Theory addrSpace
Ancestors
  list
  venomInst

Datatype:
  addr_space = MEMORY | STORAGE | TRANSIENT
End

Definition addr_space_word_scale_def:
  addr_space_word_scale MEMORY = (32:num) /\
  addr_space_word_scale STORAGE = (1:num) /\
  addr_space_word_scale TRANSIENT = (1:num)
End

Definition addr_space_load_op_def:
  addr_space_load_op MEMORY = MLOAD /\
  addr_space_load_op STORAGE = SLOAD /\
  addr_space_load_op TRANSIENT = TLOAD
End

Definition addr_space_store_op_def:
  addr_space_store_op MEMORY = SOME MSTORE /\
  addr_space_store_op STORAGE = SOME SSTORE /\
  addr_space_store_op TRANSIENT = SOME TSTORE
End

val _ = export_theory();
