(* TOP-LEVEL: the actual recursive-copy loop states preserve external and
   allocation state. These rewrite rules compose with arbitrary child copies. *)
Theory typedCopyLoopStateFrame
Ancestors
  typedCopyStateFrame typedArrayLoopHeader typedArrayLoopAddress typedArrayLoopCounter
  dynCopyPrefixExec venomState words

Theorem typed_array_loop_header_state_frame[simp]:
  !var_base counter_word len_word before after.
    copy_state_frame before (typed_array_loop_header_state var_base counter_word len_word after) <=>
    copy_state_frame before after
Proof
  simp[typed_array_loop_header_state_def, LET_THM]
QED

Theorem typed_array_loop_address_state_frame[simp]:
  !var_base counter_word dst_addr src_addr dst_size src_size before after.
    copy_state_frame before
      (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size after) <=>
    copy_state_frame before after
Proof
  simp[typed_array_loop_address_state_def, LET_THM]
QED

Theorem typed_array_loop_counter_state_frame[simp]:
  !var_base counter counter_word before after.
    copy_state_frame before (typed_array_loop_counter_state var_base counter counter_word after) <=>
    copy_state_frame before after
Proof
  simp[typed_array_loop_counter_state_def]
QED

Theorem dyn_copy_prefix_result_state_frame[simp]:
  !var_base dst_addr src_addr n before after.
    copy_state_frame before (dyn_copy_prefix_result var_base dst_addr src_addr n after) <=>
    copy_state_frame before after
Proof
  simp[dyn_copy_prefix_result_def]
QED
