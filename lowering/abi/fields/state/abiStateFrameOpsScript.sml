(* TOP-LEVEL: exact ABI setup, navigation, copying and suffix states preserve
   external state. Register-reset state images imply the same frame. *)
Theory abiStateFrameOps
Ancestors
  abiStateFrame abiBytestringExec abiChildPrefix abiChildSuffix abiComplexEntry abiFieldAddress
  abiStaticLoopEntry venomState list words

Theorem abi_state_context_bytestring[simp]:
  !dst_addr src_addr ss.
    abi_state_context (bytestring_copy_state dst_addr src_addr ss) = abi_state_context ss
Proof
  simp[bytestring_copy_state_def, LET_THM]
QED

Theorem abi_state_context_alloca[simp]:
  !id ss. abi_state_context (abi_static_loop_alloc_frame id ss) = abi_state_context ss
Proof
  rpt gen_tac >> simp[abi_static_loop_alloc_frame_def] >> Cases_on `FLOOKUP ss.vs_allocas id = NONE` >> simp[]
QED

Theorem abi_state_context_child_prefix[simp]:
  !var_base head_offset dst_addr dyn_addr ss.
    abi_state_context (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) = abi_state_context ss
Proof
  simp[abi_child_prefix_state_def]
QED

Theorem abi_state_context_child_suffix[simp]:
  !var_base head_addr dyn_addr tail_offset child_len ss.
    abi_state_context (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss) = abi_state_context ss
Proof
  simp[abi_child_suffix_state_def]
QED

Theorem abi_state_context_complex_prefix[simp]:
  !id var_base head_size ss.
    abi_state_context (abi_complex_prefix_state id var_base head_size ss) = abi_state_context ss
Proof
  simp[abi_complex_prefix_state_def]
QED

Theorem abi_state_context_field_address[simp]:
  !cs source_offset root_addr ss.
    abi_state_context (abi_field_address_state cs source_offset root_addr ss) = abi_state_context ss
Proof
  simp[abi_field_address_state_def]
QED

Theorem abi_state_frame_var_image:
  !before after index.
    after with vs_vars := before.vs_vars = before with vs_inst_idx := index ==>
    abi_state_frame before after
Proof
  rpt gen_tac >> disch_then (mp_tac o AP_TERM ``abi_state_context``) >> simp[abi_state_frame_def]
QED

Theorem abi_state_frame_bytestring_image:
  !dst_addr src_addr before after index.
    after with vs_vars := before.vs_vars =
      (bytestring_copy_state dst_addr src_addr before) with vs_inst_idx := index ==>
    abi_state_frame before after
Proof
  rpt gen_tac >> disch_then (mp_tac o AP_TERM ``abi_state_context``) >> simp[abi_state_frame_def]
QED
