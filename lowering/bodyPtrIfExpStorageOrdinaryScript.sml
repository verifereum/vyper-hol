Theory bodyPtrIfExpStorageOrdinary
Ancestors slotCopyExecution venomMemProps valueEncodingProps
  venomState words arithmetic

Theorem ifexp_slot_condition_ordinary:
  (slot_copy_cond_result cs n i s).vs_allocas = s.vs_allocas /\
  (slot_copy_cond_result cs n i s).vs_data_section = s.vs_data_section /\
  (slot_copy_cond_result cs n i s).vs_memory = s.vs_memory
Proof
  simp[slot_copy_cond_result_def, update_var_def, jump_to_def]
QED

Theorem ifexp_slot_body_ordinary:
  (slot_copy_body_result cs p d load i s).vs_allocas = s.vs_allocas /\
  (slot_copy_body_result cs p d load i s).vs_data_section = s.vs_data_section /\
  (slot_copy_body_result cs p d load i s).vs_memory =
    (mstore (w2n (d+n2w i*32w)) (slot_copy_word load s (p+n2w i)) s).vs_memory
Proof
  simp[slot_copy_body_result_def, update_var_def, jump_to_def, mstore_def]
QED

Theorem ifexp_slot_body_memory_frame:
  i < n /\ w2n (d:bytes32)+32*n < 2**256 ==>
  LENGTH s.vs_memory <= LENGTH (slot_copy_body_result cs p d load i s).vs_memory /\
  (!b len. b+len <= w2n d \/ w2n d+32*n <= b ==>
    mem_bytes_at b len (slot_copy_body_result cs p d load i s).vs_memory =
    mem_bytes_at b len s.vs_memory)
Proof
  strip_tac >> drule_all slot_copy_body_nonwrapping >> strip_tac >>
  simp[ifexp_slot_body_ordinary] >>
  conj_tac >- simp[LENGTH_mstore_eq] >>
  rpt gen_tac >> strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  simp[] >> decide_tac
QED

Theorem ifexp_slot_initial_ordinary:
  (slot_copy_initial cs s).vs_allocas = s.vs_allocas /\
  (slot_copy_initial cs s).vs_data_section = s.vs_data_section /\
  (slot_copy_initial cs s).vs_memory = s.vs_memory
Proof
  simp[slot_copy_initial_def, update_var_def, jump_to_def]
QED
