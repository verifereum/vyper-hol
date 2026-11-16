(* Inverse clean-word writes and robust field transport. *)
Theory augAssignPtrFieldStore
Ancestors
  assignBasePtrFieldRobust wordLoadStorePtr mstoreRestorePtr augAssignPtrStore robustCopyTransportPtr valueEncodingProps valueEncodingProofs
  venomMemProofs venomState list pred_set arithmetic typedCopyPtr bodyPtrDefs byte words
  stmtSimAssignAttr loweringSlice

Theorem fields_in_memory_mstore_field_robust:
  fields_layout flds fs /\ struct_has_type fs vals /\
  fields_val_wf vals fs /\ ALOOKUP fs fld = SOME ftv /\
  type_memory_size ftv = 32 /\ word_value v /\
  (!m. mem_agree_outside tainted s.vs_memory m ==>
       fields_in_memory vals fs off m) ==>
  !m. mem_agree_outside
       (tainted DIFF {i | off + struct_field_offset flds fld <= i /\
                         i < off + struct_field_offset flds fld + 32})
       (mstore (off + struct_field_offset flds fld) (val_to_w256 v) s).vs_memory m ==>
      fields_in_memory (AFUPDKEY fld (K v) vals) fs off m
Proof
  rpt strip_tac >> drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `fields_in_memory vals fs off u` by metis_tac[] >>
  `fields_in_memory (AFUPDKEY fld (K v) vals) fs off
    (mstore (off + struct_field_offset flds fld) (val_to_w256 v)
      (s with vs_memory := u)).vs_memory` by
    (irule fields_in_memory_mstore_field >> simp[word_value_in_memory] >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule (cj 2 val_in_memory_mem_agree_proof) >>
  conj_tac
  >- (irule fields_val_wf_update >> goal_assum (drule_at Any) >>
      simp[word_value_wf]) >>
  goal_assum (drule_at Any) >>
  drule memory_byte_agree_window >> simp[]
QED
