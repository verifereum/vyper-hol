Theory createSizeSlotHeader
Ancestors
  exprPtrUnwrapStorageSource storageDecodeMemory slotCopyExecution
  accountsRelProps venomState venomInst vyperStorage vyperValue words

(* The dynamic-bytes header is live even for an empty payload. *)
Theorem create_slot_source_length_word:
  storage_holds cx tr (BaseT (BytesT (Dynamic k))) tv p es s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  read_result cx tv es = (INL (BytesV bytes),es) ==>
  slot_copy_word (if tr then TLOAD else SLOAD) s p = n2w (LENGTH bytes)
Proof
  strip_tac >> drule_all storage_holds_decode >> strip_tac >> gvs[] >>
  qpat_x_assum `decode_value _ _ _ = _` mp_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule decode_dyn_bytes_observations >> strip_tac >>
  `lookup_storage p (if tr then contract_transient s else contract_storage s) =
   lookup_storage p (get_storage cx es tr)` by
    (irule storage_range_agree_head >>
     qexists `BaseTV (BytesT (Dynamic k))` >> simp[type_slot_size_def]) >>
  Cases_on `tr` >>
  fs[slot_copy_word_def, sload_def, tload_def, read_slot_def, n2w_w2n]
QED
