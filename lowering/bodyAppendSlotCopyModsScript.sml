(* The source and counted suffix for aggregate storage/transient Append. *)
Theory bodyAppendSlotCopyMods
Ancestors
  stmtSimAppendStorage vyperStorageBackend vyperStorage vyperState
  vyperValue vfmState words integer_word

(* Read the header at the reached state, not at target entry. *)
Theorem append_slot_copy_source_mods:
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\
  encode_value tv v = SOME writes ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    if cap <= len then (INR (Error (RuntimeError "append full storage array")), es)
    else if cx.txn.is_static then (INR (Error (RuntimeError "write in static context")), es)
    else (INL (), set_storage cx es tr
           (update_storage slot (n2w (len+1))
             (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes
               (get_storage cx es tr))))
Proof
  strip_tac >> gvs[] >>
  IF_CASES_TAC >- simp[stmtSimAppendStorageTheory.append_storage_full] >>
  `w2n (lookup_storage slot (get_storage cx es tr)) < cap` by decide_tac >>
  IF_CASES_TAC >- simp[stmtSimAppendStorageTheory.append_storage_static] >>
  simp[append_storage_writes, ignore_bind_def, bind_def,
       write_storage_slot_eq, get_storage_after_set, encode_value_def,
       encode_base_to_slot_def, apply_writes_def, i2w_def] >>
  Cases_on `tr` >> simp[set_storage_def, combinTheory.APPLY_UPDATE_THM]
QED
