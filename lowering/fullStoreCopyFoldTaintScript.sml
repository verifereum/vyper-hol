(* Raw finite store folds expose one storage-taint boundary. *)
Theory fullStoreCopyFoldTaint
Ancestors fullStoreCopyTaint assignBasePtrStorageSemantic placeStoreSlots
  storageCopyLive valueEncodingProps venomState venomMemDefs stmtSimStoreCopy
  words arithmetic list rich_list pred_set

Theorem store_copy_fold_stor_taint_ok:
  declared_storage_region cx mid n subs = SOME (tr,(k:bytes32),tv) /\
  MEM (tr,k,tv) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\ 0 < type_slot_size tv /\
  w2n k + type_slot_size tv <= dimword(:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v off m) /\
  store_copy_normalize s u =
    FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
      (mload (off+32*i) s) q) s ks /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta i. key_update ta (k+n2w i)
      (mem_word_taint tn.t_mem (off+32*i)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  (if tr then tf.t_stor else tf.t_trans) =
    (if tr then tn.t_stor else tn.t_trans) /\
  tf.t_imm = tn.t_imm /\ (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_call_ctx.cc_address = cx.txn.target /\
  stor_taint_ok H cx tn s ==>
  stor_taint_ok H cx tf u
Proof
  strip_tac >>
  `val_in_memory tv v off s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  FAIL_TAC "fold projection"
QED
