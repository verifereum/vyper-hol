Theory bodyPtrIfExpStorageSupplier
Ancestors accountsRelProps compileEnv vyperStorage vyperLookupStorage
  vyperValue words arithmetic

Theorem ifexp_storage_range_read_head:
  storage_range_agree st rt w ty /\ 0 < type_slot_size ty ==>
  read_slot rt (w2n w) = read_slot st (w2n w)
Proof
  strip_tac >> drule_all storage_range_agree_head >>
  simp[read_slot_def]
QED

Theorem ifexp_storage_range_bytes_length:
  storage_range_agree st rt w (BaseTV (BytesT (Dynamic max))) /\
  slots_in_range st (w2n w) (BaseTV (BytesT (Dynamic max))) ==>
  slots_in_range rt (w2n w) (BaseTV (BytesT (Dynamic max))) /\
  w2n (read_slot rt (w2n w)) = w2n (read_slot st (w2n w))
Proof
  strip_tac >>
  `read_slot rt (w2n w) = read_slot st (w2n w)` by
    (irule ifexp_storage_range_read_head >>
     qexists_tac `BaseTV (BytesT (Dynamic max))` >>
     simp[type_slot_size_def]) >>
  gvs[slots_in_range_def]
QED
