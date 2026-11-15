Theory guardStorageTransport
Ancestors
  guardStorageLive guardDeadByteRange vyperStorageFootprint
  loweringStateRelDefs vyperStorageBackend

Theorem guard_storage_transport:
  regions_consistent (FST H) /\
  EVERY (\r. MEM r (FST H)) (FST h) /\
  storage_agree (storage_dead h tr s) s t ==>
  !slot tv. MEM (tr,slot,tv) (FST H) ==>
    (slots_in_range s (w2n slot) tv <=>
     slots_in_range t (w2n slot) tv)
Proof
  strip_tac >>
  mp_tac (guard_storage_transport_conditional |> Q.INST
    [`H` |-> `H`, `h` |-> `h`, `tr` |-> `tr`, `s` |-> `s`, `t` |-> `t`]) >>
  simp[CONJUNCT1 slots_in_range_live_bytes_mutual]
QED

Theorem guard_storage_well_formed_transport:
  regions_consistent (FST H) /\
  EVERY (\r. MEM r (FST H)) (FST h) /\
  accounts_agree h cx st.accounts st'.accounts /\
  transient_agree h cx st.tStorage st'.tStorage ==>
  (storage_well_formed_on cx st (FST H) <=>
   storage_well_formed_on cx st' (FST H))
Proof
  strip_tac >>
  `!b. storage_agree (storage_dead h b (get_storage cx st b))
    (get_storage cx st b) (get_storage cx st' b)` by
    (gen_tac >> Cases_on `b` >>
     fs[get_storage_def, accounts_agree_def, transient_agree_def]) >>
  `!b slot tv. MEM (b,slot,tv) (FST H) ==>
    (slots_in_range (get_storage cx st b) (w2n slot) tv <=>
     slots_in_range (get_storage cx st' b) (w2n slot) tv)` by
    (rpt strip_tac >>
     `storage_agree (storage_dead h b (get_storage cx st b))
       (get_storage cx st b) (get_storage cx st' b)` by simp[] >>
     drule_all guard_storage_transport >> simp[]) >>
  simp[storage_well_formed_on_def]
QED
