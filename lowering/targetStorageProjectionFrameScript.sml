Theory targetStorageProjectionFrame
Ancestors
  accountsRelProps vyperLookupStorage vyperStorageFrame loweringStateRelDefs
  vyperStorage

Theorem storage_projection_capacity_read_live:
  !cx mid name keys tr root rtv slot tv st st'.
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    w2n root <= w2n slot /\
    w2n slot + type_slot_size tv <= w2n root + type_slot_size rtv /\
    w2n root + type_slot_size rtv <= dimword (:256) /\
    (!q. w2n root <= q /\ q < w2n root + type_slot_size rtv ==>
      lookup_storage (n2w q) st' = lookup_storage (n2w q) st) /\
    (!j b. w2n slot <= j /\ j < w2n slot + type_slot_size tv /\
      dead_bytes st (w2n root) rtv j b ==>
      dead_bytes st (w2n slot) tv j b) ==>
    storage_read_live cx tr st' slot tv
Proof
  rpt strip_tac >>
  `!q. w2n slot <= q /\ q < w2n slot + type_slot_size tv ==>
    lookup_storage (n2w q) st' = lookup_storage (n2w q) st` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!j b. dead_bytes st' (w2n root) rtv j b <=>
    dead_bytes st (w2n root) rtv j b` by
    (rpt gen_tac >> irule (cj 1 dead_bytes_frame) >> simp[]) >>
  `!j b. dead_bytes st' (w2n slot) tv j b <=>
    dead_bytes st (w2n slot) tv j b` by
    (rpt gen_tac >> irule (cj 1 dead_bytes_frame) >> simp[]) >>
  pure_rewrite_tac [storage_read_live_def, storage_dead_def] >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- decide_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `dead_bytes st' (w2n other) otv j b` >>
  Cases_on `(other,otv) = (root,rtv)`
  >- (gvs[] >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!mid' n' subs' slot' tv'. _`
    (qspecl_then [`mid`, `name`, `keys`, `root`, `rtv`] mp_tac) >>
  simp[ranges_disjoint_def] >>
  drule (cj 1 dead_bytes_range) >> rpt strip_tac >> decide_tac
QED

Theorem slots_in_range_capacity_frame:
  !root rtv slot tv st st'.
    w2n root <= w2n slot /\
    w2n slot + type_slot_size tv <= w2n root + type_slot_size rtv /\
    w2n root + type_slot_size rtv <= dimword (:256) /\
    (!q. w2n root <= q /\ q < w2n root + type_slot_size rtv ==>
      lookup_storage (n2w q) st' = lookup_storage (n2w q) st) ==>
    (slots_in_range st' (w2n slot) tv <=> slots_in_range st (w2n slot) tv)
Proof
  rpt strip_tac >> irule (cj 1 slots_in_range_read_agree) >>
  rpt strip_tac >>
  simp[read_slot_def] >> first_x_assum irule >> decide_tac
QED
