Theory targetStoragePathProjection
Ancestors
  targetStorageProjectionFrame assignBasePtrStorageTaint
  vyperStorageLayoutSafety loweringStateRelDefs

Theorem storage_read_live_declared_relative_projection:
  !cx mid name keys tr root rtv slot tv st.
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    storage_layout_safe cx /\ storage_read_live cx tr st slot tv ==>
    !j b. w2n slot <= j /\ j < w2n slot + type_slot_size tv /\
      dead_bytes st (w2n root) rtv j b ==>
      dead_bytes st (w2n slot) tv j b
Proof
  rpt strip_tac >>
  `storage_dead cx tr st j b` by
    (irule declared_region_dead_storage_dead >>
     qexistsl_tac [`root`, `mid`, `name`, `keys`, `rtv`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >>
         `~((mid,name,keys) = (mid',n',subs'))` by
           (strip_tac >> gvs[]) >>
         drule_all storage_layout_safe_region_separation >> simp[]) >>
     drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  gvs[storage_read_live_def] >> metis_tac[]
QED

Theorem storage_read_live_capacity_frame:
  !cx mid name keys tr root rtv slot tv st st'.
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    storage_layout_safe cx /\ storage_read_live cx tr st slot tv /\
    w2n root <= w2n slot /\
    w2n slot + type_slot_size tv <= w2n root + type_slot_size rtv /\
    (!q. w2n root <= q /\ q < w2n root + type_slot_size rtv ==>
      lookup_storage (n2w q) st' = lookup_storage (n2w q) st) ==>
    storage_read_live cx tr st' slot tv
Proof
  rpt strip_tac >> irule storage_projection_capacity_read_live >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`keys`, `mid`, `name`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule storage_read_live_declared_relative_projection >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all storage_layout_safe_region_nonoverflow >> simp[]
QED
