Theory declaredStorageAgreement
Ancestors
  accountsRelProps compileEnv vyperStorageFrame words arithmetic

Theorem dead_bytes_outside_leaf_frame[local]:
  !old post root tv base leaf j b.
    ranges_disjoint root (type_slot_size tv) base (type_slot_size leaf) /\
    (!i. i < dimword (:256) /\
         ~(base <= i /\ i < base + type_slot_size leaf) ==>
         lookup_storage (n2w i) post = lookup_storage (n2w i) old) ==>
    (dead_bytes post root tv j b <=> dead_bytes old root tv j b)
Proof
  rpt strip_tac >> irule (cj 1 dead_bytes_frame) >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[ranges_disjoint_def] >> decide_tac
QED

Theorem storage_dead_outside_subregion[local]:
  !cx tr old post mid0 name keys root tv base leaf j b.
    declared_storage_region cx mid0 name keys = SOME (tr,root,tv) /\
    w2n root <= base /\
    base + type_slot_size leaf <= w2n root + type_slot_size tv /\
    (!i. i < dimword (:256) /\
         ~(base <= i /\ i < base + type_slot_size leaf) ==>
         lookup_storage (n2w i) post = lookup_storage (n2w i) old) /\
    (!j b. j < dimword (:256) /\ b < 32 /\
       ~(base <= j /\ j < base + type_slot_size leaf) /\
       dead_bytes old (w2n root) tv j b ==>
       dead_bytes post (w2n root) tv j b) /\
    j < dimword (:256) /\ b < 32 /\
    ~(base <= j /\ j < base + type_slot_size leaf) /\
    storage_dead cx tr old j b ==>
    storage_dead cx tr post j b
Proof
  rpt gen_tac >> simp_tac bool_ss [storage_dead_def] >> strip_tac >>
  (qexistsl_tac [`mid`, `n`, `subs`, `slot`, `tv'`] >>
  asm_rewrite_tac[] >>
  Cases_on `(slot,tv') = (root,tv)`
  >- (gvs[] >> metis_tac[]) >>
  rename1 `w2n root <= bs` >>
  `ranges_disjoint (w2n slot) (type_slot_size tv')
                   bs (type_slot_size leaf)` by
    (`ranges_disjoint (w2n slot) (type_slot_size tv')
                      (w2n root) (type_slot_size tv)` by metis_tac[] >>
     gvs[ranges_disjoint_def] >> decide_tac) >>
  drule dead_bytes_outside_leaf_frame >> metis_tac[])
QED

Theorem storage_agree_subregion_effect:
  !cx mid name keys tr root tv base leaf old backend_old post backend_post.
    declared_storage_region cx mid name keys = SOME (tr,root,tv) /\
    w2n root + type_slot_size tv <= dimword (:256) /\
    (!mid' name' keys' root' tv'.
       declared_storage_region cx mid' name' keys' = SOME (tr,root',tv') /\
       (root',tv') <> (root,tv) ==>
       ranges_disjoint (w2n root) (type_slot_size tv)
                       (w2n root') (type_slot_size tv')) /\
    w2n root <= base /\
    base + type_slot_size leaf <= w2n root + type_slot_size tv /\
    storage_agree (storage_dead cx tr old) old backend_old /\
    (!j. j < dimword (:256) /\
         ~(base <= j /\ j < base + type_slot_size leaf) ==>
         lookup_storage (n2w j) post = lookup_storage (n2w j) old) /\
    (!j. j < dimword (:256) /\
         ~(base <= j /\ j < base + type_slot_size leaf) ==>
         lookup_storage (n2w j) backend_post =
         lookup_storage (n2w j) backend_old) /\
    storage_agree (\j b. ~(base <= j /\ j < base + type_slot_size leaf) \/
                         dead_bytes post base leaf j b) post backend_post /\
    (!j b. j < dimword (:256) /\ b < 32 /\
       base <= j /\ j < base + type_slot_size leaf /\
       dead_bytes post base leaf j b ==>
       dead_bytes post (w2n root) tv j b) /\
    (!j b. j < dimword (:256) /\ b < 32 /\
       ~(base <= j /\ j < base + type_slot_size leaf) /\
       dead_bytes old (w2n root) tv j b ==>
       dead_bytes post (w2n root) tv j b) ==>
    storage_agree (storage_dead cx tr post) post backend_post
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [storage_agree_def] >> rpt gen_tac >> strip_tac >>
  rename1 `~storage_dead cx tr post (w2n q) b` >>
  rename1 `w2n root <= bs` >>
  Cases_on `bs <= w2n q /\ w2n q < bs + type_slot_size leaf`
  >- (`~dead_bytes post bs leaf (w2n q) b` by
        (strip_tac >>
         `dead_bytes post (w2n root) tv (w2n q) b` by
           metis_tac[w2n_lt] >>
         qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [storage_dead_def] >>
         qexistsl_tac [`mid`, `name`, `keys`, `root`, `tv`] >>
         asm_rewrite_tac[]) >>
      qpat_x_assum `storage_agree (\j b. _) _ _` mp_tac >>
      simp[storage_agree_def] >> metis_tac[]) >>
  `~storage_dead cx tr old (w2n q) b` by
    (strip_tac >> qpat_x_assum `~storage_dead _ _ post _ _` mp_tac >>
     simp[] >>
     `w2n q < dimword (:256)` by simp[w2n_lt] >>
     drule_all storage_dead_outside_subregion >> simp[]) >>
  `lookup_storage q post = lookup_storage q old /\
   lookup_storage q backend_post = lookup_storage q backend_old` by
    (qpat_x_assum `!j. _ ==> lookup_storage _ post = _`
       (qspec_then `w2n q` mp_tac) >>
     qpat_x_assum `!j. _ ==> lookup_storage _ backend_post = _`
       (qspec_then `w2n q` mp_tac) >> simp[w2n_lt]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `storage_agree (storage_dead _ _ old) _ _` mp_tac >>
  simp[storage_agree_def]
QED
