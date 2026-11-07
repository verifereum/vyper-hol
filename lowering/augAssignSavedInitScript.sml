(* Initial raw agreement is available at live read heads, not arbitrary
   storage addresses.  This boundary is backend-polymorphic. *)
Theory augAssignSavedInit
Ancestors
  accountsRelProps compileEnv vyperStorageBackend venomState vfmState

(* This is the scoped initial relation for a saved aggregate. Its mask
   uses the saved aggregate's own header, not its enclosing root's header. *)
Theorem state_rel_live_storage_region:
  state_rel func cenv cx es s /\
  storage_read_live cx tr (get_storage cx es tr) root tv ==>
  !k b. w2n root <= w2n k /\
    w2n k < w2n root + type_slot_size tv /\ b < 32 /\
    ~dead_bytes (get_storage cx es tr) (w2n root) tv (w2n k) b ==>
    EL b (word_to_bytes
      (lookup_storage k (get_storage cx es tr)) T) =
    EL b (word_to_bytes
      (if tr then tload k s else sload k s) T)
Proof
  strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
     (get_storage cx es tr)
     (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[state_rel_def, storage_rel_def, transient_rel_def,
         get_storage_def, lookup_account_def]) >>
  rpt strip_tac >>
  `~storage_dead cx tr (get_storage cx es tr) (w2n k) b` by
    (gvs[storage_read_live_def] >> metis_tac[]) >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp[storage_agree_def] >>
  disch_then (qspecl_then [`k`, `b`] mp_tac) >>
  Cases_on `tr` >> gvs[tload_def, sload_def]
QED
