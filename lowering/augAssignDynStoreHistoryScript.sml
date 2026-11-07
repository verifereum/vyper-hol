(* Actual dynamic-array store paths, with raw selected-word history. *)
Theory augAssignDynStoreHistory
Ancestors
  placeDynStorageEffect placeDynStoragePath stmtSimStoreCopy placeStoreStorage
  vyperStorageBackend vyperStorage vyperState venomState vfmState
  list rich_list words integer_word vyperValue arithmetic combin

Theorem encode_uint_dyn_slots[local]:
  !xs offset.
  encode_dyn_array (BaseTV (UintT 256)) offset (MAP IntV xs) =
    SOME (GENLIST (\i. (offset+i, i2w (EL i xs))) (LENGTH xs))
Proof
  Induct >> simp[encode_value_def, encode_base_to_slot_def,
    type_slot_size_def, listTheory.GENLIST_CONS] >>
  rpt gen_tac >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, o_DEF, ADD_CLAUSES, ADD1, AC ADD_ASSOC ADD_COMM]
QED

Theorem selected_word_paired_fold[local]:
  !is st ts (a:num->bytes32) f saved.
    lookup_storage saved st = lookup_storage saved ts ==>
    lookup_storage saved (FOLDL (\q i. update_storage (a i) (f i) q) st is) =
    lookup_storage saved (FOLDL (\q i. update_storage (a i) (f i) q) ts is)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  Cases_on `a h = saved` >> gvs[lookup_storage_def]
QED

Theorem store_copy_selected_word[local]:
  lookup_storage saved st =
    lookup_storage saved ((if tr then contract_transient else contract_storage) s) ==>
  lookup_storage saved
    (apply_writes k
      (GENLIST (\i. (i,mload (w2n (b+n2w i*32w)) s)) n) st) =
  lookup_storage saved ((if tr then contract_transient else contract_storage)
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s n))
Proof
  strip_tac >>
  simp[placeStoreStorageTheory.place_store_apply_writes_fold,
    place_store_prefix_backend, MAP_GENLIST, o_DEF] >>
  rewrite_tac[GSYM MAP_COUNT_LIST, FOLDL_MAP] >> simp[] >>
  ho_match_mp_tac selected_word_paired_fold >> simp[]
QED
