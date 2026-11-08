Theory placeStoreCopyChunk
Ancestors
  stmtSimStoreCopy venomState list rich_list arithmetic

Theorem place_store_copy_frame_chunk:
  store_copy_frame sa loc b k sbase i s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  store_copy_normalize sbase t = store_copy_normalize sbase
    (FOLDL (\u j. (if loc = LocStorage then sstore else tstore)
       (k + n2w j) (mload (w2n (b + n2w j * 32w)) sbase) u)
       s (GENLIST (\r. i + r) n)) ==>
  store_copy_frame sa loc b k sbase (i+n) t
Proof
  strip_tac >>
  `!js acc. store_copy_normalize sbase
      (FOLDL (\u j. (if loc = LocStorage then sstore else tstore)
        (k + n2w j) (mload (w2n (b + n2w j * 32w)) sbase) u) acc js) =
    FOLDL (\u j. (if loc = LocStorage then sstore else tstore)
        (k + n2w j) (mload (w2n (b + n2w j * 32w)) sbase) u)
      (store_copy_normalize sbase acc) js` by
    (Induct >> simp[] >> rpt gen_tac >>
     first_x_assum (qspec_then
       `(if loc = LocStorage then sstore else tstore)
          (k + n2w h) (mload (w2n (b + n2w h * 32w)) sbase) acc` mp_tac) >>
     Cases_on `loc = LocStorage` >>
     simp[store_copy_normalize_def, sstore_def, tstore_def]) >>
  gvs[store_copy_frame_def] >>
  simp[store_copy_prefix_def] >>
  simp[COUNT_LIST_ADD, FOLDL_APPEND, MAP_COUNT_LIST, ADD_COMM]
QED
