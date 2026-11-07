(* Actual dynamic-array store paths, with raw selected-word history. *)
Theory augAssignDynStoreHistory
Ancestors
  placeDynStorageEffect placeDynStoragePath stmtSimStoreCopy placeStoreStorage
  placeDynLayout valueEncoding
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

Theorem encode_uint_dyn_buffer[local]:
  mload (w2n b) s = n2w (LENGTH xs) /\
  (!i. i < LENGTH xs ==>
    mload (w2n (b+n2w (SUC i)*32w)) s = i2w (EL i xs)) ==>
  encode_value (ArrayTV (BaseTV (UintT 256)) (Dynamic cap))
    (ArrayV (DynArrayV (MAP IntV xs))) =
  SOME (GENLIST (\i. (i,mload (w2n (b+n2w i*32w)) s)) (1+LENGTH xs))
Proof
  strip_tac >> simp[encode_value_def, encode_uint_dyn_slots,
    LENGTH_MAP, GSYM ADD1, GENLIST_CONS, o_DEF] >>
  conj_tac >- simp[WORD_MULT_CLAUSES, WORD_ADD_0] >>
  irule GENLIST_CONG >> simp[]
QED

Theorem store_copy_other_backend[local]:
  !n s b k tr.
  (if tr then sload saved else tload saved)
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s n) =
  (if tr then sload saved else tload saved) s
Proof
  Induct >> rpt gen_tac >>
  simp[placeStoreCopyPathTheory.place_store_prefix_eqs] >>
  first_x_assum (qspecl_then [`s`,`b`,`k`,`tr`] mp_tac) >>
  Cases_on `tr` >>
  simp[sload_def, tload_def, sstore_def, tstore_def,
    contract_storage_def, contract_transient_def]
QED

Theorem uint_dyn_normalized_history[local]:
  write_place cx
    (StoragePlace tr k (ArrayTV (BaseTV (UintT 256)) (Dynamic cap)))
    (ArrayV (DynArrayV (MAP IntV xs))) ee = (INL (),ff) /\
  mload (w2n b) s = n2w (LENGTH xs) /\
  (!i. i < LENGTH xs ==>
    mload (w2n (b+n2w (SUC i)*32w)) s = i2w (EL i xs)) /\
  (if r then tload saved s else sload saved s) =
    lookup_storage saved (get_storage cx ee r) /\
  store_copy_normalize s t =
    store_copy_prefix (if tr then LocTransient else LocStorage) b k s (1+LENGTH xs) ==>
  (if r then tload saved t else sload saved t) =
    lookup_storage saved (get_storage cx ff r)
Proof
  strip_tac >>
  `encode_value (ArrayTV (BaseTV (UintT 256)) (Dynamic cap))
    (ArrayV (DynArrayV (MAP IntV xs))) =
   SOME (GENLIST (\i. (i,mload (w2n (b+n2w i*32w)) s)) (1+LENGTH xs))` by
    (irule encode_uint_dyn_buffer >> simp[]) >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, write_storage_slot_eq] >>
  Cases_on `cx.txn.is_static` >> simp[] >> strip_tac >> gvs[] >>
  `(if r then tload saved t else sload saved t) =
   lookup_storage saved ((if r then contract_transient else contract_storage)
     (store_copy_prefix (if tr then LocTransient else LocStorage)
       b k s (1+LENGTH xs)))` by
    (qpat_x_assum `store_copy_normalize _ _ = _` mp_tac >>
     Cases_on `r` >>
     simp[store_copy_normalize_def, venom_state_component_equality] >>
     strip_tac >> gvs[sload_def, tload_def,
       contract_storage_def, contract_transient_def]) >>
  Cases_on `r = tr`
  >- (gvs[get_storage_after_set] >> asm_rewrite_tac[] >> sym_tac >>
      simp[ADD_COMM] >> irule store_copy_selected_word >>
      Cases_on `r` >> gvs[sload_def, tload_def]) >>
  simp[get_storage_after_set_other] >>
  qspec_then `1+LENGTH xs` mp_tac store_copy_other_backend >>
  disch_then (qspecl_then [`s`,`b`,`k`,`tr`] mp_tac) >>
  Cases_on `tr` >> Cases_on `r` >> gvs[sload_def, tload_def]
QED
Theorem uint_dyn_buffer_words[local]:
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Dynamic cap))
    (ArrayV (DynArrayV (MAP IntV xs))) (w2n (b:bytes32)) s.vs_memory /\
  LENGTH xs <= cap /\ w2n b+32*(1+cap) <= dimword (:256) ==>
  mload (w2n b) s = n2w (LENGTH xs) /\
  (!i. i < LENGTH xs ==>
    mload (w2n (b+n2w (SUC i)*32w)) s = i2w (EL i xs))
Proof
  strip_tac >> conj_tac
  >- gvs[valueEncodingTheory.val_in_memory_def, mload_def,
         valueEncodingTheory.mem_word_at_def] >>
  rpt strip_tac >>
  `val_in_memory (BaseTV (UintT 256)) (IntV (EL i xs))
    (w2n b+32+i*32) s.vs_memory` by
    (drule placeDynLayoutTheory.place_dyn_memory_element >> simp[] >>
     disch_then (qspec_then `i` mp_tac) >>
     simp[valueEncodingTheory.type_memory_size_def, EL_MAP]) >>
  `w2n b + SUC i*32 < dimword (:256)` by decide_tac >>
  `b+n2w (SUC i)*32w = n2w (w2n b+SUC i*32)` by
    (pure_rewrite_tac[GSYM word_mul_n2w, GSYM word_add_n2w,
       n2w_w2n] >> simp[]) >>
  qpat_x_assum `val_in_memory (ArrayTV _ _) _ _ _` kall_tac >>
  qpat_x_assum `val_in_memory _ (IntV _) _ _` mp_tac >>
  simp[valueEncodingTheory.val_in_memory_def, valueEncodingTheory.val_to_w256_def] >>
  strip_tac >>
  qpat_x_assum `b + _ = _` kall_tac >>
  `32*SUC i+w2n b = 32*i+(w2n b+32)` by decide_tac >>
  qpat_x_assum `mem_word_at _ _ = _` mp_tac >>
  simp[mload_def, valueEncodingTheory.mem_word_at_def]
QED


(* Actual compiler path, not just a masked postcondition.  The selected
   backend r is independent of the destination backend tr, and saved is
   unrestricted (header, payload, dead tail, or outside the destination).
   No nonemptiness or relation to the old length is assumed: the same
   boundary includes empty writes and shortening an existing array. *)
Theorem uint_dyn_store_path_history:
  compile_dynarray_to_storage src dst 1 32 tr sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Dynamic cap))
    (ArrayV (DynArrayV (MAP IntV xs))) (w2n b) s.vs_memory /\
  LENGTH xs < dimword (:256) /\ LENGTH xs <= cap /\
  w2n k+1+cap <= dimword (:256) /\
  w2n b+32*(1+cap) <= dimword (:256) /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  write_place cx
    (StoragePlace tr k (ArrayTV (BaseTV (UintT 256)) (Dynamic cap)))
    (ArrayV (DynArrayV (MAP IntV xs))) ee = (INL (),ff) /\
  (if r then tload saved s else sload saved s) =
    lookup_storage saved (get_storage cx ee r) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (if r then tload saved t else sload saved t) =
        lookup_storage saved (get_storage cx ff r)
Proof
  strip_tac >> drule_all uint_dyn_buffer_words >> strip_tac >>
  drule place_dyn_storage_path >> simp[] >>
  disch_then drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `store_copy_normalize s t =
   store_copy_prefix (if tr then LocTransient else LocStorage)
     b k s (1+LENGTH xs)` by
    (qpat_assum `LENGTH xs <= cap`
       (mp_then (Pos hd) mp_tac place_dyn_storage_flat) >>
     disch_then (qspecl_then [`tr`,`s`,`k`,`1`,`b`] mp_tac) >>
     gvs[mload_def, valueEncodingTheory.mem_word_at_def]) >>
  qexists_tac `t` >> simp[] >>
  irule uint_dyn_normalized_history >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED
