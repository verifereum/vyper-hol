Theory entryCreateStoredLength
Ancestors
  entryCreateRawArgExtent createSizeSlotHeader exprPtrUnwrapStorageSource
  loweringPosts vyperLookupStorage vyperStorageBackend vyperStorage vyperValue vyperTypeSystem
  allocLimits vyperAST slotCopyExecution venomState venomInst byte list words arithmetic

(* A typed storage post uses the selected slot and backend, including the
   state after any source effects. Only the first word of the actual copy is
   needed at the unwrap endpoint. The checked annotation may be wider than
   the represented bytes type. *)
Theorem blueprint_stored_length_at_materialization:
  alloc_limits_expr ce e /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
  type_widens_to (get_tenv cx) (BaseT (BytesT (Dynamic k))) (expr_type e) /\
  storage_holds cx tr (BaseT (BytesT (Dynamic k))) result slot es s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  read_result cx result es = (INL (BytesV bs),es) /\
  0 < n /\
  slot_copy_prefix (if tr then TLOAD else SLOAD) s slot (w2n d) n z /\
  u.vs_memory = z.vs_memory ==>
  mload (w2n d) u = n2w (LENGTH bs) /\ LENGTH bs <= k /\
  k < 2 ** 64 /\ w2n (mload (w2n d) u) < 2 ** 64
Proof
  strip_tac >>
  drule_all blueprint_raw_capacity_bound >> disch_tac >>
  `k <= cap` by
    (qpat_assum `type_widens_to _ _ _` mp_tac >>
     qpat_assum `expr_type e = _` (fn th => rewrite_tac[th]) >>
     simp[type_widens_to_def, arg_type_fits_def] >> strip_tac >> simp[]) >>
  drule_all storage_holds_decode >> strip_tac >> gvs[] >>
  drule_all create_slot_source_length_word >> strip_tac >>
  `LENGTH bs <= k` by
    (gvs[Once decode_value_def, AllCaseEqs()] >>
     drule storageDecodeMemoryTheory.decode_dyn_bytes_observations >> simp[]) >>
  `mload (w2n d) u = n2w (LENGTH bs)` by
    (qpat_x_assum `slot_copy_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[slot_copy_prefix_def]) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
     `32 <= LENGTH (DROP (w2n d) u.vs_memory)` by simp[] >>
     simp[mload_def, TAKE_APPEND1, WORD_ADD_0]) >>
  `w2n (n2w (LENGTH bs) : bytes32) <= LENGTH bs` by
    simp[w2n_n2w, MOD_LESS_EQ, ZERO_LT_dimword] >>
  fs[w2n_n2w] >> decide_tac
QED
