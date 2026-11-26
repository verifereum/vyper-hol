(* A successful slot Pop writes its header but keeps the removed element's
   representation. Only range agreement at the reached subregion is needed;
   the observation identifying it is retained by the unchanged trace. *)
Theory bodyPopSlotRepresentationMods
Ancestors
  exprSimPopNestedBase exprSimPopStorage exprSimProps loweringPosts
  valueEncodingTyping vyperTypeStatePreservation vyperTypeValues
  vyperStorageBackend accountsRelProps venomState venomExecSemantics words

Theorem pop_slot_representation_mods:
  storage_range_agree (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s)
    slot (ArrayTV tv (Dynamic n)) /\
  slots_in_range (get_storage cx ee tr) (w2n slot) (ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage slot (get_storage cx ee tr)) /\
  0 < len /\ ~cx.txn.is_static /\
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx ee tr) /\
  raw = (if tr then tstore slot (tload slot s - 1w) s
         else sstore slot (sload slot s - 1w) s) with vs_vars := raw.vs_vars /\
  lookup_var out raw = SOME (slot + 1w +
    ((if tr then tload slot s else sload slot s) - 1w) * n2w (type_slot_size tv)) /\
  u = (raw with vs_inst_idx := k) /\
  elem = slot + n2w (1 + (len - 1) * type_slot_size tv) /\
  ef = set_storage cx ee tr
    (apply_writes slot [(0,n2w (len - 1))] (get_storage cx ee tr)) ==>
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) ee =
    (INL (PlaceR (StoragePlace tr elem tv)),ef) /\
  (!tail. pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
      (ee with gas_obs := tail) =
    (INL (PlaceR (StoragePlace tr elem tv)),ef with gas_obs := tail)) /\
  ef.storage_trace = ee.storage_trace /\ ef.gas_obs = ee.gas_obs /\
  lookup_var out u = SOME elem /\
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem ef u /\
  w2n elem + type_slot_size tv <= dimword(:256) /\
  (?v. read_result cx (PlaceR (StoragePlace tr elem tv)) ef = (INL v,ef) /\
       value_has_type tv v /\ val_wf tv v /\ val_footprint tv v <= type_memory_size tv)
Proof
  strip_tac >>
  conj_asm1_tac
  >- (MAP_EVERY (fn p => qpat_assum p (fn th => PURE_ONCE_REWRITE_TAC [th]))
        [`elem = _`, `ef = _`] >>
      irule pop_storage_positive_source >> simp[]) >>
  conj_tac >- (gen_tac >> irule nested_pop_storage_gas_obs >> first_assum ACCEPT_TAC) >>
  conj_tac >- (Cases_on `tr` >> simp[set_storage_def]) >>
  conj_tac >- (Cases_on `tr` >> simp[set_storage_def]) >>
  `(if tr then tload slot s else sload slot s) - 1w = n2w (len - 1)` by
    (qpat_assum `len = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[wordsTheory.n2w_sub]) >>
  conj_tac
  >- (qpat_x_assum `lookup_var out raw = _` mp_tac >>
      simp[lookup_var_def, wordsTheory.word_mul_n2w,
           wordsTheory.word_add_n2w, GSYM wordsTheory.WORD_ADD_ASSOC]) >>
  `raw = (if tr then tstore slot (n2w (len - 1)) s
          else sstore slot (n2w (len - 1)) s) with vs_vars := raw.vs_vars` by
    (qpat_assum `raw = _ with vs_vars := _` mp_tac >> Cases_on `tr` >> fs[]) >>
  `storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem ef raw` by
    (qpat_assum `ef = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     irule nested_pop_positive_holds >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`n`,`s`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `u = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
      pop_assum mp_tac >>
      simp[storage_holds_def, contract_storage_def, contract_transient_def]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [storage_holds_def]) >>
  gvs[] >>
  conj_tac >- fs[storage_range_agree_def] >>
  `well_formed_type_value tv` by drule_then ACCEPT_TAC evaluate_type_well_formed_type_value >>
  drule_all_then assume_tac read_storage_slot_success_type >>
  drule_then assume_tac (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
  metis_tac[val_footprint_le]
QED
