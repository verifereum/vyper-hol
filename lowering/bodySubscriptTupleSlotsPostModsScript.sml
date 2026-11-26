(* Tuple selection in storage or transient storage, at the ADD endpoint. *)
Theory bodySubscriptTupleSlotsPostMods
Ancestors
  bodyFullPostsMods exprSimAttributeProps
  exprSimPopNestedBase exprSimAttributeFields abiDecodeStaticProps accountsRelProps
  loweringStateRelDefs loweringPosts bodyPtrDefs
  vyperStorageBackend vyperLookupStorage vyperStorage vyperState vyperValue
  context venomState words list rich_list arithmetic

Theorem tuple_decode_selected[local]:
  !tvs st a vs k.
    decode_tuple st a tvs = SOME vs /\ k < LENGTH tvs ==>
    decode_value st (a + tuple_prefix_slot_size k tvs) (EL k tvs) =
      SOME (EL k vs)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `k` >> gvs[tuple_prefix_slot_size_def] >>
  first_x_assum drule_all >> rewrite_tac[ADD_ASSOC]
QED

Theorem tuple_slot_read_selected[local]:
  read_storage_slot cx tr w (TupleTV tvs) ee = (INL (ArrayV (TupleV vs)),ee) /\
  k < LENGTH tvs ==>
  read_storage_slot cx tr (w + n2w (tuple_prefix_slot_size k tvs))
    (EL k tvs) ee = (INL (EL k vs),ee)
Proof
  simp[read_storage_slot_eq, AllCaseEqs()] >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all_then assume_tac tuple_decode_selected >>
  `decode_value (get_storage cx ee tr) (w2n (w + n2w (tuple_prefix_slot_size k tvs)))
      (EL k tvs) =
   decode_value (get_storage cx ee tr) (w2n w + tuple_prefix_slot_size k tvs)
      (EL k tvs)` by
    (irule (cj 1 decode_value_n2w) >>
     rewrite_tac[GSYM word_add_n2w, n2w_w2n]) >> simp[]
QED

(* Keep the empty slot interval modular; only positive slices need nonwrap. *)
Theorem tuple_slot_slice[local]:
  k < LENGTH tvs /\
  tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <= type_slot_size (TupleTV tvs) /\
  w2n (w:bytes32) + type_slot_size (TupleTV tvs) <= dimword (:256) ==>
  let a = w2n (w + n2w (tuple_prefix_slot_size k tvs)) in
  a + type_slot_size (EL k tvs) <= dimword (:256) /\
  !j b st. a <= j /\ j < a + type_slot_size (EL k tvs) ==>
    w2n w <= j /\ j < w2n w + type_slot_size (TupleTV tvs) /\
    (dead_bytes st (w2n w) (TupleTV tvs) j b ==>
     dead_bytes st a (EL k tvs) j b)
Proof
  strip_tac >> simp[LET_THM] >>
  Cases_on `type_slot_size (EL k tvs) = 0`
  >- (simp[] >> irule LESS_IMP_LESS_OR_EQ >> simp[w2n_lt]) >>
  `w2n (w + n2w (tuple_prefix_slot_size k tvs)) =
    w2n w + tuple_prefix_slot_size k tvs` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  rewrite_tac[Once dead_bytes_def] >> strip_tac >>
  irule dead_bytes_list_el >> asm_rewrite_tac[] >> decide_tac
QED

Theorem tuple_slot_agree_selected[local]:
  k < LENGTH tvs /\
  tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <= type_slot_size (TupleTV tvs) /\
  storage_range_agree st st' w (TupleTV tvs) ==>
  storage_range_agree st st' (w + n2w (tuple_prefix_slot_size k tvs)) (EL k tvs)
Proof
  pure_rewrite_tac[storage_range_agree_def] >> strip_tac >>
  drule_all_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) tuple_slot_slice >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> strip_tac >>
  rename1 `b < 32` >> rename1 `~dead_bytes st _ _ (w2n (needle:bytes32)) b` >>
  qpat_assum `!j b st. _ ==> _`
    (qspecl_then [`w2n needle`,`b`,`st`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then strip_assume_tac >>
  qpat_assum `!a b. _ ==> _ = _` irule >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem tuple_slot_live_selected[local]:
  k < LENGTH tvs /\
  tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <= type_slot_size (TupleTV tvs) /\
  storage_read_live H tr st w (TupleTV tvs) ==>
  storage_read_live H tr st (w + n2w (tuple_prefix_slot_size k tvs)) (EL k tvs)
Proof
  pure_rewrite_tac[storage_read_live_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!j b. storage_dead _ _ _ j b ==> _` (drule_then strip_assume_tac) >>
  drule_all_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) tuple_slot_slice >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  rename1 `storage_dead H tr st j b` >>
  qpat_assum `!j b st. _ ==> _` (qspecl_then [`j`,`b`,`st`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then strip_assume_tac >> metis_tac[]
QED

Theorem tuple_slot_holds_selected[local]:
  storage_holds cx tr (TupleT tys) raw w ee t /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx raw' ee = (INL (EL k vs),ee) /\ k < LENGTH tvs /\
  tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <= type_slot_size (TupleTV tvs) ==>
  storage_holds cx tr (EL k tys) raw'
    (w + n2w (tuple_prefix_slot_size k tvs)) ee t
Proof
  simp[storage_holds_def] >> strip_tac >>
  `tvt = TupleTV tvs /\ v = ArrayV (TupleV vs)` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ, sumTheory.INL_11] >>
  gvs[] >>
  conj_tac >- (irule tuple_slot_read_selected >> simp[]) >>
  conj_tac >- (irule nested_pop_tuple_slots >> simp[oEL_THM]) >>
  irule tuple_slot_agree_selected >> simp[]
QED

Theorem tuple_slot_base_facts[local]:
  vv_loc bvv = slot_loc tr /\
  vv_holds_mods cenv cx (TupleT tys) raw bvv ee t /\
  eval_operand (vv_operand bvv) t = SOME w /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) ==>
  storage_holds cx tr (TupleT tys) raw w ee t /\
  (vv_storage_live H cx bvv ee t ==>
   storage_read_live H tr (get_storage cx ee tr) w (TupleTV tvs))
Proof
  Cases_on `bvv` >> Cases_on `tr` >>
  simp[vv_loc_def, vv_location_def, vv_operand_def, slot_loc_def,
       vv_holds_mods_def, vv_holds_def] >> rpt strip_tac >> gvs[]
QED

Theorem tuple_slot_ptr_selected[local]:
  vv_loc bvv = slot_loc tr /\ ptr_vv_ok cx (TupleT tys) raw bvv ee G tn s /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  k < LENGTH tvs /\
  tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <= type_slot_size (TupleTV tvs) /\
  w2n w + type_slot_size (TupleTV tvs) <= dimword (:256) /\
  eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_prefix_slot_size k tvs)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ op_taint tn' dst = {} ==>
  ptr_vv_ok cx (EL k tys) raw' (LocatedValue (EL k tys) (mk_ptr dst (slot_loc tr))) ee G' tn' t
Proof
  strip_tac >> drule_all tuple_slot_slice >> simp[LET_THM] >> strip_tac >>
  Cases_on `bvv` >> Cases_on `tr` >>
  gvs[vv_loc_def, vv_location_def, vv_operand_def, slot_loc_def,
      ptr_vv_ok_def, mk_ptr_def]
QED

Theorem tuple_subscript_slots_post_mods:
  vv_loc bvv = slot_loc tr /\
  vv_holds_mods cenv cx (TupleT tys) raw bvv ee t /\
  ptr_vv_ok cx (TupleT tys) raw bvv ee G tn s /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  k < LENGTH tvs /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx raw' ee = (INL (EL k vs),ee) /\
  tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <= type_slot_size (TupleTV tvs) /\
  eval_operand (vv_operand bvv) s = SOME w /\ eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_prefix_slot_size k tvs)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ op_taint tn' dst = {} ==>
  vv_holds_mods cenv cx (EL k tys) raw'
    (LocatedValue (EL k tys) (mk_ptr dst (slot_loc tr))) ee t /\
  (vv_storage_live H cx bvv ee t ==>
   vv_storage_live H cx (LocatedValue (EL k tys) (mk_ptr dst (slot_loc tr))) ee t) /\
  ptr_vv_ok cx (EL k tys) raw' (LocatedValue (EL k tys) (mk_ptr dst (slot_loc tr))) ee G' tn' t
Proof
  strip_tac >> drule_all_then (qspec_then `H` strip_assume_tac) tuple_slot_base_facts >>
  drule_all_then assume_tac tuple_slot_holds_selected >>
  `w2n w + type_slot_size (TupleTV tvs) <= dimword (:256)` by
    (qpat_assum `storage_holds _ _ (TupleT _) _ _ _ _`
       (mp_tac o REWRITE_RULE [storage_holds_def, storage_range_agree_def]) >>
     strip_tac >> gvs[]) >>
  conj_tac
  >- (Cases_on `tr` >> gvs[vv_holds_mods_def, vv_holds_def, slot_loc_def, mk_ptr_def]) >>
  reverse conj_tac >- (drule_all tuple_slot_ptr_selected >> simp[]) >>
  strip_tac >>
  `storage_read_live H tr (get_storage cx ee tr)
    (w + n2w (tuple_prefix_slot_size k tvs)) (EL k tvs)` by
    (irule tuple_slot_live_selected >> simp[]) >>
  Cases_on `tr` >> gvs[slot_loc_def, mk_ptr_def]
QED
