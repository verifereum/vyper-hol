(* Ordinary tuple selection boundaries; physical restrictions are separate. *)
Theory bodyPtrSubscriptSeamTuplePost
Ancestors
  bodyPtrSubscriptSeamTupleMemory bodyPtrSubscriptSeamTupleStorage
  bodyPtrAttributeSource exprSimAttribute exprSimAttributeFields exprSimAttributeProps
  exprSimDefs exprSimHyps exprSimProps exprSimFieldLayout exprSimTuple
  loweringPosts accountsRelProps tupleMemoryLayout compileEnv exprLowering context vyperValue vyperStorage
  vyperInterpreter vyperState valueEncoding valueEncodingProofs
  vyperValueOperation vyperTyping vyperTypeDefaults vyperLookupStorage vyperStorageBackend vyperStorageRegionWrite list rich_list words

Theorem tuple_location_sizes:
  !tys tvs cenv cx env es loc.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    MAP (elem_size_in_location cenv loc) tys =
      MAP (if is_slot_addressed loc then type_slot_size else type_memory_size) tvs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) h` >> gvs[] >>
  Cases_on `OPT_MMAP (evaluate_type (get_tenv cx)) tys` >> gvs[] >>
  rename1 `evaluate_type _ h = SOME htv` >>
  `type_memory_bytes cenv h = type_memory_size htv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  first_x_assum drule_all >> Cases_on `loc` >>
  simp[elem_size_in_location_def, is_slot_addressed_def, slot_count_of_memory_size]
QED

Theorem tuple_decode_suffix:
  !pre rest storage off vs.
    decode_tuple storage off (pre ++ rest) = SOME vs ==>
    ?front back. vs = front ++ back /\ LENGTH front = LENGTH pre /\
      decode_tuple storage (off + type_slot_size_list pre) rest = SOME back
Proof
  Induct >> simp[type_slot_size_def] >> rpt gen_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`v::front`, `back`] >>
  gvs[] >> metis_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem tuple_decode_head_after_prefix:
  decode_tuple storage off (pre ++ tv::rest) = SOME vs ==>
  decode_value storage (off + type_slot_size_list pre) tv = SOME (EL (LENGTH pre) vs)
Proof
  strip_tac >> drule tuple_decode_suffix >> strip_tac >>
  gvs[Once decode_value_def, AllCaseEqs()] >> simp[EL_APPEND_EQN]
QED

Theorem tuple_read_child:
  read_storage_slot cx tr slot (TupleTV tvs) es = (INL (ArrayV (TupleV vs)),es1) /\
  k < LENGTH tvs ==>
  read_storage_slot cx tr (slot + n2w (tuple_prefix_slot_size k tvs))
    (EL k tvs) es = (INL (EL k vs),es1)
Proof
  strip_tac >>
  `tvs = TAKE k tvs ++ EL k tvs::DROP (SUC k) tvs` by
    simp[rich_listTheory.TAKE_DROP_SUC] >>
  `decode_tuple (get_storage cx es tr) (w2n slot) tvs = SOME vs /\ es1 = es` by
    gvs[read_storage_slot_eq, Once decode_value_def, AllCaseEqs()] >>
  `decode_value (get_storage cx es tr)
    (w2n slot + type_slot_size_list (TAKE k tvs)) (EL k tvs) = SOME (EL k vs)` by
    (qpat_assum `tvs = _` (fn th =>
       qpat_x_assum `decode_tuple _ _ _ = _` (mp_tac o ONCE_REWRITE_RULE[th])) >>
     disch_then (mp_tac o MATCH_MP tuple_decode_head_after_prefix) >> simp[]) >>
  `decode_value (get_storage cx es tr)
     (w2n (slot + n2w (tuple_prefix_slot_size k tvs))) (EL k tvs) =
   decode_value (get_storage cx es tr)
     (w2n slot + type_slot_size_list (TAKE k tvs)) (EL k tvs)` by
    (rewrite_tac[type_slot_size_list_sum, GSYM tuple_prefix_slot_size_sum] >>
     irule (cj 1 decode_value_n2w) >>
     rewrite_tac[GSYM word_add_n2w, n2w_w2n]) >>
  simp[read_storage_slot_eq]
QED

Theorem tuple_agree_head:
  storage_range_agree st st' w (TupleTV (tv::rest)) ==>
  storage_range_agree st st' w tv
Proof
  simp[storage_range_agree_def, type_slot_size_def] >> strip_tac >>
  rpt strip_tac >>
  qpat_x_assum `!k b. _ ==> _` irule >> simp[] >> strip_tac >>
  qpat_x_assum `dead_bytes _ _ (TupleTV _) _ _` mp_tac >>
  simp[Ntimes dead_bytes_def 2] >>
  strip_tac >> imp_res_tac (cj 2 dead_bytes_range) >> gvs[]
QED

Theorem tuple_agree_child:
  storage_range_agree st st' w (TupleTV tvs) /\ k < LENGTH tvs ==>
  storage_range_agree st st' (w + n2w (tuple_prefix_slot_size k tvs)) (EL k tvs)
Proof
  strip_tac >>
  `tvs = TAKE k tvs ++ EL k tvs::DROP (SUC k) tvs` by simp[TAKE_DROP_SUC] >>
  qpat_assum `tvs = _` (fn th =>
    qpat_x_assum `storage_range_agree _ _ _ _` (mp_tac o ONCE_REWRITE_RULE[th])) >>
  disch_then (mp_tac o MATCH_MP tuple_agree_suffix) >>
  disch_then (mp_tac o MATCH_MP tuple_agree_head) >>
  simp[type_slot_size_list_sum, tuple_prefix_slot_size_sum]
QED

Theorem tuple_immutable_child:
  immutable_holds cenv cx (TupleT tys) tv w es s /\
  read_result cx tv es = (INL (ArrayV (TupleV vs)),es) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) ct = SOME (EL k tvs) /\
  k < LENGTH tvs /\ read_result cx tv' es = (INL (EL k vs),es) ==>
  immutable_holds cenv cx ct tv'
    (w + n2w (SUM (MAP type_memory_size (TAKE k tvs)))) es s
Proof
  strip_tac >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV vs))` by
    (fs[immutable_holds_def] >> gvs[]) >>
  `LENGTH vs = LENGTH tvs /\ value_has_type (EL k tvs) (EL k vs)` by
    (gvs[value_has_type_def, values_have_types_LIST_REL, LIST_REL_EL_EQN]) >>
  `sub_layout (TupleTV tvs) (ArrayV (TupleV vs))
    (SUM (MAP type_memory_size (TAKE k tvs))) (EL k tvs) (EL k vs)` by
    (`sub_layout (TupleTV tvs) (ArrayV (TupleV vs)) 0
        (TupleTV tvs) (ArrayV (TupleV vs))` by simp[sub_layout_def] >>
     drule tuple_child_sub_layout >> simp[]) >>
  irule immutable_holds_sub >>
  qexistsl_tac [`EL k tvs`, `EL k vs`, `TupleTV tvs`, `ArrayV (TupleV vs)`,
    `TupleT tys`, `tv`] >> simp[]
QED

Theorem nonword_vv_physical:
  vv_holds cenv cx t tv vv es s /\ ~is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tvt /\
  eval_operand (vv_operand vv) s = SOME w ==>
  ?v. read_result cx tv es = (INL v,es) /\
    (vv_loc vv = LocMemory ==> val_in_memory tvt v (w2n w) s.vs_memory) /\
    (vv_loc vv = LocStorage ==>
      read_storage_slot cx F w tvt es = (INL v,es) /\
      slots_in_range (get_storage cx es F) (w2n w) tvt /\
      storage_range_agree (get_storage cx es F) (contract_storage s) w tvt) /\
    (vv_loc vv = LocTransient ==>
      read_storage_slot cx T w tvt es = (INL v,es) /\
      slots_in_range (get_storage cx es T) (w2n w) tvt /\
      storage_range_agree (get_storage cx es T) (contract_transient s) w tvt) /\
    (vv_loc vv = LocCode ==> immutable_holds cenv cx t tv w es s) /\
    vv_loc vv <> LocCalldata
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def, expr_val_rel_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[storage_holds_def] >> metis_tac[immutable_holds_read]
QED

Theorem tuple_child_holds:
  stmt_state_rel ctx func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
  vv_holds cenv cx (TupleT tys) tv bvv es1 q /\
  vv_at cenv cx (TupleT tys) sa sn es1 tv bvv q /\
  read_result cx tv es1 = (INL (ArrayV (TupleV vs)),es1) /\
  values_have_types tvs vs /\
  read_result cx tv' es1 = (INL (EL k vs),es1) /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\ k < LENGTH tvs ==>
  vv_holds cenv cx (EL k tys) tv'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) es1 q
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
     impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >> simp[]) >>
  `LENGTH vs = LENGTH tvs /\ value_has_type (EL k tvs) (EL k vs)` by
    gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
  drule_all nonword_vv_physical >> strip_tac >> gvs[] >>
  simp[vv_holds_def, mk_ptr_def] >>
  Cases_on `vv_loc bvv` >> gvs[]
  >~ [`LocMemory`]
  >- (drule_all tuple_memory_child_address >> strip_tac >> gvs[WORD_ADD_0] >>
      `val_in_memory (EL k tvs) (EL k vs)
         (w2n w + SUM (MAP type_memory_size (TAKE k tvs))) q.vs_memory` by
        (irule tuple_in_memory_element >> gvs[val_in_memory_def]) >>
      gvs[MAP_TAKE] >> strip_tac >>
      drule_all val_in_memory_word_type >> gvs[])
  >~ [`immutable_holds`]
  >- (drule_all tuple_location_sizes >>
      disch_then (qspec_then `LocCode` assume_tac) >>
      gvs[tuple_offset_def, is_slot_addressed_def, MAP_TAKE] >>
      drule_all tuple_immutable_child >> simp[MAP_TAKE])
  >> drule_all tuple_location_sizes >>
  disch_then (qspec_then `vv_loc bvv` assume_tac) >>
  gvs[tuple_offset_def, is_slot_addressed_def, tuple_prefix_slot_size_sum] >>
  drule_all tuple_read_child >> strip_tac >>
  drule_all tuple_agree_child >> strip_tac >>
  `oEL k tvs = SOME (EL k tvs)` by simp[oEL_THM] >>
  drule_all exprSimPopNestedBaseTheory.nested_pop_tuple_slots >> strip_tac >>
  gvs[storage_holds_def, tuple_prefix_slot_size_sum, MAP_TAKE]
QED

Theorem tuple_child_post:
  vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
  post_value_type cenv obj = TupleT tys /\ expr_type obj = TupleT tys /\
  expr_sim_inv cenv cx env es /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  k < LENGTH tvs /\
  read_result cx tv es1 = (INL (ArrayV (TupleV vs)),es1) /\
  values_have_types tvs vs /\ read_result cx tv' es1 = (INL (EL k vs),es1) /\
  post_value_type cenv e = EL k tys /\ post_value_type cenv e = expr_type e /\
  (~expr_has_effect e ==> ~expr_has_effect obj) ==>
  vv_post ctx func cenv cx e es sa sn s0 es1 tv'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) q
Proof
  strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[vv_post_def]) >>
  `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
  `vv_holds cenv cx (EL k tys) tv'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) es1 q` by
    (irule tuple_child_holds >> metis_tac[]) >>
  `vv_at cenv cx (EL k tys) sa sn es1 tv'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) q` by
    (irule tuple_child_placement >> metis_tac[]) >>
  gvs[vv_post_def] >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >> rpt strip_tac >>
  `~expr_has_effect obj` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
     impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >> simp[]) >>
  Cases_on `bvv` >>
  gvs[mk_ptr_def, vv_loc_def, vv_location_def, vv_operand_def] >>
  rename1 `LocatedValue t p` >>
  `t = TupleT tys` by
    (qpat_x_assum `vv_holds _ _ (TupleT tys) _ (LocatedValue _ _) _ _` mp_tac >>
     simp[vv_holds_def, is_bytestring_type_def] >> rpt strip_tac >> simp[]) >>
  gvs[] >> drule_all tuple_location_sizes >>
  disch_then (qspec_then `p.ptr_location` assume_tac) >>
  gvs[tuple_offset_def, is_slot_addressed_def] >>
  `oEL k tvs = SOME (EL k tvs)` by simp[oEL_THM] >>
  drule_all targetPlaceLiveTheory.nested_pop_live_tuple_element >>
  simp[tuple_prefix_slot_size_sum, MAP_TAKE]
QED
