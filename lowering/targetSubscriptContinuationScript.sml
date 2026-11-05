(* Consumer views for the typed write-side subscript continuation. *)
Theory targetSubscriptContinuation
Ancestors
  targetSubscriptMapping targetSubscriptStorage exprSimPopStorage exprSimHash
  targetPlaceLive vyperStoragePlaceProvenance vyperPlaceStoragePreservation
  vyperTyping exprLowering vyperTypeSystem vyperValue vyperStorage
  valueEncoding vyperMisc byte words list compileEnv

Theorem target_subscript_dynamic_key_view:
  hashmap_key_type (expr_type e) /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv key /\
  expr_post ctx func cenv cx e es sa sm s0 es' key op s ==>
  ?b bs. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
    encode_hashmap_key (expr_type e) key =
      word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
Proof
  strip_tac >> Cases_on `expr_type e` >>
  gvs[hashmap_key_type_def, is_bytestring_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
  gvs[hashmap_key_type_def, is_bytestring_type_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `key` >>
  gvs[value_has_type_def, is_bytestring_type_def]
  >- (drule hash_string_post_view >> simp[evaluate_type_def] >> strip_tac >>
      qexistsl_tac [`b`, `MAP (n2w o ORD) s'`] >>
      simp[encode_hashmap_key_def, n2w_o_ORD_eq, byteTheory.word_of_bytes_be_def]) >>
  drule hash_dynamic_post_view >> simp[evaluate_type_def] >> strip_tac >>
  qexistsl_tac [`b`, `l`] >>
  simp[encode_hashmap_key_def, byteTheory.word_of_bytes_be_def]
QED

Theorem target_subscript_storage_base_view:
  storage_layout_safe cx /\
  EVERY pure_expr (target_indices bt) /\
  eval_base_place cx bt es =
    (INL (PlaceR (StoragePlace tr slot tv)),mid) /\
  get_storage_backend cx tr es = (INL raw,es) ==>
  storage_read_live cx tr raw slot tv /\
  w2n slot + type_slot_size tv <= dimword(:256)
Proof
  strip_tac >>
  drule_all nested_pop_eval_base_live >>
  simp[nested_pop_result_live_def] >> strip_tac >>
  drule eval_base_place_region >>
  simp[storage_result_region_def] >> strip_tac >>
  simp[] >> Cases_on `type_slot_size tv = 0`
  >- simp[wordsTheory.w2n_lt, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `0 < type_slot_size tv` by decide_tac >>
  drule_all storage_place_region_numeric >> strip_tac >> decide_tac
QED
