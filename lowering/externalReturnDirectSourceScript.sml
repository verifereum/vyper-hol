(* Expression provenance to a live ABI encoder input. *)
Theory externalReturnDirectSource
Ancestors
  externalReturnBounds externalReturnLiveWindowResources loweringPosts
  exprLowering compileEnv vyperTypeABI vyperTyping vyperValue venomState
  externalReturnWindowResources abiBoundaryChecks valueEncoding vyperABI
  abiEncoderWindowSource abiEncoderProps contractABI list arithmetic
  valueCopyBytes vyperTypeArgFits externalNormalizePremises

Theorem direct_return_layout_split:
  (lowered_value_type ce e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  ~is_word_type ret /\
  ~(~is_word_type ret /\
    ~(is_bytestring_type (lowered_value_type ce e) /\ is_bytestring_type ret) /\
    lowered_value_type ce e <> ret) ==>
  expr_type e = ret \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type ret
Proof
  rpt strip_tac >> metis_tac[]
QED

Theorem typed_expression_live_window:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  value_has_type tv v /\ 0 < val_footprint tv v /\
  abi_enc_plan (get_tenv cx) ty ei ==>
  ?p at rv cap.
    eval_operand op s = SOME p /\ cap = val_footprint tv v /\
    w2n p + cap <= s.vs_alloca_next /\
    abi_encoder_window_input ei at rv (w2n p) cap s.vs_memory /\
    LENGTH (enc at rv) <= vyper_abi_size_bound (get_tenv cx) ty
Proof
  strip_tac >>
  drule_all expr_val_at_frontier >> strip_tac >> gvs[] >>
  `?av. vyper_to_abi (get_tenv cx) ty v = SOME av` by
    (irule (cj 1 vyper_to_abi_total) >> metis_tac[]) >>
  `val_in_memory tv v (w2n w) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  drule_all return_plan_live_window_bounded >> strip_tac >>
  qexistsl_tac [`at`, `rv`] >> gvs[]
QED

Theorem return_nominal_singleton_window:
  abi_enc_plan env (TupleT [ty]) ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v p mem /\
  p + type_memory_size tv <= frontier ==>
  ?at rv. abi_encoder_window_input ei at rv p (type_memory_size tv) mem /\
    p + type_memory_size tv <= frontier /\
    LENGTH (enc at rv) <= vyper_abi_size_bound env (TupleT [ty])
Proof
  strip_tac >>
  `evaluate_type env (TupleT [ty]) = SOME (TupleTV [tv])` by
    (drule (cj 1 evaluate_type_well_formed) >> strip_tac >>
     drule well_formed_type_value_slot_size >>
     simp[evaluate_type_def, type_slot_size_def]) >>
  `value_has_type (TupleTV [tv]) (ArrayV (TupleV [v]))` by
    simp[value_has_type_def] >>
  `?av. vyper_to_abi env (TupleT [ty]) (ArrayV (TupleV [v])) = SOME av` by
    (irule (cj 1 vyper_to_abi_total) >> metis_tac[]) >>
  `val_in_memory (TupleTV [tv]) (ArrayV (TupleV [v])) p mem` by
    simp[val_in_memory_singleton_tuple] >>
  drule_all return_plan_nominal_source_window >> strip_tac >>
  qexistsl_tac [`at`, `rv`] >> gvs[type_memory_size_def]
QED

Theorem nominal_return_expression_window:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  value_has_type tv v /\ 0 < val_footprint tv v /\
  val_footprint tv v = type_memory_size tv /\
  abi_enc_plan (get_tenv cx) (if wrap then TupleT [ty] else ty) ei ==>
  ?p at rv cap.
    eval_operand op s = SOME p /\ cap = val_footprint tv v /\
    w2n p + cap <= s.vs_alloca_next /\
    abi_encoder_window_input ei at rv (w2n p) cap s.vs_memory /\
    LENGTH (enc at rv) <=
      vyper_abi_size_bound (get_tenv cx) (if wrap then TupleT [ty] else ty)
Proof
  strip_tac >> Cases_on `wrap` >> gvs[]
  >- (drule_all expr_val_at_frontier >> strip_tac >> gvs[] >>
      `val_in_memory tv v (w2n w) s.vs_memory` by gvs[expr_val_rel_def] >>
      `w2n w + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
      drule_all return_nominal_singleton_window >> strip_tac >>
      qexistsl_tac [`at`, `rv`] >> simp[]) >>
  `0 < val_footprint tv v` by gvs[] >>
  drule_all typed_expression_live_window >> simp[]
QED

Theorem return_bytes_typed_singleton_window:
  is_bytestring_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v p mem /\
  p + val_footprint tv v <= frontier /\
  abi_enc_plan env (TupleT [ty]) ei ==>
  ?at rv cap. cap <= val_footprint tv v /\ p + cap <= frontier /\
    abi_encoder_window_input ei at rv p cap mem /\
    LENGTH (enc at rv) <= vyper_abi_size_bound env (TupleT [ty])
Proof
  strip_tac >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >> suspend "bytes") >>
  suspend "string"
QED

Resume return_bytes_typed_singleton_window[bytes]:
  gvs[evaluate_type_def] >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  ntac 3 (simp[Once abi_enc_plan_cases, vyper_to_abi_type_def,
    vyper_base_to_abi_type_def, is_dynamic_def,
    is_word_type_def, evaluate_type_def]) >> strip_tac >>
  gvs[Once abi_enc_plan_cases] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `vyperValue$BytesV bs` >>
  `evaluate_type env (BaseT (BytesT (Dynamic n))) =
     SOME (BaseTV (BytesT (Dynamic n)))` by simp[evaluate_type_def] >>
  `vyper_to_abi env (BaseT (BytesT (Dynamic n))) (vyperValue$BytesV bs) =
     SOME (contractABI$BytesV bs)` by simp[vyper_to_abi_def] >>
  `value_has_type (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs)` by
    simp[value_has_type_def] >>
  drule_all abi_encoder_window_bytes_singleton_source >> strip_tac >>
  qexistsl_tac [`Tuple [Bytes NONE]`, `ListV [contractABI$BytesV bs]`, `32 + LENGTH bs`] >>
  simp[] >>
  reverse conj_tac >- suspend "bytes_bound" >>
  mp_tac abi_encoder_window_bytes_footprint >> decide_tac
QED

Resume return_bytes_typed_singleton_window[string]:
  gvs[evaluate_type_def] >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  ntac 4 (simp[Once abi_enc_plan_cases, vyper_to_abi_type_def,
    vyper_base_to_abi_type_def, is_dynamic_def,
    is_word_type_def, evaluate_type_def]) >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >> rename1 `StringV str` >>
  `evaluate_type env (BaseT (StringT n)) = SOME (BaseTV (StringT n))` by
    simp[evaluate_type_def] >>
  `vyper_to_abi env (BaseT (StringT n)) (StringV str) =
     SOME (contractABI$BytesV (MAP n2w_o_ORD str))` by simp[vyper_to_abi_def] >>
  `value_has_type (BaseTV (StringT n)) (StringV str)` by simp[value_has_type_def] >>
  drule_all abi_encoder_window_string_singleton_source >> strip_tac >>
  qexistsl_tac [`Tuple [String]`, `ListV [contractABI$BytesV (MAP n2w_o_ORD str)]`,
                `32 + LENGTH str`] >> simp[] >>
  reverse conj_tac >- suspend "string_bound" >>
  mp_tac abi_encoder_window_string_footprint >> decide_tac
QED

Resume return_bytes_typed_singleton_window[bytes_bound]:
  conj_tac
  >- (mp_tac abi_encoder_window_bytes_footprint >> decide_tac) >>
  `evaluate_type env (TupleT [BaseT (BytesT (Dynamic n))]) =
     SOME (TupleTV [BaseTV (BytesT (Dynamic n))])` by
    (fs[type_slot_size_def] >> simp[evaluate_type_def, type_slot_size_def]) >>
  `value_has_type (TupleTV [BaseTV (BytesT (Dynamic n))])
     (ArrayV (TupleV [vyperValue$BytesV bs]))` by simp[value_has_type_def] >>
  `vyper_to_abi env (TupleT [BaseT (BytesT (Dynamic n))])
     (ArrayV (TupleV [vyperValue$BytesV bs])) =
     SOME (ListV [contractABI$BytesV bs])` by simp[vyper_to_abi_def] >>
  drule_all (cj 1 vyper_to_abi_enc_length_bound) >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def]
QED

Resume return_bytes_typed_singleton_window[string_bound]:
  conj_tac
  >- (mp_tac abi_encoder_window_string_footprint >> decide_tac) >>
  conj_tac >- (fs[] >> metis_tac[ADD_COMM]) >>
  `evaluate_type env (TupleT [BaseT (StringT n)]) =
     SOME (TupleTV [BaseTV (StringT n)])` by
    (fs[type_slot_size_def] >> simp[evaluate_type_def, type_slot_size_def]) >>
  `value_has_type (TupleTV [BaseTV (StringT n)])
     (ArrayV (TupleV [StringV str]))` by simp[value_has_type_def] >>
  `vyper_to_abi env (TupleT [BaseT (StringT n)])
     (ArrayV (TupleV [StringV str])) =
     SOME (ListV [contractABI$BytesV (MAP n2w_o_ORD str)])` by simp[vyper_to_abi_def] >>
  drule_all (cj 1 vyper_to_abi_enc_length_bound) >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def]
QED

Finalise return_bytes_typed_singleton_window

Theorem bytes_return_expression_window:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  0 < val_footprint tv v /\
  is_bytestring_type ty /\ is_bytestring_type ret /\
  type_widens_to (get_tenv cx) ty ret /\
  abi_enc_plan (get_tenv cx) (if wrap then TupleT [ret] else ret) ei ==>
  ?p at rv cap.
    eval_operand op s = SOME p /\ cap <= val_footprint tv v /\
    w2n p + cap <= s.vs_alloca_next /\
    abi_encoder_window_input ei at rv (w2n p) cap s.vs_memory /\
    LENGTH (enc at rv) <=
      vyper_abi_size_bound (get_tenv cx) (if wrap then TupleT [ret] else ret)
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  drule_all expr_val_at_frontier >> strip_tac >> gvs[] >>
  `val_in_memory tv v (w2n w) s.vs_memory` by gvs[expr_val_rel_def] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  `val_in_memory tu v (w2n w) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_footprint tu v = val_footprint tv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `w2n w + val_footprint tu v <= s.vs_alloca_next` by simp[] >>
  Cases_on `wrap` >> fs[] >>
  `w2n w + val_footprint tu v <= s.vs_alloca_next` by simp[]
  >- (drule_all return_bytes_typed_singleton_window >> strip_tac >>
      qexistsl_tac [`at`, `rv`, `cap`] >> simp[]) >>
  `?av. vyper_to_abi (get_tenv cx) ret v = SOME av` by
    (irule (cj 1 vyper_to_abi_total) >> metis_tac[]) >>
  drule_all return_plan_live_window_bounded >> strip_tac >>
  qexistsl_tac [`at`, `rv`, `cap`] >> simp[]
QED

Theorem direct_return_expression_window:
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa sb es v op s /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  0 < val_footprint tv v /\ ~is_word_type ret /\
  (ty = ret \/ is_bytestring_type ty /\ is_bytestring_type ret) /\
  type_widens_to (get_tenv cx) ty ret /\
  abi_enc_plan (get_tenv cx) (if wrap then TupleT [ret] else ret) ei ==>
  ?p at rv cap.
    eval_operand op s = SOME p /\ cap <= val_footprint tv v /\
    w2n p + cap <= s.vs_alloca_next /\
    abi_encoder_window_input ei at rv (w2n p) cap s.vs_memory /\
    LENGTH (enc at rv) <=
      vyper_abi_size_bound (get_tenv cx) (if wrap then TupleT [ret] else ret)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_bytestring_type ty`
  >- (`is_bytestring_type ret` by metis_tac[] >>
      drule_all bytes_return_expression_window >> simp[]) >>
  `ty = ret` by metis_tac[] >> gvs[] >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[normalize_nonbytes_footprint] >>
  drule_all nominal_return_expression_window >> strip_tac >>
  qexistsl_tac [`p`, `at`, `rv`, `cap`] >> simp[]
QED
