(* Consumer views for the typed write-side subscript continuation. *)
Theory targetSubscriptContinuation
Ancestors
  targetSubscriptMapping targetSubscriptStorage exprSimPopStorage exprSimHash
  targetPlaceLive vyperStoragePlaceProvenance vyperPlaceStoragePreservation
  vyperTyping exprLowering vyperTypeSystem vyperValue vyperStorage
  valueEncoding vyperMisc byte words list compileEnv
  exprLoweringProps stmtLoweringMono fragExec

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

(* The compiler continuation after the base_op and index intervals. *)
Definition target_subscript_suffix_def:
  target_subscript_suffix cenv e rb ix =
    (case SND (SND rb) of
       SOME (MapPT kt vt) =>
         comp_bind (if is_bytestring_type kt then compile_keccak256_key ix F
                    else comp_return ix)
           (\hashed. comp_bind (compile_mapping_subscript (FST rb) hashed)
             (\slot. comp_return (slot, FST (SND rb), SOME (value_type_place vt))))
     | _ =>
         let loc = (case FST (SND rb) of SOME l => l | NONE => LocMemory) in
         let dyn = (case SND (SND rb) of
                      SOME (ValPT (ArrayT _ (Dynamic _))) => T | _ => F) in
         let ety = (case SND (SND rb) of
                      SOME (ValPT (ArrayT t _)) => t | _ => BaseT (UintT 256)) in
         let cnt = (case SND (SND rb) of
                      SOME (ValPT (ArrayT _ (Fixed n))) => n | _ => 0) in
         comp_bind (compile_array_subscript (FST rb) ix dyn cnt
           (word_scale loc) (elem_size_in_location cenv loc ety)
           (is_signed_type (expr_type e))
           (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc))
           (\ptr. comp_return (ptr, FST (SND rb), SOME (ValPT ety))))
End

Theorem target_subscript_compile_decompose:
  compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (op,sb) ==>
  ?rb sm ix sn.
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
    target_subscript_suffix cenv e rb ix sn = (op,sb)
Proof
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e r` >>
  Cases_on `SND (SND q)`
  >- simp[Once compile_get_target_ptr_def, target_subscript_suffix_def,
          comp_bind_def, comp_return_def] >>
  rename1 `SND (SND q) = SOME pt` >> Cases_on `pt` >>
  simp[Once compile_get_target_ptr_def, target_subscript_suffix_def,
       comp_bind_def, comp_return_def]
QED

Theorem target_subscript_suffix_array:
  target_subscript_suffix cenv e (base_op,SOME loc,SOME (ValPT (ArrayT ety bd))) ix sn =
    (op,sb) <=>
  ?ptr. compile_array_subscript base_op ix
    (case bd of Dynamic _ => T | _ => F)
    (case bd of Fixed n => n | _ => 0)
    (word_scale loc) (elem_size_in_location cenv loc ety)
    (is_signed_type (expr_type e))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) sn = (ptr,sb) /\
    op = (ptr,SOME loc,SOME (ValPT ety))
Proof
  Cases_on `bd` >>
  simp[target_subscript_suffix_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> metis_tac[]
QED

Theorem target_subscript_suffix_mapping:
  target_subscript_suffix cenv e (base_op,loc,SOME (MapPT kt vt)) ix sn = (op,sb) <=>
  ?hashed sh slot.
    (if is_bytestring_type kt then compile_keccak256_key ix F
     else comp_return ix) sn = (hashed,sh) /\
    compile_mapping_subscript base_op hashed sh = (slot,sb) /\
    op = (slot,loc,SOME (value_type_place vt))
Proof
  simp[target_subscript_suffix_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> metis_tac[]
QED

Theorem ci_mono_target_subscript_suffix:
  !cenv e rb ix sn.
    ci_mono sn (SND (target_subscript_suffix cenv e rb ix sn))
Proof
  rpt gen_tac >> Cases_on `SND (SND rb)`
  >- (simp[target_subscript_suffix_def] >> irule ci_mono_bind >>
      simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load,
           ci_mono_comp_return]) >>
  rename1 `SND (SND rb) = SOME pt` >> Cases_on `pt`
  >- (simp[target_subscript_suffix_def] >> irule ci_mono_bind >> conj_tac
      >- (rpt gen_tac >> BETA_TAC >> irule ci_mono_bind >>
          simp[ci_mono_compile_mapping_subscript, ci_mono_comp_return]) >>
      gen_tac >> IF_CASES_TAC >>
      simp[ci_mono_compile_keccak256_key, ci_mono_comp_return]) >>
  simp[target_subscript_suffix_def] >> irule ci_mono_bind >>
  simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load,
       ci_mono_comp_return]
QED

Theorem target_subscript_compile_intervals:
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) ==>
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`bt`,`cenv`,`sa`] ci_mono_compile_get_target_ptr) >>
  `ci_mono sm (SND (lower_value compile_expr cenv (expr_type e) e sm))` by
    (irule ci_mono_lower_value_cfn >> simp[ci_mono_compile_expr_sa]) >>
  mp_tac (Q.SPECL [`cenv`,`e`,`rb`,`ix`,`sn`] ci_mono_target_subscript_suffix) >>
  gvs[]
QED

Theorem target_subscript_interval_code:
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sa sb func ==>
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn sb func
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all fn_has_code_split >> simp[]
QED
