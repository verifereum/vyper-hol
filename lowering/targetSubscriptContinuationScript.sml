(* Consumer views for the typed write-side subscript continuation. *)
Theory targetSubscriptContinuation
Ancestors
  targetSubscriptMapping targetSubscriptStorage exprSimPopStorage exprSimHash
  targetPlaceLive vyperStoragePlaceProvenance vyperPlaceStoragePreservation
  vyperTyping exprLowering vyperTypeSystem vyperValue vyperStorage
  valueEncoding vyperMisc byte words list compileEnv
  exprLoweringProps stmtLoweringMono fragExec
  loweringPosts vyperState vyperInterpreter targetSubscriptMemory exprSimDefs
  exprSimBinopFrag

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

(* A dynamic array's declared capacity is not its compiler static count. *)
Theorem target_subscript_dynamic_count_irrelevant:
  compile_array_subscript base_op ix T n ws esz sgn loader =
  compile_array_subscript base_op ix T 0 ws esz sgn loader
Proof
  simp[compile_array_subscript_def]
QED


Theorem target_subscript_memory_compile:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) ==>
  ?dst. compile_array_subscript (FST rb) ix dyn cnt 32 (type_memory_bytes cenv ety)
    (is_signed_type (expr_type e))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sn = (dst,sb) /\
    op = (dst,SOME LocMemory,SOME (ValPT ety))
Proof
  strip_tac >>
  `FST (SND rb) = SOME LocMemory /\
   SND (SND rb) = SOME (ValPT (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))` by
    gvs[target_post_def, place_ptr_rel_def, value_type_place_def] >>
  PairCases_on `rb` >> gvs[] >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[target_subscript_suffix_array] >> Cases_on `dyn` >>
  simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def,
       target_subscript_dynamic_count_irrelevant]
QED

Theorem target_subscript_memory_normal:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
  value_has_type itv (IntV i) /\ eval_operand ix s = SOME (i2w i) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INL pv',es') ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety) op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all target_subscript_memory_compile >> strip_tac >> gvs[] >>
  drule target_memory_array_suffix >> simp[] >> disch_then drule_all >> simp[]
QED

Theorem target_subscript_memory_error:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
  value_has_type itv (IntV i) /\ eval_operand ix s = SOME (i2w i) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INR err,es') ==>
  (?r. gas_marked_path F ctx func s 0 r /\ expr_exit (INR err) r) /\ es' = es
Proof
  strip_tac >> drule_all target_subscript_memory_compile >> strip_tac >> gvs[] >>
  drule target_memory_array_error_suffix >> simp[] >> disch_then drule_all >>
  strip_tac >> simp[] >> qexists `Abort Revert_abort u` >> simp[expr_exit_def]
QED

Theorem target_subscript_storage_compile:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) ==>
  ?dst. compile_array_subscript (FST rb) ix dyn cnt 1 (type_slot_size etv)
    (is_signed_type (expr_type e))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sn = (dst,sb) /\
    op = (dst,SOME (slot_loc tr),SOME (ValPT ety))
Proof
  strip_tac >>
  `FST (SND rb) = SOME (slot_loc tr) /\
   SND (SND rb) = SOME (ValPT (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) /\
   evaluate_type (get_tenv cx) ety = SOME etv` by
    gvs[target_post_def, place_ptr_rel_def, value_type_place_def,
        evaluate_type_def, AllCaseEqs()] >>
  drule_all pop_storage_element_size >> disch_then (qspec_then `tr` assume_tac) >>
  PairCases_on `rb` >> gvs[] >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[target_subscript_suffix_array] >> Cases_on `dyn` >>
  simp[slot_loc_def, target_subscript_dynamic_count_irrelevant] >>
  Cases_on `tr` >> gvs[word_scale_def, slot_loc_def]
QED

Theorem target_subscript_storage_normal:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  storage_read_live cx tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
  value_has_type itv (IntV i) /\ eval_operand ix s = SOME (i2w i) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INL pv',es') ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety) op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all target_subscript_storage_compile >> strip_tac >> gvs[] >>
  drule target_storage_array_suffix >> simp[] >> disch_then drule_all >> simp[]
QED

Theorem target_subscript_storage_error:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  storage_read_live cx tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
  value_has_type itv (IntV i) /\ eval_operand ix s = SOME (i2w i) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ local_ptrs_reserved cenv sn /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\ (!l. ix <> Label l) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INR err,es') ==>
  (?r. gas_marked_path F ctx func s 0 r /\ expr_exit (INR err) r) /\ es' = es
Proof
  strip_tac >> drule_all target_subscript_storage_compile >> strip_tac >> gvs[] >>
  drule target_storage_array_error_suffix >> simp[] >> disch_then drule_all >>
  strip_tac >> simp[] >> qexists `Abort Revert_abort u` >> simp[expr_exit_def]
QED

Theorem target_subscript_mapping_scalar_normal:
  target_post ctx func cenv cx es0 sa sn s0 es (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb s /\
  ~is_bytestring_type kt /\ eval_operand ix s = SOME (encode_hashmap_key kt key) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es = (INL pv',es') ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
   eval_operand (FST rb) s = SOME slot /\
   (!x. FST rb = Var x ==> not_fresh_at sn x) /\
   FST (SND rb) = SOME (slot_loc tr) /\ SND (SND rb) = SOME (MapPT kt vt)` by
    (fs[target_post_def, wb_frame_def, place_ptr_rel_def, value_type_place_def] >>
     metis_tac[]) >>
  PairCases_on `rb` >> gvs[] >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  simp[target_subscript_suffix_mapping, comp_return_def] >> strip_tac >> gvs[] >>
  drule_all target_mapping_counted_suffix >> strip_tac >> qexists `t` >> simp[]
QED

Theorem target_subscript_mapping_dynamic_normal:
  target_post ctx func cenv cx es0 sa sn s0 es (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb s /\
  expr_type e = kt /\ hashmap_key_type kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv key /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es = (INL pv',es') ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> gvs[] >>
  drule_all target_subscript_dynamic_key_view >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
   eval_operand (FST rb) s = SOME slot /\
   (!x. FST rb = Var x ==> not_fresh_at sn x) /\
   FST (SND rb) = SOME (slot_loc tr) /\ SND (SND rb) = SOME (MapPT (expr_type e) vt)` by
    (fs[target_post_def, wb_frame_def, place_ptr_rel_def, value_type_place_def] >>
     metis_tac[]) >>
  PairCases_on `rb` >> gvs[] >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  simp[target_subscript_suffix_mapping] >> strip_tac >> gvs[] >>
  `ci_mono sn sh /\ ci_mono sh sb` by
    (mp_tac (Q.SPECL [`ix`,`F`,`sn`] ci_mono_compile_keccak256_key) >>
     mp_tac (Q.SPECL [`rb0`,`hashed`,`sh`] ci_mono_compile_mapping_subscript) >>
     simp[]) >>
  `fn_has_code sn sh func /\ fn_has_code sh sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  drule_all target_mapping_dynamic_counted_suffix >> strip_tac >> qexists `t'` >> simp[]
QED

Theorem target_subscript_int_index_view:
  is_int_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv key /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s ==>
  ?i. key = IntV i /\ eval_operand ix s = SOME (i2w i)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[is_int_type_def] >>
     rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  drule_all int_type_value >> strip_tac >>
  `expr_val_rel cx (expr_type e) key ix s` by fs[expr_post_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[] >> Cases_on `expr_type e` >> gvs[is_int_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, expr_val_rel_def,
      is_word_type_def, typed_val_to_w256_def, val_to_w256_def]
QED

Theorem target_subscript_scalar_key_view:
  hashmap_key_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv key /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s ==>
  eval_operand ix s = SOME (encode_hashmap_key (expr_type e) key)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[hashmap_key_type_def, is_word_type_def] >>
     rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
     gvs[hashmap_key_type_def, is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def, evaluate_type_def,
         AllCaseEqs()]) >>
  irule target_mapping_scalar_operand >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`cx`, `tv`] >> fs[expr_post_def]
QED

Theorem target_subscript_typed_normal:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es pv bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_sim_inv cenv cx env es /\
  (!id path. pv = PlaceR (MemoryPlace id path) ==>
    ?entry av. lookup_scopes id es.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx es tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
       w2n (lookup_storage slot (get_storage cx es tr)) <= cnt)) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx pv (ValueSubscript key) es = (INL pv',es') ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?w. place_ptr_rel cenv cx s pv w (FST (SND rb)) bvt` by
    (fs[target_post_def] >> metis_tac[]) >>
  Cases_on `pv`
  >- gvs[place_ptr_rel_def]
  >- (rename1 `PlaceR pl` >> Cases_on `pl`
      >- (gvs[place_ptr_rel_def] >>
          rename1 `subscript_vtype (Type aty) _ = _` >> Cases_on `aty` >>
          gvs[subscript_vtype_def, AllCaseEqs()] >>
          rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
          gvs[evaluate_type_def, AllCaseEqs()] >>
          drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] target_subscript_storage_normal)) >> simp[] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] target_subscript_storage_normal)) >> simp[] >> disch_then drule_all >> simp[])
      >- (gvs[place_ptr_rel_def] >>
          rename1 `subscript_vtype (Type aty) _ = _` >> Cases_on `aty` >>
          gvs[subscript_vtype_def, AllCaseEqs()] >>
          rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
          gvs[evaluate_type_def, AllCaseEqs()] >>
          drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] target_subscript_memory_normal)) >>
              simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] target_subscript_memory_normal)) >>
          simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
      gvs[place_ptr_rel_def]) >>
  gvs[place_ptr_rel_def, subscript_vtype_def, AllCaseEqs()] >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- (drule target_subscript_mapping_dynamic_normal >> simp[] >>
      disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  drule_all target_subscript_scalar_key_view >> strip_tac >>
  drule_all target_subscript_mapping_scalar_normal >> simp[]
QED

Theorem target_subscript_typed_error:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  well_formed_vtype (get_tenv cx) vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es pv bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_sim_inv cenv cx env es /\
  (!id path. pv = PlaceR (MemoryPlace id path) ==>
    ?entry av. lookup_scopes id es.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx es tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
       w2n (lookup_storage slot (get_storage cx es tr)) <= cnt)) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx pv (ValueSubscript key) es = (INR err,es') ==>
  (?r. gas_marked_path F ctx func s 0 r /\ expr_exit (INR err) r) /\ es' = es
Proof
  strip_tac >>
  `?w. place_ptr_rel cenv cx s pv w (FST (SND rb)) bvt` by
    (fs[target_post_def] >> metis_tac[]) >>
  Cases_on `pv`
  >- gvs[place_ptr_rel_def]
  >- (rename1 `PlaceR pl` >> Cases_on `pl`
      >- (gvs[place_ptr_rel_def] >>
          rename1 `subscript_vtype (Type aty) _ = _` >> Cases_on `aty` >>
          gvs[subscript_vtype_def, AllCaseEqs()] >>
          rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
          gvs[evaluate_type_def, AllCaseEqs()] >>
          drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] target_subscript_storage_error)) >>
              simp[] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] target_subscript_storage_error)) >>
          simp[] >> disch_then drule_all >> simp[])
      >- (gvs[place_ptr_rel_def] >>
          rename1 `subscript_vtype (Type aty) _ = _` >> Cases_on `aty` >>
          gvs[subscript_vtype_def, AllCaseEqs()] >>
          rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
          gvs[evaluate_type_def, AllCaseEqs()] >>
          drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] target_subscript_memory_error)) >>
              simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] target_subscript_memory_error)) >>
          simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
      gvs[place_ptr_rel_def]) >>
  gvs[place_ptr_rel_def, subscript_vtype_def, AllCaseEqs()] >>
  rename1 `well_formed_vtype _ outvt` >> Cases_on `outvt` >>
  gvs[well_formed_vtype_def, well_formed_type_def,
      extend_place_def, bind_def, lift_option_type_def, return_def,
      raise_def, AllCaseEqs()] >>
  rename1 `IS_SOME (evaluate_type _ ty)` >>
  Cases_on `evaluate_type (get_tenv cx) ty` >> gvs[return_def]
QED
