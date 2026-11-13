(* Typed counted subscript continuation, joining the concrete suffix families. *)
Theory popNestedTargetSuffixMemory
Ancestors
  popNestedArrayCheckMemory popNestedMemoryArraySuffix popNestedStorageArraySuffix
  popNestedMappingSuffixMemory targetSubscriptContinuation targetSubscriptSplit
  targetSubscriptDecode targetSubscriptMemory targetSubscriptStorage
  targetPlaceSimDefs exprSimMemDefs loweringPosts exprSimDefs exprSimProps
  gasSummary gasContext fragGasMode fragExec exprLowering context compileEnv
  exprLoweringProps emitHelperProps emitHelper freshWrites
  vyperAST vyperInterpreter vyperValue vyperState vyperTypeSystem vyperTyping
  venomState venomInst words list finite_map vyperPlaceFrames
Libs
  pairLib

Theorem pop_nested_subscript_memory_normal_mem[local]:
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
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INL pv',es') ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety) op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule_all target_subscript_memory_compile >> strip_tac >> gvs[] >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    pop_nested_memory_array_suffix_mem >>
  disch_then (drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (ArrayT _ _) = _`)) >>
  disch_then (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  simp[] >>
  (impl_tac >- (rpt strip_tac >> drule_all pop_nested_array_check_ptr_path_mem >>
               strip_tac >> qexists_tac `t` >> simp[])) >>
  simp[]
QED

Theorem pop_nested_subscript_memory_error_mem[local]:
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
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INR err,es') ==>
  (?r. gas_marked_path T ctx func s 0 r /\ expr_exit (INR err) r) /\ es' = es
Proof
  strip_tac >> drule_all target_subscript_memory_compile >> strip_tac >> gvs[] >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    pop_nested_memory_array_error_suffix_mem >>
  disch_then (drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (ArrayT _ _) = _`)) >>
  disch_then (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  simp[] >>
  (impl_tac >- (rpt strip_tac >> drule_all pop_nested_array_check_ptr_abort_path_mem >>
               simp[])) >>
  strip_tac >> simp[] >>
  qexists_tac `Abort Revert_abort u` >> simp[expr_exit_def]
QED

Theorem pop_nested_subscript_storage_normal_mem[local]:
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
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INL pv',es') ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety) op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule_all target_subscript_storage_compile >> strip_tac >> gvs[] >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    pop_nested_storage_array_suffix_mem >>
  disch_then (drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  simp[] >>
  (impl_tac >- (rpt strip_tac >> drule_all pop_nested_array_check_ptr_path_mem >>
               strip_tac >> qexists_tac `t` >> simp[])) >>
  simp[]
QED

Theorem pop_nested_subscript_storage_error_mem[local]:
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
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved cenv sn /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\ (!l. ix <> Label l) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INR err,es') ==>
  (?r. gas_marked_path T ctx func s 0 r /\ expr_exit (INR err) r) /\ es' = es
Proof
  strip_tac >> drule_all target_subscript_storage_compile >> strip_tac >> gvs[] >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    pop_nested_storage_array_error_suffix_mem >>
  disch_then (drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  simp[] >>
  (impl_tac >- (rpt strip_tac >> drule_all pop_nested_array_check_ptr_abort_path_mem >>
               simp[])) >>
  strip_tac >> simp[] >>
  qexists_tac `Abort Revert_abort u` >> simp[expr_exit_def]
QED

Theorem pop_nested_subscript_mapping_scalar_normal_mem[local]:
  target_post ctx func cenv cx es0 sa sn s0 es (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb s /\
  ~is_bytestring_type kt /\ eval_operand ix s = SOME (encode_hashmap_key kt key) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es = (INL pv',es') ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 es sa s0 s /\
   eval_operand (FST rb) s = SOME slot /\
   (!x. FST rb = Var x ==> not_fresh_at sn x) /\
   FST (SND rb) = SOME (slot_loc tr) /\ SND (SND rb) = SOME (MapPT kt vt)` by
    (fs[target_post_def, wb_frame_def, place_ptr_rel_def, value_type_place_def] >>
     metis_tac[]) >>
  PairCases_on `rb` >> gvs[] >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  simp[target_subscript_suffix_mapping, comp_return_def] >> strip_tac >> gvs[] >>
  drule_all pop_nested_mapping_counted_suffix_mem >> strip_tac >> qexists_tac `t` >> simp[]
QED

Theorem pop_nested_subscript_mapping_dynamic_normal_mem[local]:
  target_post ctx func cenv cx es0 sa sn s0 es (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb s /\
  expr_type e = kt /\ hashmap_key_type kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv key /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_store_bound cx kt key ix s /\ alloca_history func s /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es = (INL pv',es') ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 es sa s0 s /\
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
  drule_at (Pat `compile_keccak256_key _ _ _ = _`)
    pop_nested_mapping_dynamic_typed_suffix_mem >>
  disch_then (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >> qexists_tac `t'` >> simp[]
QED

Theorem pop_nested_subscript_typed_normal_mem[local]:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es pv bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_sim_inv cenv cx env es /\
  expr_store_bound cx (expr_type e) key ix s /\ alloca_history func s /\
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
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
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
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] pop_nested_subscript_storage_normal_mem)) >>
              simp[] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] pop_nested_subscript_storage_normal_mem)) >>
          simp[] >> disch_then drule_all >> simp[])
      >- (gvs[place_ptr_rel_def] >>
          rename1 `subscript_vtype (Type aty) _ = _` >> Cases_on `aty` >>
          gvs[subscript_vtype_def, AllCaseEqs()] >>
          rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
          gvs[evaluate_type_def, AllCaseEqs()] >>
          drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] pop_nested_subscript_memory_normal_mem)) >>
              simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] pop_nested_subscript_memory_normal_mem)) >>
          simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
      gvs[place_ptr_rel_def]) >>
  gvs[place_ptr_rel_def, subscript_vtype_def, AllCaseEqs()] >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- (drule pop_nested_subscript_mapping_dynamic_normal_mem >> simp[] >>
      disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  drule_all target_subscript_scalar_key_view >> strip_tac >>
  drule_all pop_nested_subscript_mapping_scalar_normal_mem >> simp[]
QED

Theorem pop_nested_subscript_typed_error_mem[local]:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  well_formed_vtype (get_tenv cx) vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es pv bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_sim_inv cenv cx env es /\ alloca_history func s /\
  (!id path. pv = PlaceR (MemoryPlace id path) ==>
    ?entry av. lookup_scopes id es.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx es tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
       w2n (lookup_storage slot (get_storage cx es tr)) <= cnt)) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  extend_place cx pv (ValueSubscript key) es = (INR err,es') ==>
  (?r. gas_marked_path T ctx func s 0 r /\ expr_exit (INR err) r) /\ es' = es
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
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] pop_nested_subscript_storage_error_mem)) >>
              simp[] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] pop_nested_subscript_storage_error_mem)) >>
          simp[] >> disch_then drule_all >> simp[])
      >- (gvs[place_ptr_rel_def] >>
          rename1 `subscript_vtype (Type aty) _ = _` >> Cases_on `aty` >>
          gvs[subscript_vtype_def, AllCaseEqs()] >>
          rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
          gvs[evaluate_type_def, AllCaseEqs()] >>
          drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
          >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] pop_nested_subscript_memory_error_mem)) >>
              simp[evaluate_type_def] >> disch_then drule_all >> simp[]) >>
          drule (SRULE [] (Q.INST [`dyn` |-> `T`] pop_nested_subscript_memory_error_mem)) >>
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

Theorem pop_nested_subscript_typed_summary_mem:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  well_formed_vtype (get_tenv cx) vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es pv bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_sim_inv cenv cx env es /\
  expr_store_bound cx (expr_type e) key ix s /\ alloca_history func s /\
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
  (!x. FST op = Var x ==> not_fresh_at sb x) ==>
  gas_summary_at T (ctx,func) [] (extend_place cx pv (ValueSubscript key))
    (es,s)
    (\res es' u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next)
    (\res es' r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `extend_place cx pv (ValueSubscript key) es` >>
  rename1 `extend_place cx pv (ValueSubscript key) es = (result,es')` >>
  Cases_on `result`
  >- (drule_all pop_nested_subscript_typed_normal_mem >> strip_tac >>
      drule extend_place_state >> strip_tac >> gvs[] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INL x`, `es`, `OK u`] >>
      simp[gas_marked_exec_def, target_subscript_extend_gas_obs] >>
      fs[target_post_def] >>
      `locals_kept cenv es0 (es with gas_obs := []) s0 u <=>
       locals_kept cenv es0 es s0 u` by
        (rpt (pop_assum kall_tac) >> simp[locals_kept_def, popped_kept_def]) >>
      pop_assum (fn th => rewrite_tac[th]) >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all pop_nested_subscript_typed_error_mem >> strip_tac >> gvs[] >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es`, `r`] >>
  simp[gas_marked_exec_def, target_subscript_extend_gas_obs] >>
  qpat_x_assum `expr_exit (INR _) _` mp_tac >>
  Cases_on `y`
  >~ [`Error exc`]
  >- (Cases_on `exc` >> Cases_on `r` >>
      simp[oneline expr_exit_def, exit_result_def]) >>
  Cases_on `r` >> simp[oneline expr_exit_def, exit_result_def]
QED
