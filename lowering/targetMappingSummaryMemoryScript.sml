(* Typed counted mapping target continuations. *)
Theory targetMappingSummaryMemory
Ancestors
  targetMappingSuffixMemory targetSubscriptContinuation targetSubscriptSplit
  bodyMemBiKeccakBounds gasSummary gasOutcome targetPlaceSimDefs fragExec
  exprSimDefs exprSimHyps exprLowering exprLoweringProps loweringPosts
  loweringStateRelDefs compileEnv vyperTypeSystem vyperValue vyperInterpreter
  valueEncoding byte words list finite_map vyperTyping vyperStorage vyperMisc vyperState
Libs
  pairLib

Theorem target_mapping_key_bounds_mem[local]:
  hashmap_key_type (expr_type e) /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv key /\
  expr_post ctx func cenv cx e es sa sm s0 es' key op s /\
  expr_store_bound cx (expr_type e) key op s ==>
  ?b bs. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
    b+32 <= s.vs_alloca_next /\
    (bs = [] \/ b+32+LENGTH bs <= s.vs_alloca_next) /\
    encode_hashmap_key (expr_type e) key =
      word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
Proof
  strip_tac >> Cases_on `expr_type e` >>
  gvs[hashmap_key_type_def, is_bytestring_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
  gvs[hashmap_key_type_def, is_bytestring_type_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `key` >>
  gvs[value_has_type_def, is_bytestring_type_def]
  >- (drule keccak_string_post_bounds >> simp[evaluate_type_def] >>
      strip_tac >>
      qexistsl [`b`, `MAP (n2w o ORD) s'`] >>
      simp[encode_hashmap_key_def, n2w_o_ORD_eq, byteTheory.word_of_bytes_be_def] >>
      gvs[] >> decide_tac) >>
  drule keccak_dynamic_post_bounds >> simp[evaluate_type_def] >>
  strip_tac >> qexistsl [`b`, `l`] >>
  simp[encode_hashmap_key_def, byteTheory.word_of_bytes_be_def] >>
  gvs[] >> decide_tac
QED

Theorem target_mapping_scalar_normal_mem[local]:
  target_post ctx func cenv cx es0 sa sn s0 es (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb s /\
  ~is_bytestring_type kt /\ ~block_is_terminated sn /\
  eval_operand ix s = SOME (encode_hashmap_key kt key) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func s /\
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
  drule_all target_mapping_suffix_mem >> strip_tac >> qexists `t` >> simp[]
QED

Theorem target_mapping_dynamic_normal_mem[local]:
  target_post ctx func cenv cx es0 sa sn s0 es (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb s /\
  expr_type e = kt /\ hashmap_key_type kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv key /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_store_bound cx (expr_type e) key ix s /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func s /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es = (INL pv',es') ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> gvs[] >>
  drule_all target_mapping_key_bounds_mem >> strip_tac >>
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
     mp_tac (Q.SPECL [`rb0`,`hashed`,`sh`] ci_mono_compile_mapping_subscript) >> simp[]) >>
  `fn_has_code sn sh func /\ fn_has_code sh sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `?u. gas_marked_path T ctx func s 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    target_post ctx func cenv cx es0 sa sb s0 es' pv' vt
      (slot',SOME (slot_loc tr),SOME (value_type_place vt)) u /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next` suffices_by metis_tac[] >>
  irule target_mapping_dynamic_suffix_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_keccak256_key _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `encode_hashmap_key _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_mapping_subscript _ _ _ = _`)) >>
  qexists `b` >> simp[] >> decide_tac
QED

Theorem target_mapping_typed_summary_mem:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  well_formed_vtype (get_tenv cx) vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es (HashMapRef tr slot kt vty) bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_store_bound cx (expr_type e) key ix s /\ expr_sim_inv cenv cx env es /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sn /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (extend_place cx (HashMapRef tr slot kt vty) (ValueSubscript key)) (es,s)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es0 sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `?w. place_ptr_rel cenv cx s (HashMapRef tr slot kt vty) w (FST (SND rb)) bvt` by
    (fs[target_post_def] >> metis_tac[]) >>
  gvs[place_ptr_rel_def, subscript_vtype_def, AllCaseEqs()] >>
  `?pv'. extend_place cx (HashMapRef tr slot (expr_type e) vt) (ValueSubscript key) es = (INL pv',es)` by
    (Cases_on `vt` >>
     gvs[well_formed_vtype_def, well_formed_type_def,
       extend_place_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >>
     rename1 `IS_SOME (evaluate_type _ ty)` >>
     Cases_on `evaluate_type (get_tenv cx) ty` >> gvs[return_def]) >>
  `?u. gas_marked_path T ctx func s 0 (OK u) /\
    target_post ctx func cenv cx es0 sa sb s0 es pv' vt op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next` by
    (Cases_on `is_bytestring_type (expr_type e)`
     >- (drule (SRULE [] (Q.INST [`kt` |-> `expr_type e`] target_mapping_dynamic_normal_mem)) >>
         simp[] >> disch_then drule_all >> simp[]) >>
     drule_all target_subscript_scalar_key_view >> strip_tac >>
     drule_all target_mapping_scalar_normal_mem >> simp[]) >>
  irule target_subscript_extend_summary_normal >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[target_post_def, locals_kept_def, popped_kept_def] >> metis_tac[]
QED

