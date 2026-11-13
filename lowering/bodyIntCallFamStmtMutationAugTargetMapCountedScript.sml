(* Counted mapping-target suffixes with the joint continuation. *)
Theory bodyIntCallFamStmtMutationAugTargetMapCounted
Ancestors
  bodyIntCallFamStmtMutationAugTargetMappingFinish
  bodyIntCallFamStmtMutationAugTargetPrehash bodyIntCallJointAggCore
  targetSubscriptContinuation targetSubscriptMapping
  bodyIntCallJointContract exprLoweringProps compileEnv loweringPosts
  stmtSimAugAssignPlaceMemory exprSimMapKey loweringShapeRules byte
  pair freshWrites fragGasMode

Theorem intcall_target_mapping_suffix:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es0 sa s0 /\
  intcall_expr_cont fp ce env es0 sa s0 es sn s /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  compile_mapping_subscript base_op ix sn = (dst,sb) /\
  fn_has_code sn sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. base_op = Var x \/ ix = Var x ==> not_fresh_at sn x) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  eval_operand base_op s = SOME slot /\
  eval_operand ix s = SOME (encode_hashmap_key kt key) /\
  extend_place fp.jc_cx (HashMapRef tr slot kt vt) (ValueSubscript key) es =
    (INL pv,es') ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 es' pv vt
        (dst,SOME (slot_loc tr),SOME (value_type_place vt)) u /\
      intcall_expr_cont fp ce env es0 sa s0 es' sb u
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sn s /\ ~s.vs_halted /\
   s.vs_current_bb = sn.cs_current_bb /\
   s.vs_inst_idx = LENGTH sn.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_at (Pat `compile_mapping_subscript _ _ _ = _`) intcall_mapping_suffix >>
  disch_then drule_all >> strip_tac >>
  `es' = es` by metis_tac[target_mapping_extend_place] >> gvs[] >>
  `intcall_expr_cont fp ce env es0 sa s0 es sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`es`, `sn`, `s`] >> simp[]) >>
  qexists_tac `u` >> simp[] >> irule target_mapping_post >>
  goal_assum (drule_at Any) >>
  fs[bodyIntCallJointAggCoreTheory.intcall_expr_cont_frame, intcall_expr_res_def] >>
  metis_tac[]
QED

Theorem intcall_target_mapping_dynamic_suffix:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es0 sa s0 /\
  intcall_expr_cont fp ce env es0 sa s0 es sn s /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  expr_type e = kt /\ hashmap_key_type kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv fp.jc_cx) kt = SOME tv /\ value_has_type tv key /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e mid sm sn t es key ix s /\
  compile_keccak256_key ix F sn = (hashed,sh) /\
  compile_mapping_subscript base_op hashed sh = (dst,sb) /\
  fn_has_code sn sh fp.jc_func /\ fn_has_code sh sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  (!x. base_op = Var x \/ ix = Var x ==> not_fresh_at sn x) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  eval_operand base_op s = SOME slot /\
  extend_place fp.jc_cx (HashMapRef tr slot kt vt) (ValueSubscript key) es =
    (INL pv,es') ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 es' pv vt
        (dst,SOME (slot_loc tr),SOME (value_type_place vt)) u /\
      intcall_expr_cont fp ce env es0 sa s0 es' sb u
Proof
  strip_tac >> gvs[] >>
  drule_all target_subscript_dynamic_key_view >> strip_tac >>
  `intcall_expr_res fp ce env es sn s /\ ~s.vs_halted /\
   s.vs_current_bb = sn.cs_current_bb /\
   s.vs_inst_idx = LENGTH sn.cs_current_insts` by fs[intcall_expr_cont_def] >>
  drule_at (Pat `compile_keccak256_key _ _ _ = _`) intcall_key_prehash >>
  simp[] >> disch_then drule_all >> strip_tac >>
  rename1 `intcall_expr_cont _ _ _ _ _ _ _ sh h` >>
  `ci_mono sn sh` by metis_tac[ci_mono_compile_keccak256_key, SND] >>
  `intcall_expr_cont fp ce env es0 sa s0 es sh h` by
    (irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`es`, `sn`, `s`] >> simp[]) >>
  `eval_operand base_op h = SOME slot` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_saved_operand >>
     goal_assum (drule_at Any) >> fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `!x. hashed = Var x ==> not_fresh_at sh x` by
    (drule compile_keccak256_key_parts >> strip_tac >>
     qpat_x_assum `emit_op SHA3 _ _ = _` (mp_tac o MATCH_MP emit_op_facts) >>
     simp[] >> strip_tac >> gvs[]) >>
  `sa.cs_next_var <= sh.cs_next_var /\ sa.cs_next_id <= sh.cs_next_id /\
   (!x. base_op = Var x \/ hashed = Var x ==> not_fresh_at sh x)` by
    (fs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, not_fresh_at_mono]) >>
  `eval_operand hashed h = SOME (encode_hashmap_key (expr_type e) key)` by
    fs[byteTheory.word_of_bytes_be_def] >>
  drule_at (Pat `compile_mapping_subscript _ _ _ = _`) intcall_target_mapping_suffix >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule_all >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD]
QED
