(* Optional mapping-key hashing, including the scalar identity suffix. *)
Theory bodyIntCallFamAggSubscriptOptionalKey
Ancestors
  bodyIntCallFamAggSubscriptKey bodyIntCallJointContract exprSimMapKey
  loweringPosts exprLoweringProps fragGasFocus fragGasPath fragGasMode vyperValue
  compileEnv context venomState venomInst vyperTypeSystem vyperAST vyperTyping

Theorem intcall_optional_key_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es sn s /\
  sa.cs_next_var <= sn.cs_next_var /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e ek sk sn ks es kv key s /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv fp.jc_cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  fn_has_code sn sp fp.jc_func /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sn x) /\
  eval_operand base_op s = SOME slot ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es0 sa s0 es sp u /\
    eval_operand hashed u = SOME (encode_hashmap_key kt kv) /\
    (!x. hashed = Var x ==> not_fresh_at sp x) /\
    eval_operand base_op u = SOME slot
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_bytestring_type kt`
  >- (gvs[] >> irule intcall_dynamic_key_cont >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `~s.vs_halted` by fs[intcall_expr_cont_def] >>
  qexists_tac `s` >>
  simp[gas_marked_path_def, gas_path_rules] >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_word >>
     Cases_on `expr_type e` >> gvs[hashmap_key_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[hashmap_key_type_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def, evaluate_type_def,
         AllCaseEqs()]) >>
  irule expr_val_rel_hashmap_scalar >> simp[] >>
  qexistsl_tac [`fp.jc_cx`, `tv`] >>
  qpat_x_assum `post_value_type _ _ = _`
    (fn th => fs[expr_post_def, th])
QED
