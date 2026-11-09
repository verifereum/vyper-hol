(* The complete mapping hash tail at its own entry. *)
Theory bodyIntCallFamAggSubscriptHashTail
Ancestors
  bodyIntCallFamAggSubscriptOptionalKey bodyIntCallFamAggSubscriptMappingSlot
  bodyIntCallJointContract bodyIntCallJointAggCore exprSimMapKey
  exprLoweringProps loweringPosts exprSimProps fragGasMode
  compileEnv context venomState

Theorem intcall_hashmap_tail_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sn s /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e ek sk sn ks es kv key s /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv fp.jc_cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (op,sb) /\
  fn_has_code sn sp fp.jc_func /\ fn_has_code sp sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sn x) /\
  eval_operand base_op s = SOME slot ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sn s es sb u /\
    eval_operand op u = SOME (hashmap_slot slot (encode_hashmap_key kt kv)) /\
    (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt gen_tac >> strip_tac >>
  `intcall_expr_cont fp ce env es sn s es sn s` by
    simp[intcall_expr_cont_def] >>
  `sn.cs_next_var <= sn.cs_next_var` by simp[] >>
  drule_all intcall_optional_key_cont >> strip_tac >>
  `sn.cs_next_var <= sp.cs_next_var /\ sn.cs_next_id <= sp.cs_next_id` by
    (Cases_on `is_bytestring_type kt` >> fs[]
     >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
         drule (cj 1 mapping_suffix_next_id) >> simp[])) >>
  `!x. base_op = Var x ==> not_fresh_at sp x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sn` >> simp[]) >>
  `intcall_joint_res fp ce env es sp u /\ ~u.vs_halted /\
   u.vs_current_bb = sp.cs_current_bb /\
   u.vs_inst_idx = LENGTH sp.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  drule_all intcall_mapping_slot_cont >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es sp u es sb out` >>
  `intcall_expr_cont fp ce env es sn s es sb out` by
    (irule intcall_expr_cont_trans >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `out` >> simp[] >>
  qpat_x_assum `gas_marked_path _ _ _ s 0 (OK _)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[]
QED
