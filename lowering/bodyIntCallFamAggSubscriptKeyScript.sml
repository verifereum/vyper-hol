(* Optional mapping key hashing retains the caller's continuation. *)
Theory bodyIntCallFamAggSubscriptKey
Ancestors
  bodyIntCallFamAggSubscriptReadOnly bodyIntCallJointContract exprSimMapKey
  exprLoweringProps loweringPosts stmtSimAugAssignPlaceMemory
  compileEnv context venomState venomInst

Theorem intcall_dynamic_key_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es sn s /\
  sa.cs_next_var <= sn.cs_next_var /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e ek sk sn ks es kv key s /\
  expr_type e = kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv fp.jc_cx) kt = SOME tv /\ value_has_type tv kv /\
  compile_keccak256_key key F sn = (hashed,sp) /\
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
  `local_ptrs_reserved ce sn` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  drule_all compile_hashmap_dynamic_key_frame >> strip_tac >>
  drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> strip_tac >>
  `sn.cs_next_var <= sp.cs_next_var /\ sp.cs_current_bb = sn.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sn sp) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sn sp) /\
   (!x. hashed = Var x ==> not_fresh_at sp x)` by
    fs[same_blocks_def, listTheory.EVERY_CONJ] >>
  drule_all intcall_readonly_run_landing >> strip_tac >>
  `!x w. not_fresh_at sn x /\ lookup_var x s = SOME w ==>
     lookup_var x (t with vs_inst_idx := LENGTH sp.cs_current_insts) = SOME w` by
    (rpt strip_tac >> fs[lookup_var_def]) >>
  `eval_operand base_op (t with vs_inst_idx := LENGTH sp.cs_current_insts) = SOME slot` by
    (drule_all aug_place_saved_operand >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sp.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def]
QED
