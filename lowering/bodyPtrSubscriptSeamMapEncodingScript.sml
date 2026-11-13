(* Typed dispatch for the mapping-key suffix. Fixed-byte keys, like scalar
   keys, are used directly; only dynamic bytes and strings are hashed. *)
Theory bodyPtrSubscriptSeamMapEncoding
Ancestors
  bodyPtrSubscriptSeamMapKey bodyPtrSubscriptSeamMapInterface
  exprSimMapKey exprOperandVar bodyPtrDefs loweringPosts
  bodyPtrHashBuiltinsGhostFrame compileEnv exprLowering fragGasPathPtr
  exprLoweringProps

Theorem mapping_key_encode_ptr:
  expr_post ctx fn cenv cx e es sa sm s0 ee kv key s /\
  hashmap_key_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  ptr_val_ok cx (post_value_type cenv e) kv key G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (key,sm) /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_key key F sm
   else (key,sm)) = (op,sb) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    eval_operand op t = SOME (encode_hashmap_key (expr_type e) kv) /\
    stmt_state_rel ctx fn cenv cx ee t /\
    ghost_inv d cenv cx ee G' tn'
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv ee sm G tn s G' tn' /\ op_taint tn' op = {} /\
    (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s)
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by metis_tac[mapping_key_post_type] >>
  `!z. key = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx ee s` by metis_tac[expr_post_def] >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- (gvs[] >> drule_all mapping_key_bytestring_input >> strip_tac >> gvs[] >>
      `op_taint tn (Var p) = {}` by gvs[ptr_val_ok_def] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
      `b+32+LENGTH bs <= root+cap /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)` by simp[] >>
      drule_all mapping_key_hash_ptr_frame >>
      disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
      qexistsl [`t`, `G'`, `tn'`] >> gvs[]) >>
  gvs[] >> qexistsl [`s`, `G`, `tn`] >>
  `s with vs_inst_idx := LENGTH sb.cs_current_insts = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  simp[emitted_insts_def, ghost_kept_def] >>
  conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  conj_tac
  >- (irule expr_val_rel_hashmap_scalar >> goal_assum (drule_at Any) >>
      gvs[expr_post_def] >> metis_tac[]) >>
  gvs[ptr_val_ok_def]
QED
