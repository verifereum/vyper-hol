Theory bodyPtrSubscriptSeamMapTail
Ancestors
  bodyPtrSubscriptSeamMapEncoding bodyPtrSubscriptSeamMapHash
  stmtReasonLitFragMemory exprSimMapKey fragExec exprLoweringProps
  bodyPtrHashBuiltinsShaEndpoint instIdxIndep

Theorem mapping_slot_hash_endpoint_ptr:
  compile_mapping_subscript slot key sa = (op,sb) /\
  (!z. slot = Var z \/ key = Var z ==> not_fresh_at sa z) /\
  eval_operand slot s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn slot = {} /\ op_taint tn key = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u) /\
    eval_operand op u = SOME (hashmap_slot w0 w1) /\
    stmt_state_rel ctx fn cenv cx es u /\ ghost_inv d cenv cx es G' tn' u /\
    ghost_kept cenv es sa G tn s G' tn' /\ op_taint tn' op = {} /\
    wb_frame cenv es es sa s u /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[mapping_suffix_shape] >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  drule_all mapping_alloca_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all mapping_slot_hash_ptr_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  gvs[listTheory.LENGTH_APPEND, eval_op_inst_idx] >>
  gvs[stmt_state_rel_inst_idx, loweringPostsTheory.wb_frame_def,
      loweringStateRelDefsTheory.local_region_def, venomStateTheory.lookup_var_def] >> gvs[]
QED

Theorem mapping_key_encoding_layout:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  (!z. key = Var z ==> not_fresh_at sn z) ==>
  same_blocks sn sp /\
  sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp /\
  sn.cs_next_var <= sp.cs_next_var /\ sn.cs_next_id <= sp.cs_next_id /\
  (!z. hashed = Var z ==> not_fresh_at sp z)
Proof
  strip_tac >> Cases_on `is_bytestring_type kt`
  >- (gvs[] >> drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
      strip_tac >> drule (cj 1 mapping_suffix_next_id) >> strip_tac >>
      simp[]) >>
  gvs[emitted_insts_def, same_blocks_def]
QED

Theorem mapping_key_encoding_extends:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) ==>
  cs_extends sn sp
Proof
  strip_tac >> Cases_on `is_bytestring_type kt` >> gvs[]
  >- (qspec_then `key` (qspec_then `F` (qspec_then `sn` mp_tac))
        ci_mono_compile_keccak256_key >> simp[ci_mono_def]) >>
  MATCH_ACCEPT_TAC compileEnvTheory.cs_extends_refl
QED

Theorem mapping_key_encode_endpoint_ptr:
  expr_post ctx fn cenv cx e es sa sn s0 ee kv key s /\
  hashmap_key_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  ptr_val_ok cx (post_value_type cenv e) kv key G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (key,sn) /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_key key F sn
   else (key,sn)) = (op,sp) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sn p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sn p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  fn_has_code sn sp fn ==>
  ?u G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u) /\
    eval_operand op u = SOME (encode_hashmap_key (expr_type e) kv) /\
    stmt_state_rel ctx fn cenv cx ee u /\ ghost_inv d cenv cx ee G' tn' u /\
    ghost_kept cenv ee sn G tn s G' tn' /\ op_taint tn' op = {} /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!z. not_fresh_at sn z ==> lookup_var z u = lookup_var z s) /\
    u.vs_current_bb = sp.cs_current_bb /\ u.vs_inst_idx = LENGTH sp.cs_current_insts
Proof
  strip_tac >>
  `!z. key = Var z ==> not_fresh_at sn z` by
    (drule_at (Pos hd) exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  drule_all mapping_key_encoding_layout >> strip_tac >>
  `sp.cs_current_bb = sn.cs_current_bb` by gvs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sn sp) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all mapping_key_encode_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`t with vs_inst_idx := LENGTH sp.cs_current_insts`, `G'`, `tn'`] >>
  gvs[listTheory.LENGTH_APPEND, eval_op_inst_idx, stmt_state_rel_inst_idx] >>
  simp[venomStateTheory.lookup_var_def] >>
  qpat_x_assum `t with vs_vars := _ = s` mp_tac >>
  simp[venomStateTheory.venom_state_component_equality] >>
  strip_tac >> gvs[venomStateTheory.lookup_var_def]
QED

Theorem mapping_encoding_slot_frame:
  (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!z. not_fresh_at sn z ==> lookup_var z u = lookup_var z s) /\
  ghost_kept cenv ee sn G tn s G' tn' /\
  (!z. slot = Var z ==> not_fresh_at sn z) /\
  eval_operand slot s = SOME base_slot /\ op_taint tn slot = {} ==>
  eval_operand slot u = SOME base_slot /\ op_taint tn' slot = {}
Proof
  strip_tac >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s`
      (mp_tac o Q.AP_TERM `\v. v.vs_labels`) >> simp[]) >>
  Cases_on `slot` >>
  gvs[venomStateTheory.eval_operand_def,
      bodyPtrDefsTheory.ghost_kept_def, ptrDisciplineTheory.op_taint_def] >>
  metis_tac[]
QED

Theorem mapping_index_tail_ptr:
  expr_post ctx fn cenv cx e es sa sn s0 ee kv key s /\
  hashmap_key_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  ptr_val_ok cx (post_value_type cenv e) kv key G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (key,sn) /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript slot hashed sp = (out,sb) /\
  fn_has_code sn sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sn p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sn p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!z. slot = Var z ==> not_fresh_at sn z) /\
  eval_operand slot s = SOME base_slot /\ op_taint tn slot = {} ==>
  ?u Gu tnu. gas_path_ptr D 0 ctx fn PG G tn s 0 Gu tnu (OK u) /\
    eval_operand out u = SOME (hashmap_slot base_slot (encode_hashmap_key (expr_type e) kv)) /\
    stmt_state_rel ctx fn cenv cx ee u /\ ghost_inv d cenv cx ee Gu tnu u /\
    op_taint tnu out = {} /\ wb_frame cenv ee ee sn s u /\
    ghost_kept cenv ee sn G tn s Gu tnu /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule mapping_key_encoding_extends >> strip_tac >>
  `cs_extends sp sb` by
    (mp_tac (Q.SPECL [`slot`, `hashed`, `sp`] ci_mono_compile_mapping_subscript) >>
     simp[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `!z. key = Var z ==> not_fresh_at sn z` by
    (drule_at (Pos hd) exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  drule_all mapping_key_encoding_layout >> strip_tac >>
  drule_all mapping_key_encode_endpoint_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK a)` >>
  drule_all mapping_encoding_slot_frame >> strip_tac >>
  `local_ptrs_reserved cenv sp /\
   (!z. slot = Var z \/ hashed = Var z ==> not_fresh_at sp z) /\
   (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sp p) /\
   (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sp p)` by
    metis_tac[local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono] >>
  `~a.vs_halted` by
    (qpat_x_assum `a with <|vs_vars := _; vs_inst_idx := _|> = s`
       (mp_tac o Q.AP_TERM `\v. v.vs_halted`) >> simp[]) >>
  drule_all mapping_slot_hash_endpoint_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `a with <|vs_vars := _; vs_inst_idx := _|> = s`
      (mp_tac o Q.AP_TERM `\v. (v.vs_memory,v.vs_allocas)`) >> simp[]) >>
  `wb_frame cenv ee ee sn s a` by
    (simp[loweringPostsTheory.wb_frame_def] >>
     irule exprSimPropsTheory.locals_kept_regions >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx ee s` by
    gvs[loweringPostsTheory.expr_post_def] >>
  `wb_frame cenv ee ee sn s u` by
    (qspecl_then [`fn`, `cenv`, `cx`, `ee`, `s`, `sn`, `ee`, `ee`, `sp`, `a`, `u`, `ctx`]
       mp_tac exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `ghost_kept cenv ee sn G tn s G'' tn''` by
    (irule hash_ghost_kept_then >> goal_assum (drule_at Any) >>
     qexistsl [`G'`, `a`, `sp`, `tn'`] >> simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qexistsl [`u`, `G''`, `tn''`] >> simp[] >>
  drule_all fragGasPathPtrTheory.gas_path_ptr_then >> simp[]
QED
