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
    wb_frame cenv es sa s u /\ u.vs_current_bb = sb.cs_current_bb /\
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
      compileEnvTheory.local_region_def, venomStateTheory.lookup_var_def] >> gvs[]
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
