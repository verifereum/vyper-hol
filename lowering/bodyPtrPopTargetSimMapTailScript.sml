(* Typed mapping-key input boundary for the checked mapping continuation. *)
Theory bodyPtrPopTargetSimMapTail
Ancestors bodyPtrPopTargetSimMapScratchRun bodyPtrPopTargetSimMapKeyRun
  bodyPtrEnvBuiltinsMemoryHashTyped
  exprSimMapKey vyperTypeSystem vyperValue vyperTyping vyperStorage
  valueEncoding words finite_map pred_set rich_list list loweringPosts
  compileEnv bodyPtrDefs valueEncodingProps venomState
  bodyPtrEnvBuiltinsEdges appendStorageGhostPtr fragGasSeqPtr fragGasPathPtr
  exprLoweringProps instIdxIndep venomExecSemantics venomInst exprSimWordArgs
  ghostPcTransportPtr

Theorem map_key_typed_input:
  expr_post ctx fn cenv cx e es sa sm s0 en kv key s /\
  ptr_val_ok cx (expr_type e) kv key G tn s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv ==>
  ?root a b sz n.
    key = Var root /\ lookup_var root s = SOME a /\
    FLOOKUP G root = SOME (b,sz) /\ b <= w2n a /\
    w2n a+32+n <= b+sz /\ w2n a+32 < dimword (:256) /\
    n < dimword (:256) /\ op_taint tn key = {} /\
    (!i. w2n a <= i /\ i < w2n a+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at (w2n a) s.vs_memory = n2w n
Proof
  strip_tac >> Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, evaluate_type_def]
  >- (Cases_on `kv` >> gvs[value_has_type_def] >>
      `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT n))`
        by simp[evaluate_type_def] >>
      drule_at (Pat `expr_type _ = _`) memory_hash_string_input >>
      simp[evaluate_type_def] >> disch_then drule_all >> strip_tac >>
      qexistsl_tac [`root`, `a`, `b`, `sz`, `w2n (n2w (LENGTH s'):bytes32)`] >>
      gvs[ptr_covers_def, mem_word_at_eq_mload]) >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[is_bytestring_type_def, evaluate_type_def] >>
  Cases_on `kv` >> gvs[value_has_type_def] >>
  rename1 `BytesV bs` >> rename1 `Dynamic cap` >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by simp[evaluate_type_def] >>
  drule_at (Pat `expr_type _ = _`) memory_hash_bytes_input >>
  simp[evaluate_type_def] >> disch_then drule_all >> strip_tac >>
  qexistsl_tac [`root`, `a`, `b`, `sz`, `w2n (n2w (LENGTH bs):bytes32)`] >>
  gvs[ptr_covers_def, mem_word_at_eq_mload]
QED

Theorem map_key_typed_checked:
  expr_post ctx fn cenv cx e es sa sm s0 en kv key s /\
  ptr_val_ok cx (expr_type e) kv key G tn s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  compile_keccak256_key key F sm = (hashed,sp) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx ==>
  ?H tm. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sp) s H tm /\
    op_taint tm hashed = {} /\ op_prov H hashed = NONE /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all map_key_typed_input >> strip_tac >> gvs[] >>
  irule map_key_inst_seq >> simp[eval_operand_def] >>
  qexistsl_tac [`w2n a`, `b`, `sz`, `n`, `root`] >> simp[] >> decide_tac
QED

Theorem map_key_typed_frame:
  expr_post ctx fn cenv cx e es sa sm s0 en kv key s /\
  ptr_val_ok cx (expr_type e) kv key G tn s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  compile_keccak256_key key F sm = (hashed,sp) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx en G tn s /\ local_ptrs_reserved cenv sm /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) ==>
  ?t H tm. run_inst_seq (emitted_insts sm sp) s = OK t /\
    eval_operand hashed t = SOME (encode_hashmap_key (expr_type e) kv) /\
    stmt_state_rel ctx fn cenv cx en t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sp) s H tm /\
    ghost_inv d cenv cx en H tm t /\ ghost_kept cenv en sm G tn s H tm /\
    op_taint tm hashed = {} /\ op_prov H hashed = NONE /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all map_key_typed_checked >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_at (Pat `compile_keccak256_key _ _ _ = _`)
    compile_hashmap_dynamic_key_frame >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qexistsl_tac [`t`, `H`, `tm`] >> simp[] >> conj_tac
  >- (irule ghost_inv_register_transport >>
      qexistsl_tac [`G`, `s`, `sm`, `tn`] >> simp[] >>
      qpat_x_assum `t with vs_vars := _ = _`
        (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_call_ctx,z.vs_accounts,z.vs_transient)`) >>
      simp[]) >>
  irule ghost_kept_old_transport >> simp[]
QED

Theorem map_key_typed_counted:
  expr_post ctx fn cenv cx e es sa sm s0 en kv key s /\
  ptr_val_ok cx (expr_type e) kv key G tn s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  compile_keccak256_key key F sm = (hashed,sp) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx en G tn s /\ local_ptrs_reserved cenv sm /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sp) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H tm. run_inst_seq (emitted_insts sm sp) s = OK t /\
    eval_operand hashed t = SOME (encode_hashmap_key (expr_type e) kv) /\
    stmt_state_rel ctx fn cenv cx en t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sp))) /\
    ghost_inv d cenv cx en H tm t /\ ghost_kept cenv en sm G tn s H tm /\
    op_taint tm hashed = {} /\ op_prov H hashed = NONE /\
    tm.t_mem = tn.t_mem /\
    (!x. not_fresh_at sm x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all map_key_typed_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `tm`] >> simp[] >>
  drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sp)) = 0 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sp)` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem map_scalar_key_word[local]:
  hashmap_key_type kt /\ ~is_bytestring_type kt /\
  evaluate_type tenv kt = SOME tv ==> is_word_type kt
Proof
  Cases_on `kt` >> gvs[hashmap_key_type_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[hashmap_key_type_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_bytestring_type_def, is_word_type_def, evaluate_type_def, AllCaseEqs()]
QED

Theorem map_index_key_prefix_ptr:
  expr_post ctx fn cenv cx e es sa sm s0 en kv key s /\
  ptr_val_ok cx (expr_type e) kv key G tn s /\ hashmap_key_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_key key F sm
   else (key,sm)) = (hashed,sp) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx en G tn s /\ local_ptrs_reserved cenv sm /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sp) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t H tm. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    eval_operand hashed t = SOME (encode_hashmap_key (expr_type e) kv) /\
    stmt_state_rel ctx fn cenv cx en t /\ wb_frame cenv en sm s t /\
    ghost_inv d cenv cx en H tm t /\ ghost_kept cenv en sm G tn s H tm /\
    op_taint tm hashed = {} /\ op_prov H hashed = NONE /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_mem = tn.t_mem /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> Cases_on `is_bytestring_type (expr_type e)`
  >- (gvs[] >> drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
        map_key_typed_counted >> simp[] >> disch_then drule_all >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      suspend "dynamic") >>
  gvs[] >>
  `is_word_type (expr_type e)` by (drule_all map_scalar_key_word >> simp[]) >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `eval_operand hashed s = SOME (encode_hashmap_key (expr_type e) kv)` by
    (irule expr_val_rel_hashmap_scalar >> simp[] >>
     qexistsl_tac [`cx`, `tv`] >> fs[expr_post_def]) >>
  `op_taint tn hashed = {} /\ op_prov G hashed = NONE` by
    fs[ptr_val_ok_def] >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[gas_path_ptr_rules, wb_frame_refl, ghost_kept_def] >>
  drule exprSimWordArgsTheory.expr_post_state >> simp[]
QED

Resume map_index_key_prefix_ptr[dynamic]:
  drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `t with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas,z.vs_current_bb)`) >> simp[]) >>
  `wb_frame cenv en sm s t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sm`, `s`] >>
     simp[wb_frame_refl]) >>
  `~t.vs_halted` by
    (drule gas_path_ptr_ok_not_halted >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sp.cs_current_insts`, `H`, `tm`] >>
  gvs[stmt_state_rel_inst_idx, bodyPtrEnvBuiltinsScalarTheory.ghost_inv_inst_idx, same_blocks_def,
      wb_frame_def, lookup_var_def]
QED

Finalise map_index_key_prefix_ptr
