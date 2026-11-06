(* Semantic endpoints use the very same deterministic runs as the pointer paths. *)
Theory bodyPtrHashBuiltinsShaCase
Ancestors bodyPtrHashBuiltinsShaFixedPaths bodyPtrHashBuiltinsShaBytes
  bodyPtrHashBuiltinsKeccakCase exprSimHash exprOperandVar exprSimVVFrame
  bodyPtrDefs compileEnv venomState list words exprSimWordArgs bodyPtrHashBuiltinsCases arithmetic bodyPtrHashBuiltinsInputWindow

Theorem hash_fixed_sha256_ptr_post:
  expr_post ctx fn cenv cx e es sa sm s0 ee (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  op_taint tn x = {} /\ ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  ?t Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (OK (t with vs_inst_idx := s.vs_inst_idx+7)) /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 (ee with outcomes := SOME rest)
      (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
      (StackValue (BaseT (BytesT (Fixed 32))) op)
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_inv d cenv cx (ee with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_kept cenv ee sm G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  strip_tac >>
  drule_all sha256_fixed_post_run >> strip_tac >>
  drule_all hash_fixed_post_view >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx ee s` by metis_tac[expr_post_state] >>
  drule_all (SRULE [] (Q.INST [`sha` |-> `T`] hash_fixed_alloca_code)) >>
  strip_tac >>
  `TAKE m (word_to_bytes_be w) = bs` by metis_tac[] >>
  drule_all hash_sha256_bytesm_success_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  gvs[] >> qexistsl_tac [`Gf`, `tf`] >> simp[]
QED

(* Shared operand/window preparation for the two dynamic SHA outcomes. *)
fun hash_dynamic_sha256_input_tac semantic_run_tac g = (
  drule_all hash_dynamic_post_view >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all hash_dynamic_bytes_operand >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx ee s` by metis_tac[expr_post_state] >>
  semantic_run_tac >>
  drule_all hash_sha256_memory_alloca_code >> strip_tac >>
  `expr_val_at cenv cx (expr_type e) sa sm ee (BytesV bs) x s` by
    fs[loweringPostsTheory.expr_post_def] >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `lower_value compile_expr cenv (expr_type e) e sa = (Var p,sm)` by
    asm_rewrite_tac[] >>
  `b + 32 + LENGTH bs <= b' + sz'` by decide_tac >>
  `b + 32 + LENGTH bs = b + (LENGTH bs + 32)` by decide_tac >>
  `!i. b <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tn.t_mem` by
    asm_rewrite_tac[] >>
  drule_at (Pos hd) hash_dynamic_bytes_input_window >> simp[] >>
  disch_then (qspecl_then [`n2w b`, `sm`] mp_tac) >>
  simp[eval_operand_def] >> disch_tac) g;

Theorem hash_dynamic_sha256_ptr_post:
  expr_post ctx fn cenv cx e es sa sm s0 ee (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ptr_val_ok cx (expr_type e) (BytesV bs) x G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytes x sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  ?t Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (OK (t with vs_inst_idx := s.vs_inst_idx+7)) /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 (ee with outcomes := SOME rest)
      (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
      (StackValue (BaseT (BytesT (Fixed 32))) op)
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_inv d cenv cx (ee with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_kept cenv ee sm G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  strip_tac >> hash_dynamic_sha256_input_tac
    (drule_all sha256_memory_post_run >> strip_tac) >>
  drule_at (Pos hd) (SRULE [eval_operand_def, GSYM ADD_ASSOC]
    (GEN_ALL (Q.INST [`n` |-> `LENGTH bs`]
      (SPEC_ALL hash_sha256_bytes_success_path)))) >>
  simp[] >>
  disch_then (drule_all_then (qspecl_then [`PG`, `D`] strip_assume_tac)) >>
  gvs[] >> qexistsl_tac [`Gf`, `tf`] >> simp[]
QED

Theorem hash_fixed_sha256_ptr_abort:
  expr_post ctx fn cenv cx e es sa sm s0 ee (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  op_taint tn x = {} /\ ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t j Gf tf. gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
    (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all hash_fixed_post_view >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx ee s` by metis_tac[expr_post_state] >>
  drule_all (SRULE [] (Q.INST [`sha` |-> `T`] hash_fixed_alloca_code)) >>
  strip_tac >> drule_all hash_sha256_bytesm_abort_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem hash_dynamic_sha256_ptr_abort:
  expr_post ctx fn cenv cx e es sa sm s0 ee (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ptr_val_ok cx (expr_type e) (BytesV bs) x G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytes x sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t j Gf tf. gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
    (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >> hash_dynamic_sha256_input_tac all_tac >>
  drule_at (Pat `mem_word_at _ _ = _`) hash_sha256_bytes_abort_path >>
  simp[eval_operand_def, GSYM ADD_ASSOC] >>
  disch_then (drule_at_then (Pos hd) mp_tac) >> simp[] >>
  disch_then (drule_all_then mp_tac) >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED
