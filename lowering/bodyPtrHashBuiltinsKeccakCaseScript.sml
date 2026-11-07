(* Typed semantic endpoints paired with the checked Keccak suffix paths. *)
Theory bodyPtrHashBuiltinsKeccakCase
Ancestors
  exprSimHashBoundary
  bodyPtrHashBuiltinsUnary bodyPtrHashBuiltinsCases
  bodyPtrHashBuiltinsKeccakFixedFrame bodyPtrHashBuiltinsKeccakBytesFrame
  bodyPtrHashBuiltinsShaEndpoint exprSimHash exprSimVVFrame exprSimAlloc
  exprLoweringProps exprOperandVar exprSimWordArgs bodyPtrDefs
  gasSummaryComposePtr compileEnv venomState arithmetic words list

Theorem hash_fixed_keccak_ptr_post:
  expr_post ctx fn cenv cx e es sa sm s0 ee (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  op_taint tn x = {} /\ ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    t.vs_current_bb = s.vs_current_bb /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx+3)) /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 ee (Value (BytesV (Keccak_256_w64 bs)))
      (StackValue (BaseT (BytesT (Fixed 32))) op)
      (t with vs_inst_idx := s.vs_inst_idx+3) /\
    ghost_inv d cenv cx ee G' tn' (t with vs_inst_idx := s.vs_inst_idx+3) /\
    ghost_kept cenv ee sm G tn s G' tn' /\ op_taint tn' op = {} /\
    op_prov G' op = NONE
Proof
  strip_tac >>
  drule_all hash_fixed_post_view >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx ee s` by metis_tac[expr_post_state] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by
    (irule (SRULE [] (Q.INST [`sha` |-> `F`] hash_fixed_alloca_code)) >>
     metis_tac[]) >>
  drule_all keccak_fixed_post_run >> strip_tac >>
  qpat_x_assum `LENGTH bs = m` (SUBST_ALL_TAC o SYM) >>
  drule_all hash_fixed_keccak_ptr_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`u`, `G3`, `tn3`] >> gvs[]
QED

Theorem hash_dynamic_keccak_ptr_post:
  expr_post ctx fn cenv cx e es sa sm s0 ee (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ptr_val_ok cx (expr_type e) (BytesV bs) x G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytes x sm = (op,sb) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    t.vs_current_bb = s.vs_current_bb /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 ee (Value (BytesV (Keccak_256_w64 bs)))
      (StackValue (BaseT (BytesT (Fixed 32))) op)
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_inv d cenv cx ee G' tn'
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv ee sm G tn s G' tn' /\ op_taint tn' op = {} /\
    op_prov G' op = NONE
Proof
  strip_tac >> drule_all hash_dynamic_post_view >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all hash_dynamic_bytes_operand >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `lower_value compile_expr cenv (expr_type e) e sa = (Var p,sm)` by
    asm_rewrite_tac[] >>
  `b + 32 + LENGTH bs <= b' + sz'` by decide_tac >>
  `b + 32 + LENGTH bs = b + (LENGTH bs + 32)` by decide_tac >>
  `!i. b <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tn.t_mem` by
    asm_rewrite_tac[] >>
  drule_all (SRULE [eval_operand_def] hash_bytes_keccak_ptr_post) >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `LENGTH (emitted_insts sm sb) + s.vs_inst_idx =
   s.vs_inst_idx + LENGTH (emitted_insts sm sb)` by decide_tac >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_rewrite_tac[]
QED

Theorem hash_string_keccak_ptr_post:
  expr_post ctx fn cenv cx e es sa sm s0 ee (StringV str) x s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)) /\
  ptr_val_ok cx (expr_type e) (StringV str) x G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytes x sm = (op,sb) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ghost_inv d cenv cx ee G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sm p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    t.vs_current_bb = s.vs_current_bb /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 ee (Value (BytesV (Keccak_256_w64 (MAP (n2w o ORD) str))))
      (StackValue (BaseT (BytesT (Fixed 32))) op)
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_inv d cenv cx ee G' tn'
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv ee sm G tn s G' tn' /\ op_taint tn' op = {} /\
    op_prov G' op = NONE
Proof
  strip_tac >> drule_all hash_string_post_view >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all hash_string_operand >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `lower_value compile_expr cenv (expr_type e) e sa = (Var p,sm)` by
    asm_rewrite_tac[] >>
  `b + 32 + LENGTH str <= b' + sz'` by decide_tac >>
  `b + 32 + LENGTH str = b + (LENGTH str + 32)` by decide_tac >>
  `!i. b <= i /\ i < b + 32 + LENGTH str ==> i NOTIN tn.t_mem` by
    asm_rewrite_tac[] >>
  drule_all (SRULE [eval_operand_def, LENGTH_MAP]
    (Q.SPEC `MAP (n2w o ORD) str` o Q.GEN `bs` o SPEC_ALL $
      hash_bytes_keccak_ptr_post)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `LENGTH (emitted_insts sm sb) + s.vs_inst_idx =
   s.vs_inst_idx + LENGTH (emitted_insts sm sb)` by decide_tac >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_rewrite_tac[]
QED
