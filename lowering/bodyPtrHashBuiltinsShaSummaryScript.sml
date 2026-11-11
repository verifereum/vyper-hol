(* Typed SHA suffix summaries use only counted endpoint boundaries. *)
Theory bodyPtrHashBuiltinsShaSummary
Ancestors bodyPtrHashBuiltinsShaCase bodyPtrHashBuiltinsShaSource
  bodyPtrHashBuiltinsWordSummary bodyPtrHashBuiltinsGhostCompose
  bodyPtrHashBuiltinsCursor exprSimVVFrame exprSimHash exprLoweringProps
  exprLowering emitHelperProps exprSimDefs exprSimWordArgs exprSimSource
  bodyPtrDefs gasSummaryComposePtr vyperInterpreter vyperContext compileEnv loweringStateRelDefs
  vyperTypeSystem vyperState list arithmetic

Theorem hash_fixed_sha256_summary:
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
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ee.gas_obs = [] /\ local_ptrs_rel fn cenv es.scopes s0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?marks. gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG marks
    (\es'. case builtin_result cx es'.accounts (BaseT (BytesT (Fixed 32)))
       Sha256 [expr_type e] [BytesV bs] of
       INR exc => (INR exc,es')
     | INL w => (do precompile_call_success Sha256; return (Value w) od) es')
    (ee,s,G,tn)
    (\res ef G' tn' t. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
        es sa sb s0 ef tv (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef G' tn' t /\
      ptr_vv_ok cx (expr_type (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]))
        tv (StackValue (BaseT (BytesT (Fixed 32))) op) ef G' tn' t /\
      (!t' op'. StackValue (BaseT (BytesT (Fixed 32))) op = StackValue t' op' /\
        ~is_word_type (expr_type (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])) ==>
        ptr_buf_ok cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]) op' G' t) /\
      (!t' p. StackValue (BaseT (BytesT (Fixed 32))) op = LocatedValue t' p /\
        p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]) p.ptr_operand G' t) /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res ef gt rr. expr_exit res rr)
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s` by metis_tac[expr_post_state] >>
  `builtin_result cx ee.accounts (BaseT (BytesT (Fixed 32))) Sha256
     [expr_type e] [BytesV bs] =
     INL (BytesV (word_to_bytes (SHA_256_bytes bs) T))` by
    simp[builtin_result_def, evaluate_builtin_def] >>
  Cases_on `?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success`
  >- suspend "success" >>
  drule_all hash_fixed_sha256_ptr_abort >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qexists_tac `[F]` >> irule hash_sha256_abort_summary >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Private endpoint consumer shared by fixed and dynamic successful suffixes. *)
fun hash_sha256_word_summary_tac g = (
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all hash_expr_post_ghost_kept_compose >> strip_tac >>
  drule_at (Pos hd) hash_sha256_success_cursor >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  drule_all hash_sha256_source_success >> strip_tac >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  irule (SRULE [vyperASTTheory.expr_type_def, is_word_type_def]
    (Q.INST [`e` |-> `Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]`]
      (SPEC_ALL hash_word_endpoint_summary))) >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) o SRULE []) >>
  simp[read_result_def, return_def] >> conj_tac
  >- (qpat_x_assum `!tail. _` mp_tac >> simp[]) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ (_ with vs_inst_idx := _)` mp_tac >> simp[]) g;

Resume hash_fixed_sha256_summary[success]:
  pop_assum strip_assume_tac >>
  drule_all hash_fixed_sha256_ptr_post >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `is_bytes_or_string_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    simp[is_bytes_or_string_type_def, is_bytestring_type_def] >>
  hash_sha256_word_summary_tac
QED
Finalise hash_fixed_sha256_summary

Theorem hash_dynamic_sha256_summary:
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
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ee.gas_obs = [] /\ local_ptrs_rel fn cenv es.scopes s0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?marks. gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG marks
    (\es'. case builtin_result cx es'.accounts (BaseT (BytesT (Fixed 32)))
       Sha256 [expr_type e] [BytesV bs] of
       INR exc => (INR exc,es')
     | INL w => (do precompile_call_success Sha256; return (Value w) od) es')
    (ee,s,G,tn)
    (\res ef G' tn' t. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
        es sa sb s0 ef tv (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef G' tn' t /\
      ptr_vv_ok cx (expr_type (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]))
        tv (StackValue (BaseT (BytesT (Fixed 32))) op) ef G' tn' t /\
      (!t' op'. StackValue (BaseT (BytesT (Fixed 32))) op = StackValue t' op' /\
        ~is_word_type (expr_type (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])) ==>
        ptr_buf_ok cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]) op' G' t) /\
      (!t' p. StackValue (BaseT (BytesT (Fixed 32))) op = LocatedValue t' p /\
        p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]) p.ptr_operand G' t) /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res ef gt rr. expr_exit res rr)
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s` by metis_tac[expr_post_state] >>
  `builtin_result cx ee.accounts (BaseT (BytesT (Fixed 32))) Sha256
     [expr_type e] [BytesV bs] =
     INL (BytesV (word_to_bytes (SHA_256_bytes bs) T))` by
    simp[builtin_result_def, evaluate_builtin_def] >>
  Cases_on `?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success`
  >- (pop_assum strip_assume_tac >>
      drule_all hash_dynamic_sha256_ptr_post >>
      disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
      `is_bytes_or_string_type (expr_type e) /\ is_bytestring_type (expr_type e)` by
        simp[is_bytes_or_string_type_def, is_bytestring_type_def] >>
      hash_sha256_word_summary_tac) >>
  drule_all hash_dynamic_sha256_ptr_abort >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qexists_tac `[F]` >> irule hash_sha256_abort_summary >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
