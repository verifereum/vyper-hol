Theory bodyPtrTypeBuiltinsMemoryPost
Ancestors bodyPtrTypeBuiltinsMemoryInterface bodyPtrTypeBuiltinsWidenSemantic
  bodyPtrTypeBuiltinsCastExecution bodyPtrTypeBuiltinsWidenExecution
  bodyPtrTypeBuiltinsSourceTyping exprSimConvert vyperValueOperation
  vyperTyping vyperValue valueEncoding compileEnv arithmetic loweringPosts bodyPtrDefs
  ptrDiscipline bodyPtrTypeBuiltinsSourceFrame bodyPtrTypeBuiltinsCastSemantic
  bodyPtrTypeBuiltinsWidenCounted fragExec
Libs intLib

Theorem memory_widen_length_bound:
  !len sz n. sz MOD 32 = 0 /\ len + 32 <= sz /\
    sz < 32 * ((n + 31) DIV 32) + 32 ==> len <= n
Proof
  rpt gen_tac >> qspec_then `32` mp_tac DIVISION >> simp[] >>
  disch_then (fn th => map_every (fn q => qspec_then q mp_tac th) [`sz`,`n+31`]) >>
  map_every (fn (tm,v) => Q.SPEC_TAC (tm,v))
    [(`(n+31) MOD 32`,`r`), (`(n+31) DIV 32`,`q`),
     (`sz MOD 32`,`srem`), (`sz DIV 32`,`squot`)] >> COOPER_TAC
QED

Theorem memory_widen_semantic_success:
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ value_has_type tv v /\
  val_footprint tv v <= sz /\ sz MOD 32 = 0 /\
  sz < type_memory_bytes cenv tdst ==>
  ?v'. convert_result cx tsrc tdst v = INL v'
Proof
  strip_tac >> qspecl_then [`tsrc`,`tdst`] mp_tac memory_convert_shapes >>
  simp[] >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, val_footprint_def, type_memory_bytes_def,
      convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  rename1 `LENGTH payload + 32 <= sz` >>
  `LENGTH payload <= n` by (irule memory_widen_length_bound >> metis_tac[]) >> simp[]
QED

Theorem memory_conversion_layout:
  is_bytestring_type tsrc /\ is_bytestring_type tdst /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\
  evaluate_type (get_tenv cx) tdst = SOME tv2 /\ value_has_type tv v /\
  convert_result cx tsrc tdst v = INL v' ==>
  value_has_type tv2 v' /\ val_wf tv2 v' /\
  val_footprint tv2 v' = val_footprint tv v /\
  (!off mem. val_in_memory tv2 v' off mem <=> val_in_memory tv v off mem)
Proof
  strip_tac >> qspecl_then [`tsrc`,`tdst`] mp_tac memory_convert_shapes >>
  simp[] >> strip_tac >> gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, convert_result_def, evaluate_convert_from_def,
      evaluate_convert_def, AllCaseEqs(), val_footprint_def, val_wf_def,
      val_in_memory_def, abiDecoderStringTheory.abi_decoder_string_bytes_roundtrip] >>
  simp[type_memory_size_def] >>
  mp_tac (Q.SPEC `n` exprSimPropsTheory.le_word_size_mul) >> decide_tac
QED

Theorem memory_conversion_expr_post:
  is_bytestring_type (expr_type e1) /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\ value_has_type tv v /\
  convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
  expr_post ctx fn cenv cx e1 es sa sb s0 es1 v op t ==>
  expr_post ctx fn cenv cx e es sa sb s0 es1 v' op t
Proof
  strip_tac >> drule_all memory_conversion_layout >> strip_tac >>
  `~is_word_type (expr_type e1) /\ ~is_word_type (expr_type e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def] >>
  simp[] >>
  qspecl_then [`expr_type e1`,`expr_type e`] mp_tac memory_convert_shapes >>
  simp[] >> strip_tac >> gvs[evaluate_type_def] >>
  metis_tac[exprSimPropsTheory.local_val_at_base, LESS_EQ_REFL]
QED

Theorem memory_outer_annotation:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es ==>
  ann = dst
Proof
  strip_tac >> drule expr_body_pre_convert >> simp[]
QED

Theorem memory_outer_buffer_covered:
  lookup_var src s = SOME w /\ ptr_covers G tn src s (type_memory_bytes cenv dst) ==>
  ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) (Var src) G s
Proof
  simp[ptr_buf_ok_def, convert_outer_lowered_type, ptr_covers_def,
       venomStateTheory.eval_operand_def] >> rpt strip_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem memory_post_inst_idx:
  expr_post ctx fn cenv cx e es sa sb s0 es1 v op
    (s with vs_inst_idx := pc) <=>
  expr_post ctx fn cenv cx e es sa sb s0 es1 v op s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       local_region_def, locals_kept_def]
QED

Theorem memory_readonly_val_at:
  expr_val_at cenv cx ty sa sm es v x s /\
  eval_operand x s = SOME p /\ eval_operand op t = SOME p /\
  t.vs_allocas = s.vs_allocas /\ sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sm /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) ==>
  expr_val_at cenv cx ty sa sb es v op t
Proof
  strip_tac >>
  `!n b sz. local_region cenv es.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule exprSimPropsTheory.local_region_frame >>
         conj_tac >- (qexists_tac `fn` >> simp[]) >>
         qexistsl_tac [`sm`,`es.scopes`,`t`] >> simp[]) >>
     strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`,`sm`,`es.scopes`] >> simp[]) >>
  gvs[expr_val_at_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. _ ==> _` drule_all >> strip_tac >> gvs[]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]
QED

Theorem memory_readonly_expr_post:
  expr_post ctx fn cenv cx e es sa sm s0 es1 v x s /\
  stmt_state_rel ctx fn cenv cx es1 t /\
  eval_operand x s = SOME p /\ eval_operand op t = SOME p /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  sm.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved cenv sm /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) ==>
  expr_post ctx fn cenv cx e es sa sb s0 es1 v op t
Proof
  strip_tac >>
  `local_ptrs_rel fn cenv es1.scopes s` by
    gvs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  `expr_val_at cenv cx (expr_type e) sa sb es1 v op t` by
    (irule memory_readonly_val_at >> goal_assum (drule_at Any) >>
     gvs[expr_post_def] >> metis_tac[]) >>
  `expr_val_rel cx (expr_type e) v op t` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  gvs[expr_post_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x'` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  irule exprSimPropsTheory.locals_kept_mem_tail >> qexists_tac `s` >> simp[]
QED

Theorem memory_expr_post_compose:
  expr_post ctx fn cenv cx e1 es sa sm s0 es1 v1 x s1 /\
  expr_post ctx fn cenv cx e es1 sm sb s1 es1 v op t /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
  expr_post ctx fn cenv cx e es sa sb s0 es1 v op t
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 s1` by
    (gvs[expr_post_def, wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es1 sm s1 t` by
    (gvs[expr_post_def, wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all exprSimWordArgsTheory.wb_frame_trans >> strip_tac >>
  gvs[expr_post_def, wb_frame_def] >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  irule exprSimPropsTheory.expr_val_at_start_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem memory_covered_ptr_val:
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_var src s = SOME w /\ ptr_covers G tn src s sz /\
  val_store_size tv v <= sz /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
  ptr_val_ok cx ty v (Var src) G tn s
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_covers_def,
       venomStateTheory.eval_operand_def] >> rpt strip_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem memory_widen_destination_post:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword(:256) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  expr_post ctx fn cenv cx e es sa sm s0 es1 v x s /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME p /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tv2 /\ value_has_type tv v /\
  val_wf tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
  val_footprint tv v <= k /\ convert_result cx (expr_type e) dst v = INL v' ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e])
      es sa sb s0 es1 v' op t
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx es1 s` by gvs[expr_post_def] >>
  `~is_word_type (expr_type e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  drule_all widen_copy_actual_post >> strip_tac >>
  `expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e])
     es1 sm sb s es1 v' op t` by
    (irule memory_conversion_expr_post >>
     simp[vyperASTTheory.expr_type_def] >>
     qexistsl_tac [`e`,`tv`,`v`] >> simp[]) >>
  qexists_tac `t` >> simp[] >> irule memory_expr_post_compose >>
  simp[SF SFY_ss]
QED

Theorem memory_cast_destination_post:
  expr_post ctx fn cenv cx e es sa sm s0 es1 v (Var src) s /\
  stmt_state_rel ctx fn cenv cx es1 t /\ local_ptrs_reserved cenv sm /\
  lookup_var src s = SOME w /\ not_fresh_at sm src /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
  sm.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tv2 /\ value_has_type tv v /\
  convert_result cx (expr_type e) dst v = INL v' ==>
  expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 es1 v' (Var src) t
Proof
  strip_tac >>
  `expr_post ctx fn cenv cx e es sa sb s0 es1 v (Var src) t` by
    (irule memory_readonly_expr_post >>
     goal_assum (drule_at Any) >>
     simp[venomStateTheory.eval_operand_def] >>
     qexistsl_tac [`s`,`sm`,`Var src`] >>
     simp[venomStateTheory.eval_operand_def]) >>
  irule memory_conversion_expr_post >> simp[vyperASTTheory.expr_type_def] >>
  qexistsl_tac [`e`,`tv`,`v`] >> simp[]
QED

Theorem memory_cast_actual_destination_post:
  compile_type_convert (Var src) (ConvBytestringCast n i) sm = (out,sb) /\
  (expr_type e = BaseT (BytesT (Dynamic i)) \/ expr_type e = BaseT (StringT i)) /\
  (dst = BaseT (BytesT (Dynamic n)) \/ dst = BaseT (StringT n)) /\
  expr_post ctx fn cenv cx e es sa sm s0 es1 v (Var src) s /\
  local_ptrs_reserved cenv sm /\ lookup_var src s = SOME w /\
  not_fresh_at sm src /\ i < dimword(:256) /\ n < dimword(:256) /\
  sm.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tv2 /\ value_has_type tv v /\
  val_in_memory tv v (w2n w) s.vs_memory ==>
  out = Var src /\
  case convert_result cx (expr_type e) dst v of
    INL v' => ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
      (t with vs_vars := s.vs_vars) = s /\
      (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
      expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e])
        es sa sb s0 es1 v' out t
  | INR ex => ?msg t. ex = Error (RuntimeError msg) /\
      run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all cast_compile_typed_outcome >>
  Cases_on `convert_result cx (expr_type e) dst v` >> simp[] >> strip_tac >>
  simp[] >>
  `stmt_state_rel ctx fn cenv cx es1 s` by gvs[expr_post_def] >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `stmt_state_rel ctx fn cenv cx es1 t` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`s`,`sm`] >> simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  irule memory_cast_destination_post >>
  simp[SF SFY_ss] >>
  fs[is_bytestring_type_def] >>
  qexistsl_tac [`s`,`sm`,`v`,`w`] >> gvs[]
QED

Theorem memory_destination_pointer_post:
  is_bytestring_type dst /\ evaluate_type (get_tenv cx) dst = SOME tv /\
  val_wf tv v /\ lookup_var src s = SOME w /\
  ptr_covers G tn src s (type_memory_bytes cenv dst) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) ==>
  ptr_val_ok cx dst v (Var src) G tn s /\
  ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) (Var src) G s
Proof
  strip_tac >> conj_tac
  >- (irule memory_covered_ptr_val >>
      `~is_word_type dst` by
        metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
      `type_memory_bytes cenv dst = type_memory_size tv` by
        (qspecl_then [`dst`,`dst`] mp_tac memory_convert_shapes >>
         simp[] >> strip_tac >>
         gvs[evaluate_type_def, type_memory_bytes_def, type_memory_size_def,
             vfmConstantsTheory.word_size_def, AllCaseEqs()]) >>
      simp[] >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[exprSimPropsTheory.val_store_size_le]) >>
  irule memory_outer_buffer_covered >> simp[SF SFY_ss]
QED

Theorem memory_widen_counted_destination_post:
  compile_bytestring_widen_copy (type_memory_bytes cenv dst) (Var src) k sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  0 < k /\ k <= type_memory_bytes cenv dst /\
  type_memory_bytes cenv dst < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sm src /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  expr_post ctx fn cenv cx e es sa sm s0 es1 v (Var src) s /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tv2 /\ value_has_type tv v /\
  val_wf tv v /\ val_footprint tv v <= k /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s k /\ ghost_inv d cenv cx es1 G tn s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  convert_result cx (expr_type e) dst v = INL v' ==>
  ?t H th. t.vs_current_bb = s.vs_current_bb /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 es1 v' op
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_inv d cenv cx es1 H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ptr_val_ok cx dst v' op H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) op H
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv es1 sm G tn s H th
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx es1 s /\
   expr_val_at cenv cx (expr_type e) sa sm es1 v (Var src) s` by gvs[expr_post_def] >>
  `~is_word_type (expr_type e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `val_in_memory tv v (w2n a) s.vs_memory` by
    (qpat_x_assum `!m. mem_agree_outside _ _ m ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  `eval_operand (Var src) s = SOME a` by simp[venomStateTheory.eval_operand_def] >>
  `!z. Var src = Var z ==> not_fresh_at sm z` by simp[] >>
  drule_all memory_widen_destination_post >> strip_tac >>
  drule_all widen_copy_straight_code >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all exec_block_run_inst_seq >> strip_tac >> metis_tac[]) >>
  drule_all widen_copy_converted_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all memory_conversion_layout >> strip_tac >>
  `ptr_val_ok cx dst v' op G' th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
   ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) op G'
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))` by
    (gvs[] >> irule memory_destination_pointer_post >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`t`,`G'`,`th`] >> gvs[memory_post_inst_idx]
QED

Theorem memory_cast_counted_destination_post:
  compile_type_convert (Var src) (ConvBytestringCast n i) sm = (out,sb) /\
  (expr_type e = BaseT (BytesT (Dynamic i)) \/ expr_type e = BaseT (StringT i)) /\
  (dst = BaseT (BytesT (Dynamic n)) \/ dst = BaseT (StringT n)) /\
  expr_post ctx fn cenv cx e es sa sm s0 es1 v (Var src) s /\
  local_ptrs_reserved cenv sm /\ lookup_var src s = SOME w /\
  not_fresh_at sm src /\ i < dimword(:256) /\ n < dimword(:256) /\
  sm.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tv2 /\ value_has_type tv v /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ type_memory_bytes cenv dst <= sz /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es1 G tn s /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sm p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sm p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
  convert_result cx (expr_type e) dst v = INL v' ==>
  ?t H th. out = Var src /\ t.vs_current_bb = s.vs_current_bb /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 es1 v' out
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_inv d cenv cx es1 H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ptr_val_ok cx dst v' out H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out H
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv es1 sm G tn s H th
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_in_memory tv v (w2n w) s.vs_memory` by
    (qpat_assum `!m. mem_agree_outside _ _ m ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  drule_all memory_cast_actual_destination_post >> simp[] >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `is_bytestring_type (expr_type e) /\ is_bytestring_type dst` by
    (fs[is_bytestring_type_def] >> simp[is_bytestring_type_def]) >>
  drule_all convert_cast_converted_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all memory_conversion_layout >> strip_tac >>
  `lookup_var src t = SOME w` by metis_tac[] >>
  `ptr_covers H th src t (type_memory_bytes cenv dst)` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all memory_destination_pointer_post >>
  disch_then (qspec_then `e` strip_assume_tac) >>
  qexistsl_tac [`t`,`H`,`th`] >>
  gvs[memory_post_inst_idx, ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      SRULE [] (Q.INST [`es` |-> `es1`, `gs` |-> `es1.gas_obs`]
        (SPEC_ALL exprSimPtrLiteralBufferTheory.literal_ptr_ghost_inv_normalize))]
QED

Theorem memory_cast_counted_exit:
  compile_type_convert (Var src) (ConvBytestringCast n i) sm = (out,sb) /\
  (tsrc = BaseT (BytesT (Dynamic i)) \/ tsrc = BaseT (StringT i)) /\
  (dst = BaseT (BytesT (Dynamic n)) \/ dst = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\ lookup_var src s = SOME w /\
  not_fresh_at sm src /\ i < dimword(:256) /\ n < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn src s sz /\ 32 <= sz /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sm /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sm p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sm p) /\
  convert_result cx tsrc dst v = INR ex ==>
  ?r H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th r /\
    expr_exit (INR ex : value + exception) r /\ ghost_kept cenv es sm G tn s H th
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all cast_compile_typed_outcome >> simp[] >> strip_tac >>
  drule_all bodyPtrTypeBuiltinsCastTheory.convert_cast_abort_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[exprSimDefsTheory.expr_exit_def]
QED
