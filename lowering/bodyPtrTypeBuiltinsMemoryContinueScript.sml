Theory bodyPtrTypeBuiltinsMemoryContinue
Ancestors bodyPtrTypeBuiltinsMemoryPost bodyPtrTypeBuiltinsLoweredRepresentation
  bodyPtrTypeBuiltinsMemoryInterface bodyPtrTypeBuiltinsWidenCopyShape
  exprLowering exprLoweringProps loweringHalt emitHelper emitHelperProps rich_list
  context arithmetic wordArgsPtr exprSimWordArgs fragGasPathPtr allocLimits
  exprSimHypsDefs valueTypingMemoryProps words bodyPtrTypeBuiltinsUintCounted
  bodyPtrTypeBuiltinsHeaderLoad representationCleanPtr exprSimHyps
  bodyPtrDefs exprSimDefs vyperTyping valueEncoding vyperValue
  vyperTypeSystem compileEnv venomState loweringPosts
Libs monadsyntax

Theorem memory_source_representation:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ ptr_val_ok cx ty v x G tn s /\
  eval_operand x s = SOME w ==>
  ?src. x = Var src /\ lookup_var src s = SOME w /\
    op_taint tn (Var src) = {} /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
    (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `ptr_mem_ok cx ty v x G tn s` by gvs[ptr_val_ok_def] >>
  `val_footprint tv v <> 0` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def] >>
     TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
          gvs[is_bytestring_type_def, evaluate_type_def]) >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def]) >>
  `?src b sz. x = Var src /\ FLOOKUP G src = SOME (b,sz)` by
    (fs[ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m` by
    (fs[ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- gvs[ptr_val_ok_def, eval_operand_def] >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, evaluate_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
       gvs[is_bytestring_type_def, evaluate_type_def]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  metis_tac[robust_val_in_memory_bytes_clean, robust_val_in_memory_string_clean]
QED

Theorem memory_source_packet:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  ptr_val_ok cx (expr_type e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  eval_operand x s = SOME w ==>
  ?src ltv. x = Var src /\ lookup_var src s = SOME w /\
    ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
    (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    value_has_type ltv v /\
    val_footprint tv v <= type_memory_bytes cenv (lowered_value_type cenv e) /\
    32 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) MOD 32 = 0
Proof
  strip_tac >> drule_all memory_source_representation >> strip_tac >> gvs[] >>
  drule_all bytestring_read_lowered_layout >> strip_tac >>
  drule_all bodyPtrTypeBuiltinsBodyTypingTheory.body_runtime_source_lowered_bytestring >>
  strip_tac >>
  `32 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) MOD 32 = 0` by
    (qspecl_then [`lowered_value_type cenv e`,`lowered_value_type cenv e`]
       mp_tac memory_convert_shapes >> simp[] >> strip_tac >>
     gvs[compileEnvTheory.type_memory_bytes_def, evaluate_type_def,
         type_memory_size_def] >> simp[]) >>
  `ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e))` by
    (irule ptr_buf_ok_covers >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `ltv` >> simp[]
QED

Theorem memory_widen_compiler_frame:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\ fn_has_code sm sb fn ==>
  same_blocks sm sb /\ isPREFIX sm.cs_current_insts sb.cs_current_insts /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >> drule_all widen_copy_code_split >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  Cases_on `k = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def, same_blocks_def, ci_mono_def] >>
      metis_tac[]) >>
  `emit_void MCOPY [buf.buf_operand;x;Lit (n2w k)] sm' = ((),sb)` by
    (Cases_on `k` >> gvs[compile_copy_memory_def]) >>
  drule emit_void_extends >> strip_tac >>
  gvs[same_blocks_def, ci_mono_def] >>
  simp[IS_PREFIX_APPEND] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem memory_cast_compiler_frame:
  compile_type_convert x (ConvBytestringCast n i) sm = (op,sb) ==>
  same_blocks sm sb /\ isPREFIX sm.cs_current_insts sb.cs_current_insts /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id
Proof
  Cases_on `n < i` >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_void_def, emit_op_def, emit_inst_def, comp_bind_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      comp_return_def, same_blocks_def] >>
  simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

Theorem memory_success_summary:
  expr_post ctx fn cenv cx e es sa sm s0 (ee with gas_obs := []) v1 x s /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  convert_result cx (expr_type e) dst v1 = INL v /\
  same_blocks sm sb /\ isPREFIX sm.cs_current_insts sb.cs_current_insts /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  s.vs_current_bb = sm.cs_current_bb /\ t.vs_current_bb = s.vs_current_bb /\
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
  expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es sa sb s0
    (ee with gas_obs := []) v op
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
  ghost_inv d cenv cx (ee with gas_obs := []) H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
  ptr_val_ok cx dst v op H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
  ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) op H
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
  ghost_kept cenv (ee with gas_obs := []) sm G tn s H th ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) dst v1,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?v. res = INL v /\
      expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\ ptr_val_ok cx dst v op K tk ss /\
      ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) op K ss /\
      ghost_kept cenv es sa G0 tn0 s0 K tk)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 s` by
    (gvs[expr_post_def, wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept cenv es sa G0 tn0 s0 H th` by
    (irule ghost_kept_wb_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`ctx`,`cx`,`fn`] >> simp[]) >>
     qexistsl_tac [`G`,`ee with gas_obs := []`,`s`,`sm`,`tn`] >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (gvs[emitted_insts_def] >>
     drule rich_listTheory.IS_PREFIX_LENGTH >> simp[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`,`ee`,`H`,`th`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  gvs[same_blocks_def]
QED

Theorem memory_convert_continuation:
  expr_post ctx func cenv cx e es sa sm s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = sm.cs_current_bb /\
  t0.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type typ /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
    (StackValue ann op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v1,ee) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\ ptr_buf_ok cenv e x G t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  body_inv tops ctx cenv cx /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) typ v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert typ [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\ ptr_val_ok cx typ v op H th ss /\
      ptr_buf_ok cenv (TypeBuiltin ann Convert typ [e]) op H ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> drule exprSimConvertTheory.expr_body_pre_convert >> strip_tac >> gvs[] >>
  `~cx.in_deploy` by gvs[bodySimTheory.body_inv_def] >>
  `?w. eval_operand x t0 = SOME w` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_all memory_source_packet >> strip_tac >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  `~is_word_type ann` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `?tv2. evaluate_type (get_tenv cx) ann = SOME tv2` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[vyperASTTheory.expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `type_memory_bytes cenv ann < dimword(:256)` by
    (qpat_x_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `val_wf tv v1` by metis_tac[value_has_type_memory_wf] >>
  drule_all memory_convert_dispatch >>
  Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv ann` >>
  simp[as_stack_val_def] >> strip_tac
  >- suspend "widen"
  >> suspend "cast"
QED

Resume memory_convert_continuation[widen]:
  qpat_x_assum `!ty' ann'. _` (qspecl_then [`ty`,`ann`] mp_tac) >>
  Cases_on `compile_bytestring_widen_copy (type_memory_bytes cenv ann) (Var src)
    (type_memory_bytes cenv (lowered_value_type cenv e)) sm` >>
  gvs[as_stack_val_def] >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_widen_copy _ _ _ sm = (op,sb)` >>
  drule_all memory_widen_compiler_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[same_blocks_def] >>
     fs[same_blocks_def, IS_PREFIX_APPEND, inst_extends_def,
        emitted_insts_def, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
   type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv ann` by
    decide_tac >>
  drule_all memory_widen_semantic_success >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by simp[] >>
  drule_all memory_widen_counted_destination_post >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  irule memory_success_summary >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`t`,`Var src`] >> gvs[]
QED

Resume memory_convert_continuation[cast]:
  qpat_x_assum `!ty' ann'. _` (qspecl_then [`ty`,`ann`] mp_tac) >>
  Cases_on `compile_type_convert (Var src) (mk_convert_op (expr_type e) ann) sm` >>
  gvs[as_stack_val_def] >> strip_tac >> gvs[] >>
  rename1 `compile_type_convert _ _ sm = (op,sb)` >>
  qspecl_then [`expr_type e`,`ann`] mp_tac memory_convert_shapes >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `i` (qx_choose_then `n`
    (map_every assume_tac o CONJUNCTS))) >>
  `compile_type_convert (Var src) (ConvBytestringCast n i) sm = (op,sb)` by fs[] >>
  drule memory_cast_compiler_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[same_blocks_def] >>
     fs[same_blocks_def, IS_PREFIX_APPEND, inst_extends_def,
        emitted_insts_def, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `i < dimword(:256) /\ n < dimword(:256)` by
    (gvs[evaluate_type_def, AllCaseEqs()]) >>
  `type_memory_bytes cenv ann <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    decide_tac >>
  Cases_on `convert_result cx (expr_type e) ann v1`
  >- suspend "cast_normal"
  >> suspend "cast_exit"
QED

Resume memory_convert_continuation[cast_normal]:
  qpat_assum `convert_result _ _ _ _ = INL _`
    (fn th => rewrite_tac[GSYM th]) >>
  drule_all memory_cast_counted_destination_post >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  irule memory_success_summary >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`t`,`Var src`] >> gvs[]
QED

Resume memory_convert_continuation[cast_exit]:
  `val_in_memory tv v1 (w2n w) t0.vs_memory` by
    (qpat_assum `!m. mem_agree_outside _ _ m ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  drule_all memory_cast_counted_exit >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,`r`] >> simp[] >>
  Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def, fragExecTheory.exit_result_def]
QED

Finalise memory_convert_continuation
