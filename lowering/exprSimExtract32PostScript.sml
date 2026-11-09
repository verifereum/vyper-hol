(* Post/frame boundaries for dynamic bytes and unsigned extract32 offsets. *)
Theory exprSimExtract32Post
Ancestors
  exprSimExtract32Read exprSimExtract32Source exprSimHash exprSimWordArgs
  exprSimOperands exprSimOps exprOperandVar exprBopSimProps
  loweringPosts valueEncodingProofs valueEncoding exprLoweringProps builtinBytes
  stmtSimLogArgs freshWrites exprSafeOperand fragExec exprReasonOperand
  exprSimHypsDefs exprSimHyps vyperTypeSystem vyperTyping exprSimVVFrame
  vyperValue vyperAST integer_word words compileEnv
Libs
  monadsyntax

Theorem extract32_source_post_view:
  expr_post ctx func cenv cx src es sa sm s0 es' (BytesV bs) op s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) ==>
  ?p. eval_operand op s = SOME (n2w p) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
    mem_word_at p s.vs_memory = n2w (LENGTH bs) /\
    LENGTH bs < dimword (:256) /\ p + 32 + LENGTH bs < dimword (:256)
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
   ~is_word_type (expr_type src)` by simp[evaluate_type_def, is_word_type_def] >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  `expr_val_rel cx (expr_type src) (BytesV bs) op s` by gvs[expr_post_def] >>
  drule_all expr_val_rel_memory >> strip_tac >>
  drule_all hash_post_footprint_bound >>
  simp[val_footprint_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> strip_tac >>
  qexists `b` >> gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem extract32_post_operand_kept:
  expr_post ctx func cenv cx e es sm sb s es' v op s' /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) ==>
  !w. eval_operand x s = SOME w ==> eval_operand x s' = SOME w
Proof
  strip_tac >> rpt strip_tac >> irule eval_operand_frame >>
  simp[] >> qexistsl [`sm`,`s`] >> simp[] >>
  gvs[expr_post_def]
QED

Theorem extract32_posts_to_vv_post_frame:
  expr_post ctx func cenv cx src es sa sm s0 es1 (BytesV bs) src_op s1 /\
  expr_post ctx func cenv cx off es1 sm st3 s1 es2 (IntV i) off_op s2 /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv st3 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= st3.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func cenv cx es2 u /\
  u.vs_memory = s2.vs_memory /\ u.vs_allocas = s2.vs_allocas /\
  (!x w. not_fresh_at st3 x /\ lookup_var x s2 = SOME w ==> lookup_var x u = SOME w) /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  eval_operand op u = SOME (typed_val_to_w256 tv v) ==>
  vv_post ctx func cenv cx (TypeBuiltin ann Extract32 target [src;off])
    es sa final s0 es2 (Value v) (StackValue ty op) u
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 s1` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es1 sm s1 s2` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es sa s0 s2` by metis_tac[wb_frame_trans] >>
  `sa.cs_next_var <= st3.cs_next_var` by decide_tac >>
  `wb_frame cenv es sa s0 u` by
    (irule wb_frame_readonly_tail >> qexistsl [`st3`,`s2`] >> simp[]) >>
  `~expr_has_effect src /\ ~expr_has_effect off ==>
   pure_frame cenv func es sa s0 u` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 s1` by metis_tac[expr_post_pure_frame] >>
     `pure_frame cenv func es1 sm s1 s2` by metis_tac[expr_post_pure_frame] >>
     irule exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `s2` >> simp[] >>
     match_mp_tac exprSimPropsTheory.pure_frame_trans >>
     qexistsl_tac [`es1`, `sm`, `s1`] >> fs[wb_frame_def]) >>
  irule vv_post_word_intro >> simp[expr_type_def, expr_has_effect_thm] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem extract32_prepare_post:
  expr_post ctx func cenv cx src es sa sm s0 es' (BytesV bs) op s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  compile_bytestring_src op sm = ((len,dp),sb) /\
  fresh_vars_wrt sm s /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var ==>
  ?u p. run_inst_seq (emitted_insts sm sb) s = OK u /\
    expr_post ctx func cenv cx src es sa sb s0 es' (BytesV bs) op u /\
    eval_operand op u = SOME (n2w p) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand dp u = SOME (n2w (p+32)) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p u.vs_memory /\
    LENGTH bs < dimword (:256) /\ p+32+LENGTH bs < dimword (:256) /\
    fresh_vars_wrt sb u
Proof
  strip_tac >> drule_all extract32_source_post_view >> strip_tac >>
  `p + 32 < dimword (:256)` by decide_tac >>
  drule_all extract32_prepare_run >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es' u` by
    (irule hash_readonly_state_rel >> qexistsl [`s`,`sm`] >>
     gvs[expr_post_def]) >>
  `!n b sz. local_region cenv es'.scopes u n b sz <=>
             local_region cenv es'.scopes s n b sz` by
    (rpt gen_tac >> simp[local_region_def] >>
     eq_tac >> strip_tac >> goal_assum (drule_at Any) >> simp[] >>
     `not_fresh_at sm p'` by
       (gvs[local_ptrs_reserved_def] >> metis_tac[]) >> metis_tac[]) >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (qspec_then `op` (qspec_then `sm` mp_tac) ci_mono_compile_bytestring_src >>
     simp[ci_mono_def]) >>
  `expr_val_at cenv cx (expr_type src) sa sb es' (BytesV bs) op u` by
    (`expr_val_at cenv cx (expr_type src) sa sm es' (BytesV bs) op s` by
       gvs[expr_post_def] >>
     pop_assum mp_tac >> simp[expr_val_at_def] >>
     simp[is_word_type_def] >> strip_tac
     >- (disj1_tac >> qexistsl [`aid`,`b`,`sz`] >>
         asm_rewrite_tac[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
     >- (disj2_tac >> disj1_tac >> qexistsl [`n`,`b`,`sz`] >>
         asm_rewrite_tac[]) >> simp[]) >>
  qexistsl [`u`,`p`] >> simp[] >>
  `wb_frame cenv es sa s0 u` by
    (irule wb_frame_readonly_tail >> qexistsl [`sm`,`s`] >>
     simp[] >> metis_tac[expr_post_frame]) >>
  gvs[expr_post_def, wb_frame_def] >>
  conj_tac
  >- (gvs[expr_val_rel_def] >> qexists `n2w p` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> match_mp_tac exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `s` >>
  rpt conj_tac >- res_tac >- first_assum ACCEPT_TAC >>
  simp[]
QED


Theorem extract32_offset_post_view:
  expr_sim_inv cenv cx env es1 /\
  expr_post ctx func cenv cx src es sa sm s0 es1 (BytesV bs) src_op s1 /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  expr_post ctx func cenv cx off es1 sm sb s1 es2 (IntV i) off_op s2 /\
  (!z. src_op = Var z ==> not_fresh_at sm z) /\
  (!z. len = Var z ==> not_fresh_at sm z) /\
  (!z. dp = Var z ==> not_fresh_at sm z) /\
  (!l. src_op <> Label l) /\ (!l. len <> Label l) /\ (!l. dp <> Label l) /\
  eval_operand src_op s1 = SOME (n2w p) /\
  eval_operand len s1 = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s1 = SOME (n2w (p+32)) /\
  expr_type off = BaseT (UintT k) /\
  evaluate_type (get_tenv cx) (expr_type off) = SOME (BaseTV (UintT k)) /\
  0 <= i /\ Num i < dimword (:256) /\
  LENGTH bs < dimword (:256) /\ p+32+LENGTH bs < dimword (:256) ==>
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s2.vs_memory /\
  eval_operand len s2 = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s2 = SOME (n2w (p+32)) /\
  eval_operand src_op s2 = SOME (n2w p) /\
  eval_operand off_op s2 = SOME (n2w (Num i))
Proof
  strip_tac >>
  `expr_val_rel cx (expr_type src) (BytesV bs) src_op s2` by
    (irule log_argument_value_kept >>
     conj_tac >- simp[] >>
     qexistsl [`cenv`,`es1`,`s1`,`sa`,`sm`] >> simp[] >>
     conj_tac >- (simp[] >> irule log_arg_clear_base >> metis_tac[]) >>
     conj_tac >- gvs[expr_post_def] >>
     conj_tac >- metis_tac[expr_post_frame] >>
     gvs[expr_post_def]) >>
  `eval_operand src_op s2 = SOME (n2w p)` by
    metis_tac[extract32_post_operand_kept] >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s2.vs_memory` by
    (`~is_word_type (expr_type src)` by simp[is_word_type_def] >>
     drule_all expr_val_rel_memory >> strip_tac >>
     `p < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  simp[] >> conj_tac
  >- metis_tac[extract32_post_operand_kept] >>
  conj_tac
  >- metis_tac[extract32_post_operand_kept] >>
  `expr_val_rel cx (expr_type off) (IntV i) off_op s2` by gvs[expr_post_def] >>
  `is_word_type (expr_type off)` by simp[is_word_type_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  drule_all expr_val_rel_typed >>
  simp[is_word_type_def, typed_val_to_w256_def, val_to_w256_def,
       integer_wordTheory.i2w_def, integerTheory.INT_NOT_LT]
QED

Theorem extract32_prepare_available:
  lower_value compile_expr cenv ty src sa = (src_op,sx) /\
  local_ptrs_reserved cenv sa /\
  emit_op MLd [src_op] sx = (len,sy) /\
  emit_op ADD [src_op; Lit 32w] sy = (dp,sm) ==>
  (!z. src_op = Var z ==> not_fresh_at sm z) /\
  (!z. len = Var z ==> not_fresh_at sm z) /\
  (!z. dp = Var z ==> not_fresh_at sm z)
Proof
  strip_tac >>
  `!z. src_op = Var z ==> not_fresh_at sx z` by
    metis_tac[compile_lower_value_var] >>
  `sx.cs_next_var <= sm.cs_next_var /\
   (!z. len = Var z ==> not_fresh_at sm z) /\
   (!z. dp = Var z ==> not_fresh_at sm z)` by
    (gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def, fresh_id_def,
         fresh_var_def, emit_def, comp_ignore_bind_def] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem extract32_tail_available:
  lower_value compile_expr cenv ty src sa = (src_op,sx) /\
  local_ptrs_reserved cenv sa /\
  emit_op MLd [src_op] sx = (len,sy) /\
  emit_op ADD [src_op; Lit 32w] sy = (dp,sm) /\
  local_ptrs_reserved cenv sm /\
  lower_value compile_expr cenv off_ty off sm = (off_op,st3) /\
  sm.cs_next_var <= st3.cs_next_var ==>
  (!z. len = Var z ==> not_fresh_at st3 z) /\
  (!z. dp = Var z ==> not_fresh_at st3 z) /\
  (!z. off_op = Var z ==> not_fresh_at st3 z)
Proof
  strip_tac >> drule_all extract32_prepare_available >> strip_tac >>
  `!z. off_op = Var z ==> not_fresh_at st3 z` by
    metis_tac[compile_lower_value_var] >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem extract32_prepared_not_label:
  emit_op MLd [src] sa = (len,sb) /\
  emit_op ADD [src; Lit 32w] sb = (dp,sc) ==>
  (!l. len <> Label l) /\ (!l. dp <> Label l)
Proof
  metis_tac[emit_op_safe_operand, safe_operand_def]
QED

Theorem extract32_read_grows:
  extract32_straight_read_frame m /\ m sa = (r,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> drule_all extract32_read_extends >> strip_tac >> simp[] >>
  simp[cs_extends_def] >> qexists `[]` >> simp[]
QED

Theorem extract32_stage_cuts:
  lower_value compile_expr cenv (expr_type src) src st = (src_op,st1) /\
  compile_bytestring_src src_op st1 = ((len,dp),st2) /\
  lower_value compile_expr cenv ty off st2 = (off_op,st3) /\
  compile_extract32_load len dp off_op st3 = (raw,st4) /\
  compile_clamp_basetype raw t st4 = (result,st5) /\
  fn_has_code st st5 func /\ local_ptrs_reserved cenv st ==>
  cs_extends st st1 /\ cs_extends st1 st2 /\ cs_extends st2 st3 /\
  cs_extends st3 st4 /\ cs_extends st4 st5 /\
  st.cs_next_var <= st1.cs_next_var /\ st1.cs_next_var <= st2.cs_next_var /\
  st2.cs_next_var <= st3.cs_next_var /\ st3.cs_next_var <= st4.cs_next_var /\
  st4.cs_next_var <= st5.cs_next_var /\
  fn_has_code st st1 func /\ fn_has_code st1 st2 func /\
  fn_has_code st2 st3 func /\ fn_has_code st3 st4 func /\ fn_has_code st4 st5 func /\
  local_ptrs_reserved cenv st1 /\ local_ptrs_reserved cenv st2 /\
  local_ptrs_reserved cenv st3 /\ local_ptrs_reserved cenv st4 /\ local_ptrs_reserved cenv st5
Proof
  strip_tac >> imp_res_tac (cj 2 compile_expr_grows) >>
  `extract32_straight_read_frame (compile_bytestring_src src_op) /\
   extract32_straight_read_frame (compile_extract32_load len dp off_op) /\
   extract32_straight_read_frame (compile_clamp_basetype raw t)` by
    simp[extract32_read_prepare, extract32_read_load, extract32_read_clamp_basetype] >>
  imp_res_tac extract32_read_grows >>
  `cs_extends st1 st5 /\ cs_extends st2 st5 /\ cs_extends st3 st5` by
    metis_tac[cs_extends_trans] >>
  imp_res_tac fn_has_code_split >> simp[] >>
  `local_ptrs_reserved cenv st1` by metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_reserved cenv st2` by metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_reserved cenv st3` by metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_reserved cenv st4` by metis_tac[local_ptrs_reserved_next_var] >>
  metis_tac[local_ptrs_reserved_next_var]
QED

Theorem extract32_offset_bounds:
  expr_body_pre cenv cx env off es /\
  expr_type off = BaseT (UintT k) /\
  (do r <- eval_expr cx off; read_result cx r od) es = (INL (IntV i),es') ==>
  0 <= i /\ Num i < dimword (:256)
Proof
  strip_tac >>
  `k <= 256` by
    (drule expr_body_pre_type_evaluates >>
     simp[evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  first_x_assum (qspec_then `IntV i` mp_tac) >>
  simp[value_has_type_def] >> strip_tac >> simp[] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists `2 ** k` >> simp[wordsTheory.dimword_def]
QED

Theorem extract32_compiled_offset_post_view:
  expr_body_pre cenv cx env src es /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv (BaseT (BytesT (Dynamic m))) src sa = (src_op,sx) /\
  emit_op MLd [src_op] sx = (len,sy) /\
  emit_op ADD [src_op; Lit 32w] sy = (dp,sm) /\
  expr_body_pre cenv cx env off es1 /\
  (do r <- eval_expr cx off; read_result cx r od) es1 = (INL (IntV i),es2) /\
  expr_post ctx func cenv cx src es sa sm s0 es1 (BytesV bs) src_op s1 /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  expr_post ctx func cenv cx off es1 sm sb s1 es2 (IntV i) off_op s2 /\
  eval_operand src_op s1 = SOME (n2w p) /\
  eval_operand len s1 = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s1 = SOME (n2w (p+32)) /\
  expr_type off = BaseT (UintT k) /\
  LENGTH bs < dimword (:256) /\ p+32+LENGTH bs < dimword (:256) ==>
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s2.vs_memory /\
  eval_operand len s2 = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s2 = SOME (n2w (p+32)) /\
  eval_operand src_op s2 = SOME (n2w p) /\
  eval_operand off_op s2 = SOME (n2w (Num i))
Proof
  strip_tac >>
  `!l. src_op <> Label l` by
    (drule lower_compile_expr_not_label >>
     disch_then irule >> qexists `env` >>
     qpat_x_assum `expr_body_pre _ _ _ src _` mp_tac >>
     simp[expr_body_pre_def, expr_sim_inv_def]) >>
  `(!l. len <> Label l) /\ (!l. dp <> Label l)` by
    metis_tac[extract32_prepared_not_label] >>
  `0 <= i /\ Num i < dimword (:256)` by metis_tac[extract32_offset_bounds] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (qpat_assum `expr_body_pre _ _ _ src _` (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `evaluate_type (get_tenv cx) (expr_type off) = SOME (BaseTV (UintT k))` by
    (qpat_assum `expr_body_pre _ _ _ off _` (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `(!z. src_op = Var z ==> not_fresh_at sm z) /\
   (!z. len = Var z ==> not_fresh_at sm z) /\
   (!z. dp = Var z ==> not_fresh_at sm z)` by
    metis_tac[extract32_prepare_available] >>
  `expr_sim_inv cenv cx env es1` by gvs[expr_body_pre_def] >>
  drule_all extract32_offset_post_view >> simp[]
QED

Theorem extract32_expr_post_start_gas_obs:
  expr_post ctx func cenv cx e (es with gas_obs := gs) sa sb s0 ee v op s =
  expr_post ctx func cenv cx e es sa sb s0 ee v op s
Proof
  simp[expr_post_def, locals_kept_def]
QED

Theorem extract32_expr_post_end_gas_obs:
  expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := gs) v op s =
  expr_post ctx func cenv cx e es sa sb s0 ee v op s
Proof
  simp[expr_post_def, expr_val_at_def, stmt_state_rel_def, state_rel_gas_obs]
QED
