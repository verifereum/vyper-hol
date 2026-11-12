Theory bodyPtrTypeBuiltinsExtract32Callback
Ancestors
  bodyPtrTypeBuiltinsExtract32Ready bodyPtrTypeBuiltinsExtract32Assembly
  bodyPtrTypeBuiltinsExtract32Entry exprSimExtract32Source exprSimExtract32Post
  exprSimExtract32ReadyFacts exprBopSimProps exprSimHypsDefs exprSimHyps
  gasSummaryComposePtr gasSummary bodyPtrDefs bodyPtrPreds exprLoweringProps
  loweringPosts compileEnv vyperState vyperContext vyperAST vyperTypeSystem
  exprOperandVar valueEncoding words list finite_map vyperValue
  bodyPtrEnvBuiltinsMethodTyping vyperTyping exprSimSource freshWrites fragExec

Theorem extract32_callback_ptr_ready:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [src;off] /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 typ [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\ is_uint_type (expr_type off) /\
  lower_value compile_expr cenv (expr_type src) src sa = (Var sv,sx) /\
  compile_bytestring_src (Var sv) sx = ((Var len,Var data),sb) /\
  lower_value compile_expr cenv ty off sb = (offop,sc) /\
  compile_extract32_load (Var len) (Var data) offop sc = (raw,sd) /\
  compile_clamp_basetype raw typ sd = (op,se) /\
  fn_has_code sa se func /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (vyperState$bind (eval_expr cx src) (read_result cx))
    (es,s0,G0,tn0) left (INL (BytesV bs)) mid G tn (OK t) /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (vyperState$bind (eval_expr cx off) (read_result cx))
    (mid with gas_obs := [],u,H,th) right (INL (IntV i)) fin J un (OK v) /\
  0 <= i /\
  expr_post ctx func cenv cx src es sa sb s0
    (mid with gas_obs := []) (BytesV bs) (Var sv) u /\
  expr_post ctx func cenv cx off (mid with gas_obs := []) sb sc u
    (fin with gas_obs := []) (IntV i) offop v /\
  not_fresh_at sb sv /\ not_fresh_at sb len /\ not_fresh_at sb data /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) J un v /\
  eval_operand (Var sv) v = SOME (n2w p) /\
  eval_operand (Var len) v = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) v = SOME (n2w (p+32)) /\
  op_taint un (Var len) = {} /\ op_prov J (Var len) = NONE /\
  (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers J un data v n) /\
  v.vs_current_bb = sc.cs_current_bb /\ v.vs_inst_idx = LENGTH sc.cs_current_insts /\
  ghost_inv d cenv cx (fin with gas_obs := []) J un v /\
  ptr_val_ok cx (post_value_type cenv off) (IntV i) offop J un v /\
  ghost_kept cenv es sa G0 tn0 s0 J un ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (vyperState$bind
      (lift_sum (evaluate_type_builtin cx Extract32 typ
        [expr_type src;expr_type off] [BytesV bs;IntV i])) (\w. return (Value w)))
    (fin with gas_obs := [],v,J,un)
    (\res ef K kn z. ?w. res = INL (Value w) /\
      vv_post ctx func cenv cx (TypeBuiltin ann Extract32 typ [src;off])
        es sa se s0 ef (Value w) (StackValue ty op) z /\
      z.vs_current_bb = se.cs_current_bb /\ z.vs_inst_idx = LENGTH se.cs_current_insts /\
      ghost_inv d cenv cx ef K kn z /\
      ptr_vv_ok cx (post_value_type cenv (TypeBuiltin ann Extract32 typ [src;off]))
        (Value w) (StackValue ty op) ef K kn z /\
      ghost_kept cenv es sa G0 tn0 s0 K kn)
    (\res ef gt r. expr_exit res r)
Proof
  strip_tac >> drule_all extract32_stage_cuts >> strip_tac >>
  `?bt. typ = BaseT bt /\ extract32_result_base_ok bt /\ ann = typ` by
    metis_tac[extract32_body_pre_shape] >> gvs[] >>
  `evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt)` by
    metis_tac[extract32_ready_result_evaluates] >>
  `is_word_type (BaseT bt)` by metis_tac[extract32_ready_result_word] >>
  `case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T` by metis_tac[extract32_ready_result_width] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := []) /\
   expr_body_pre cenv cx env off (mid with gas_obs := [])` by
    (drule_all extract32_marked_offset_ptr_sim >> metis_tac[]) >>
  `?k. expr_type off = BaseT (UintT k)` by gvs[is_uint_type_def] >>
  `evaluate_type (get_tenv cx) (expr_type off) = SOME (BaseTV (UintT k))` by
    (drule_all expr_body_pre_type_evaluates >> simp[evaluate_type_def, AllCaseEqs()]) >>
  suspend "operands"
QED

Resume extract32_callback_ptr_ready[operands]:
  gvs[] >>
  `value_has_type (BaseTV (UintT k)) (IntV i) /\ ~v.vs_halted` by
    (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)
       method_id_marked_operand_facts >> simp[] >>
     disch_then drule_all >> metis_tac[]) >>
  `k <= 256` by
    (qpat_assum `evaluate_type _ (BaseT (UintT k)) = _` mp_tac >>
     simp[NoAsms, evaluate_type_def, AllCaseEqs()]) >>
  `Num i < dimword(:256)` by
    (qpat_assum `value_has_type _ (IntV i)` mp_tac >>
     simp[NoAsms, value_has_type_def] >> strip_tac >>
     irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >>
     simp[wordsTheory.dimword_def]) >>
  `eval_operand offop v = SOME (n2w (Num i)) /\
   op_prov J offop = NONE /\ op_taint un offop = {}` by
    (irule extract32_offset_scalar_view >>
     qpat_assum `expr_post _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_arg >> conj_tac
     >- gvs[expr_body_pre_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (qpat_assum `expr_body_pre _ _ _ src _` (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `?q. eval_operand (Var sv) v = SOME (n2w q) /\
    eval_operand (Var data) v = SOME (n2w (q+32)) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) q v.vs_memory /\
    LENGTH bs < dimword(:256) /\ q+32+LENGTH bs < dimword(:256)` by
    (irule extract32_saved_source_view >>
     qpat_assum `expr_post _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >> qexists_tac `p` >> simp[]) >>
  suspend "finish"
QED

Resume extract32_callback_ptr_ready[finish]:
  `is_word_type (expr_type off)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `not_fresh_at sc len /\ not_fresh_at sc data /\
   sa.cs_next_var <= sb.cs_next_var` by metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `sa.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `lower_value _ _ _ src _ = _`
       (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> strip_tac >>
     qspecl_then [`Var sv`,`sx`] mp_tac ci_mono_compile_bytestring_src >>
     simp[ci_mono_def] >> decide_tac) >>
  `cs_extends sc se` by metis_tac[cs_extends_trans] >>
  `cs_extends sa sc` by metis_tac[cs_extends_trans] >>
  `fn_has_code sc se func` by
    (qspecl_then [`sa`,`sc`,`se`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ (es,s0,G0,tn0) _ _ _ _ _ _`
       (mp_tac o MATCH_MP gas_marked_exec_ptr_exec) >>
     disch_then (mp_tac o MATCH_MP (CONV_RULE (DEPTH_CONV ETA_CONV) bop_marked_scopes_dom)) >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  simp[evaluate_type_builtin_def, expr_type_def] >>
  irule (SRULE [post_value_type_word, expr_type_def] extract32_tail_ptr_ready) >>
  qpat_assum `expr_post _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_extract32_load _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_clamp_basetype _ _ _ = _` (irule_at Any) >>
  simp[] >> qexists_tac `q` >> simp[] >> metis_tac[]
QED

Finalise extract32_callback_ptr_ready
