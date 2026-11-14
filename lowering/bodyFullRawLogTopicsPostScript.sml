(* Pointwise composition at the RawLog topic boundary. *)
Theory bodyFullRawLogTopicsPost
Ancestors
  bodyFullPreds bodySimFull bodyRawLogArgPre exprSimSource exprSimProps
  exprSimWordArgs loweringPosts bodyPtrDefs exprLoweringProps
  vyperInterpreter vyperState vyperAST list finite_map
  loweringStateRelDefs loweringShapeDefs compileEnv vyperValue

Theorem raw_log_topics_ghost_cons[local]:
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin a (MakeArray elem bd) (pre ++ e::rest); data] dflt) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  expr_post H ctx func cenv cx e es sa sm s mid v op u /\
  ghost_kept_at lo cenv es sa G0 tn0 s G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 u G tn ==>
  ghost_kept_at lo cenv es sa G0 tn0 s G tn
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz <=>
             local_region cenv mid.scopes u n b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame_fwd >>
         qexistsl_tac [`s`, `sa`, `es.scopes`] >> gvs[expr_post_def] >> metis_tac[]) >>
     strip_tac >> irule local_region_frame >>
     conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `mid.scopes`, `u`] >>
     gvs[expr_post_def] >> metis_tac[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, ghost_kept_at_def] >>
  fs[ghost_kept_at_def] >> rpt strip_tac
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[not_fresh_at_mono]
  >- (`aid < sm.cs_next_id` by decide_tac >>
      `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `i IN tn1.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = _ /\ _ ==> _` irule >>
         reverse conj_tac >- simp[] >>
         qexistsl_tac [`aid`, `off`, `sz`] >> asm_rewrite_tac[]) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _` irule >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`aid`, `off`, `sz`] >> asm_rewrite_tac[]) >>
  metis_tac[]
QED

(* The successful cons case, with the suffix post expanded so its one
   endpoint and all frame/ghost anchors are visible to the consumer. *)
Theorem raw_log_topics_post_cons:
  !tops ctx func cenv cx env ann n pre e rest data dflt
   sa sm sb shadow_sa shadow_sm shadow_sb op ops
   H DF lo d es s G0 tn0 xs mid v u G1 tn1 ys ee vs t G tn.
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n))
        (pre ++ e::rest); data] dflt) es /\
  expr_body_pre cenv cx env e es /\
  expr_type e = BaseT (BytesT (Fixed 32)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  compile_multi_exprs compile_expr cenv rest sm = (ops,sb) /\
  lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
    shadow_sa = (op,shadow_sm) /\
  compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr rest)
    shadow_sm = (ops,shadow_sb) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sb.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := xs ++ tail) = (INL v,mid with gas_obs := tail)) /\
  expr_post H ctx func cenv cx e es sa sm s mid v op u /\
  expr_store_bound cx (expr_type e) v op u /\
  u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~u.vs_halted /\
  alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u /\
  ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 u /\
  ghost_kept_at lo cenv es sa G0 tn0 s G1 tn1 /\
  (!tail. eval_exprs cx rest (mid with gas_obs := ys ++ tail) =
      (INL vs,ee with gas_obs := tail)) /\
  (?ws. INL vs = INL ws /\ LENGTH rest = LENGTH ws /\
    LENGTH ops = LENGTH ws /\
    EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) ws /\
    LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) ops ws /\
    EVERY (\op. op_taint tn op = {}) ops /\
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
    wb_frame cenv mid ee sm u t /\
    (~EXISTS expr_has_effect rest ==> pure_frame cenv func mid sm u t) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv mid sm G1 tn1 u G tn /\
    (!op x. MEM op ops /\ op = Var x ==> not_fresh_at sb x) /\
    (!op l. MEM op ops ==> op <> Label l)) ==>
  (?ws. INL (v::vs) = INL ws /\ LENGTH (e::rest) = LENGTH ws /\
    LENGTH (op::ops) = LENGTH ws /\
    EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) ws /\
    LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) (op::ops) ws /\
    EVERY (\op. op_taint tn op = {}) (op::ops) /\
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    wb_frame cenv es ee sa s t /\
    (~EXISTS expr_has_effect (e::rest) ==> pure_frame cenv func es sa s t) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
    (!op' x. MEM op' (op::ops) /\ op' = Var x ==> not_fresh_at sb x) /\
    (!op' l. MEM op' (op::ops) ==> op' <> Label l))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `value_has_type (BaseTV (BytesT (Fixed 32))) v` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env e (es with gas_obs := xs ++ [])` by simp[] >>
     drule (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value) >>
     disch_then (qspecl_then [`v`, `mid with gas_obs := []`] mp_tac) >>
     simp[is_word_type_def, evaluate_type_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s G tn` by
    (drule_all raw_log_topics_ghost_cons >> simp[]) >>
  `wb_frame cenv es mid sa s u` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def] >> strip_tac >>
     rewrite_tac[wb_frame_def] >> asm_rewrite_tac[]) >>
  `wb_frame cenv es ee sa s t` by (drule_all wb_frame_trans >> simp[]) >>
  `(~expr_has_effect e /\ EVERY ($~ o expr_has_effect) rest) ==>
    pure_frame cenv func es sa s t` by
    (strip_tac >> fs[expr_post_def, wb_frame_def] >>
     drule_all pure_frame_trans >> simp[]) >>
  simp[] >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `eval_operand op u = SOME (event_value_to_word v)` by
    (fs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def] >>
     qpat_x_assum `!tv. _` (qspec_then `BaseTV (BytesT (Fixed 32))` mp_tac) >>
     simp[evaluate_type_def] >> strip_tac >>
     Cases_on `v` >>
     gvs[vyperTypingTheory.value_has_type_def,
         valueEncodingTheory.typed_val_to_w256_def,
         vyperEventTheory.event_value_to_word_def]) >>
  Cases_on `op` >>
  gvs[venomStateTheory.eval_operand_def,
      ptr_val_ok_def, ghost_kept_at_def, wb_frame_def,
      ptrDisciplineTheory.op_taint_def] >>
  rename1 `not_fresh_at sm x` >>
  qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  `not_fresh_at sb x` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[]) >>
  rpt strip_tac >> gvs[]
QED
