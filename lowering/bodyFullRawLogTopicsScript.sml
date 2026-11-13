(* RawLog topics: join the checked suffix and pointwise contracts. *)
Theory bodyFullRawLogTopics
Ancestors
  bodyFullRawLogTopicsPost bodyFullRawLogTopicsSuffix bodyFullPreds
  gasOutcomeFullCompose bodyRawLogArgPre exprSimSource exprSimHypsDefs
  vyperTypeSystem vyperContext vyperValue vyperInterpreter vyperState vyperAST list

Theorem raw_log_topics_full:
  (!cenv cx env ann a n topics data dflt es vs es'.
    expr_body_pre cenv cx env
      (Call ann RawLog
        [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
         data] dflt) es /\
    body_exprs_full_ok cx
      [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
       data] /\ LENGTH topics <= n /\
    eval_exprs cx topics es = (INL vs,es') ==>
    expr_sim_inv cenv cx env es' /\
    expr_body_pre cenv cx env data es' /\ body_expr_full_ok cx data) ==>
  !topics DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx
   env ann n data dflt st0 sa sb shadow_sa shadow_sb ops es s G0 tn0.
  (!cenv ty e.
     gas_shadow_compiles (lower_value compile_expr cenv ty e)
       (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
  (!cenv xs.
     gas_shadow_compiles (compile_multi_exprs compile_expr cenv xs)
       (compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr xs))) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n))
        topics; data] dflt) es /\
  body_exprs_full_ok cx
    [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] /\
  compile_multi_exprs compile_expr cenv topics sa = (ops,sb) /\
  compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr topics)
    shadow_sa = (ops,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx topics) (es,s,G0,tn0)
    (\H res ee G tn t. ?vs. res = INL vs /\
      LENGTH topics = LENGTH vs /\ LENGTH ops = LENGTH vs /\
      EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs /\
      LIST_REL (\op v. eval_operand op t = SOME (event_value_to_word v)) ops vs /\
      EVERY (\op. op_taint tn op = {}) ops /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      wb_frame cenv es ee sa s t /\
      (~EXISTS expr_has_effect topics ==> pure_frame cenv func es sa s t) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
      expr_body_pre cenv cx env data ee /\ body_expr_full_ok cx data)
    (\H res ee gt r. expr_exit res r)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >> simp[expr_body_pre_def]) >>
  `expr_body_pre cenv cx env
     (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
       (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics) es` by
    (drule expr_body_pre_raw_log_arg >> disch_then irule >> simp[]) >>
  `LENGTH topics <= n` by
    (qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
          compatible_bound_def, builtin_args_length_ok_def]) >>
  `body_exprs_full_ok cx topics` by
    (irule body_make_array_children_full_ok >>
     qexistsl_tac [`ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n)`,
                   `Dynamic n`, `SOME (BaseT (BytesT (Fixed 32)))`] >>
     gvs[body_exprs_full_ok_def, builtin_args_length_ok_def, compatible_bound_def]) >>
  mp_tac raw_log_topics_suffix_full_under_compose >>
  (impl_tac >- MATCH_ACCEPT_TAC raw_log_topics_post_cons) >>
  disch_then (qspecl_then [`topics`, `[]`, `topics`] mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `!PG. gas_outcome_full _ _ _ _ _ _ _ _`
    (qspec_then `PG` assume_tac) >>
  irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!tail. eval_exprs _ _ _ = _`
    (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!cenv cx env ann a n topics data dflt es vs es'. _`
    (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
