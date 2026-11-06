(* Counted topic evaluation for the RawLog body case. *)
Theory bodySimRawLogTopics
Ancestors
  bodySimRawLogTails bodySimRawLogBodySource bodySim exprSimHypsDefs
  exprSimPrecompiles exprSimWordArgs exprSimHyps exprSimDefs gasOutcome
  exprLoweringProps vyperAST vyperValue compileEnv list
  gasSummary exprSimRawLog vyperState

Theorem raw_log_body_topics_sim:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  lower_word_args cenv expr_type topics sa = (ops,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx topics) (es,s0)
    (\rr ee t. ?vs. rr = INL vs /\
       typed_args_post ctx func cenv cx es sa s0 ee topics ops vs t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >>
  `typed_args_ready ctx func cenv cx expr_type
     (\s. expr_sim_inv cenv cx env s) topics` by
    metis_tac[raw_log_body_topics_ready] >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  irule lower_typed_args_sim >> simp[] >>
  qexists_tac `\s. expr_sim_inv cenv cx env s` >> simp[] >>
  qexists_tac `expr_type` >> simp[]
QED

Theorem raw_log_topics_marked_post:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s0)
    marks (INL vs) ee r /\
  typed_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) topics ops vs t ==>
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  wb_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) ops vs t
Proof
  strip_tac >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  conj_tac >- (drule_all raw_log_body_topics_success >> simp[]) >>
  drule_all raw_log_body_topics_values >> strip_tac >>
  irule raw_log_topics_post_wb >> simp[] >> qexists_tac `topics` >> simp[]
QED

(* The body induction hypothesis for data is available at a marked topic
   endpoint, not merely at the unmarked source evaluation. *)
Theorem raw_log_marked_data_ready:
  body_inv tops ctx cenv cx /\
  body_exprs_ok cx
    [Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] /\
  LENGTH topics <= n /\
  expr_sim_inv cenv cx env es /\
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  (!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s) /\
  gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s0)
    marks (INL vs) ee (OK t) ==>
  expr_sim ctx func cenv cx (expr_type data) data (ee with gas_obs := [])
Proof
  strip_tac >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all raw_log_literal_read_success >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  `body_expr_ok cx data` by
    (qpat_x_assum `!ann'. _` (qspec_then `ann` strip_assume_tac) >>
     gvs[] >> drule_all raw_log_body_data_after_topics >> simp[]) >>
  `expr_body_pre cenv cx env data (ee with gas_obs := [])` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `body_expr_ok cx data`
    (assume_tac o PURE_REWRITE_RULE [body_expr_ok_def]) >>
  metis_tac[]
QED
