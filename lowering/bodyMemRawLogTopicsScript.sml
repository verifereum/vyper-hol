(* Memory-counted topics and reachable data for RawLog. *)
Theory bodyMemRawLogTopics
Ancestors
  bodyArgsMemory bodySimRawLogTopics bodySimRawLogBodySource
  gasSummary vyperState exprSimRawLog bodyMemoryPreds exprSimWordArgs exprSimHypsDefs compileEnv exprSimPrecompiles

Theorem raw_log_body_topics_sim_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  lower_word_args cenv expr_type topics sa = (ops,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx topics) (es,s0)
    (\rr ee t. ?vs. rr = INL vs /\
       typed_args_post ctx func cenv cx es sa s0 ee topics ops vs t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >>
  `typed_args_ready_mem ctx func cenv cx expr_type
     (expr_sim_inv cenv cx env) topics` by
    (irule typed_args_ready_mem_of_body >>
     reverse conj_tac >- metis_tac[] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  irule lower_typed_args_sim_mem >> simp[] >>
  qexists_tac `expr_sim_inv cenv cx env` >> simp[] >>
  qexists_tac `expr_type` >> simp[]
QED

Theorem raw_log_marked_data_ready_mem:
  body_inv tops ctx cenv cx /\
  body_exprs_mem_ok cx
    [Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] /\
  LENGTH topics <= n /\
  expr_sim_inv cenv cx env es /\
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  (!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s) /\
  gas_marked_exec T (ctx,func) (eval_exprs cx topics) (es,s0)
    marks (INL vs) ee (OK t) ==>
  expr_sim_mem ctx func cenv cx (expr_type data) data (ee with gas_obs := [])
Proof
  strip_tac >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all raw_log_literal_read_success >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  `body_expr_mem_ok cx data` by
    (qpat_x_assum `!ann'. _` (qspec_then `ann` strip_assume_tac) >>
     gvs[] >>
     qpat_x_assum `body_exprs_mem_ok _ _` mp_tac >>
     simp[body_exprs_mem_ok_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env data (ee with gas_obs := [])` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `body_expr_mem_ok cx data`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_mem_ok_def]) >>
  metis_tac[]
QED
