(* Memory-checked word operand lists: exprSimPrecompiles' lower_typed_args_sim
   on the memory-counted contract (expr_sim_mem), keeping the allocation
   history and the frontier across the operands. *)
Theory bodyArgsMemory
Ancestors
  exprSimMemDefs exprSimPrecompiles exprSimWordArgs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasPathMem allocaHistory
  exprLowering exprLoweringProps fragExec compileEnv
  bodyMemoryPreds exprSimHyps gasStorage
  vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState list

(* typed_args_ready with each operand's memory-counted simulation. *)
Definition typed_args_ready_mem_def:
  typed_args_ready_mem ctx func cenv cx arg_ty Inv [] = T /\
  typed_args_ready_mem ctx func cenv cx arg_ty Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim_mem ctx func cenv cx (arg_ty e) e es /\
       is_word_type (expr_type e) /\
       IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es =
                    (res, es') ==> expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es =
                  (INL v, es') ==> Inv es')) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      typed_args_ready_mem ctx func cenv cx arg_ty Inv args))
End

Theorem typed_args_ready_mem_head:
  typed_args_ready_mem ctx func cenv cx arg_ty Inv (e::args) /\ Inv es ==>
    expr_sim_mem ctx func cenv cx (arg_ty e) e es /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!res es'. (do r <- eval_expr cx e; read_result cx r od) es =
                 (res, es') ==> expr_res_ok res) /\
    (!v es'. (do r <- eval_expr cx e; read_result cx r od) es =
               (INL v, es') ==> Inv es')
Proof
  simp[typed_args_ready_mem_def] >> metis_tac[]
QED

Theorem typed_args_ready_mem_tail:
  typed_args_ready_mem ctx func cenv cx arg_ty Inv (e::args) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
  typed_args_ready_mem ctx func cenv cx arg_ty Inv args
Proof
  simp[typed_args_ready_mem_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

(* The operands' run keeps the invariant. *)
Theorem typed_args_ready_mem_inv:
  !args es vs es' ctx.
    typed_args_ready_mem ctx func cenv cx arg_ty Inv args /\ Inv es /\
    eval_exprs cx args es = (INL vs, es') ==>
    Inv es'
Proof
  Induct >- simp[eval_exprs_nil] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  rewrite_tac[eval_exprs_cons_action] >>
  qabbrev_tac `hd = bind (eval_expr cx h) (read_result cx)` >>
  simp[Once bind_def] >>
  Cases_on `hd es` >> rename1 `hd es = (rr, es1)` >>
  Cases_on `rr` >> simp[] >>
  simp[bind_def, return_def, AllCaseEqs()] >> strip_tac >>
  unabbrev_all_tac >>
  drule_all typed_args_ready_mem_head >> strip_tac >>
  `Inv es1` by metis_tac[] >>
  `typed_args_ready_mem ctx func cenv cx arg_ty Inv args` by
    metis_tac[typed_args_ready_mem_tail] >>
  metis_tac[]
QED

Theorem typed_args_mem_head_admissible:
  typed_args_ready_mem ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  `Inv (es with gas_obs := gs)` by metis_tac[] >>
  drule_all typed_args_ready_mem_head >> strip_tac >>
  first_x_assum irule >> qexists_tac `ee` >> gvs[bind_def]
QED

Theorem typed_args_mem_marked_facts:
  typed_args_ready_mem ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) mid r ==>
  Inv (mid with gas_obs := []) /\
  typed_args_ready_mem ctx func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  fs[] >> rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) typed_args_ready_mem_head) >>
  strip_tac >>
  `Inv (mid with gas_obs := [])` by metis_tac[] >>
  `typed_args_ready_mem ctx func cenv cx arg_ty Inv args` by
    (irule (CONV_RULE (DEPTH_CONV ETA_CONV) typed_args_ready_mem_tail) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV)
           forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Theorem lower_typed_args_nil_sim_mem:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx, func) cx st0 (eval_exprs cx []) (es, s0)
    (\H rr ee t. ?vs. rr = INL vs /\
       typed_args_post H ctx func cenv cx es sa s0 ee [] [] vs t /\
       t.vs_current_bb = sa.cs_current_bb /\
       t.vs_inst_idx = LENGTH sa.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\H rr ee r. wb_args_exit rr r)
Proof
  rpt strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_explicit_def,
       eval_exprs_nil, gas_marked_path_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s0`] >>
  simp[cj 1 gas_path_mem_rules, typed_args_post_def, wb_frame_refl] >>
  disj1_tac >> rpt strip_tac >>
  `(es with gas_obs := []).accounts = es.accounts /\
   (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
  metis_tac[storage_well_formed_on_backends]
QED

Theorem lower_typed_args_sim_mem:
  !args ctx func cenv cx arg_ty Inv st0 es sa xs sb s0.
    typed_args_ready_mem ctx func cenv cx arg_ty Inv args /\ Inv es /\
    (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
    ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx, func) cx st0 (eval_exprs cx args) (es, s0)
      (\H rr ee t. ?vs. rr = INL vs /\
         typed_args_post H ctx func cenv cx es sa s0 ee args xs vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\H rr ee r. wb_args_exit rr r)
Proof
  Induct
  >- (simp[lower_word_args_nil, eval_exprs_nil] >> rpt strip_tac >>
      irule lower_typed_args_nil_sim_mem >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `typed_args_ready_mem ctx func cenv cx arg_ty Inv (e::args)` >>
  `wb_args_shape cenv arg_ty args` by metis_tac[wb_args_shape_tail] >>
  gvs[lower_word_args_cons] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (qpat_x_assum `wb_args_shape _ _ (_::_)` mp_tac >>
     rewrite_tac[wb_args_shape_def] >>
     disch_then (qspec_then `e` mp_tac) >> simp[] >>
     disch_then drule >> simp[]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[typed_args_mem_head_admissible] >>
  `storage_trace_frame (eval_exprs cx args)` by
    simp[evaluate_storage_trace_frame] >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `!v. storage_trace_frame (bind (eval_exprs cx args) (\vs. return (v::vs)))` by
    (gen_tac >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_return]) >>
  drule_all typed_args_ready_mem_head >> strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_exprs_cons_action] >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           rewrite_tac[eval_exprs_cons_action] >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume lower_typed_args_sim_mem[head_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?v. _`
    (drule_then (qx_choose_then `v` strip_assume_tac)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?v. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?obs. es_end.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (bind (eval_expr cx e) _)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `es_end.storage_trace = _` kall_tac >>
  drule_all typed_args_mem_marked_facts >> strip_tac >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) t /\
     storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _ /\ _`
       drule >> simp[expr_post_def]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `!ctx func cenv cx arg_ty Inv st0 es sa xs sb s0. _`
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `arg_ty`, `Inv`, `st0`,
                  `es_end with gas_obs := []`, `s1`, `ys`, `sb`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
      rewrite_tac[eval_exprs_cons_action] >>
      irule gas_bad_storage_at_bind_right >>
      qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _` (irule_at Any) >>
      simp[] >> irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_return])
  >- (qpat_x_assum `gas_summary_at _ _ _ (eval_exprs _ _) _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end'.storage_trace`)
       >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
           rewrite_tac[eval_exprs_cons_action] >>
           irule gas_bad_storage_at_bind_right >>
           qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _` (irule_at Any) >>
           simp[] >> irule gas_bad_storage_at_bind_left >>
           simp[storage_trace_frame_return] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end'.storage_trace)
         es_end'.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume lower_typed_args_sim_mem[head_exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `expr_exit res r` by metis_tac[] >>
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED

Resume lower_typed_args_sim_mem[head_exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  irule_at Any wb_args_head_exempt_cert >> goal_assum (drule_at Any)
QED

Resume lower_typed_args_sim_mem[tail_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?vs. _`
    (drule_then (qx_choose_then `vs` strip_assume_tac)) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?vs. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?obs'. es_end'.storage_trace = es_end.storage_trace ++ obs'` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (eval_exprs _ _)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end'.storage_trace ==>
       valid_horizon cx st0 H es_end.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `es_end'.storage_trace = _` kall_tac >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t'`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es_end.storage_trace` by metis_tac[] >>
  `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  irule typed_args_post_cons >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)` >> gvs[]
QED

Resume lower_typed_args_sim_mem[tail_exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `wb_args_exit res r` by metis_tac[] >>
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED

Resume lower_typed_args_sim_mem[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED

Finalise lower_typed_args_sim_mem

(* typed_args_ready_mem from the operands' body induction hypotheses. *)
Theorem typed_args_ready_mem_of_body:
  !args tops ctx func cenv cx env arg_ty.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx args ==>
    typed_args_ready_mem ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  Induct >> simp[typed_args_ready_mem_def, body_exprs_mem_ok_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env h es /\ is_word_type (expr_type h)` by
        metis_tac[] >>
      rpt conj_tac
      >- metis_tac[body_expr_mem_ok_def]
      >- first_assum ACCEPT_TAC
      >- metis_tac[expr_body_pre_type_evaluates]
      >- (rpt strip_tac >> drule_all expr_body_pre_stack_result >> simp[]) >>
      rpt strip_tac >> drule_all expr_body_pre_stack_result >> simp[]) >>
  disch_tac >>
  qpat_x_assum `!tops ctx func cenv cx env arg_ty. _` irule >>
  metis_tac[]
QED
