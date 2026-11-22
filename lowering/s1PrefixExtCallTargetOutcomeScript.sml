(* Request-prefix companion to bodyFullExtCallTargetOutcome. *)
Theory s1PrefixExtCallTargetOutcome
Ancestors
  s1PrefixPreds bodyFullExtCallTargetOutcome s1PrefixDefs s1PrefixOfVV
  bodyFullHashKeccakFixed vyperStorageFootprint vyperStorageTrace
  exprSimSource exprSimWordArgs vyperState vyperInterpreter gasOutcomeFull list

Theorem extcall_request_head_prefix:
  expr_type addr = BaseT AddressT /\
  body_exprs_full_ok cx [addr] /\ body_exprs_prefix_ok cx [addr] /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env addr es /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx [addr]) (es,s0,G0,tn0)
Proof
  strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H es.storage_trace`
  >- (`ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
        metis_tac[stmt_state_rel_allocas_below_fmp] >>
      `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (BaseT AddressT) addr es` by
        (fs[body_exprs_prefix_ok_def] >>
         metis_tac[CONJUNCT1 body_expr_prefix_ok_def]) >>
      `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (BaseT AddressT) addr es
         (st0,sa,sb,shadow_sa,shadow_sb,ao,s0,G0,tn0)` by
        (simp[expr_sim_full_pre_def] >>
         metis_tac[expr_body_pre_gas_admissible]) >>
      qpat_assum `expr_sim_prefix _ _ _ _ _ _`
        (drule_then assume_tac o REWRITE_RULE[expr_sim_prefix_def]) >>
      `!qe. SND (bind (eval_expr cx addr) (read_result cx) qe) =
            SND (eval_exprs cx [addr] qe)` by
        (gen_tac >> rewrite_tac[eval_exprs_cons_action] >>
         Cases_on `bind (eval_expr cx addr) (read_result cx) qe` >>
         rename1 `_ = (raw,mid)` >> Cases_on `raw` >>
         simp[bind_def, return_def, eval_exprs_nil]) >>
      drule gas_prefix_full_state_cong >> metis_tac[]) >>
  (* A valid request prefix would validate the input trace it extends. *)
  simp[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`,
                    `func`, `PG`, `G0`, `tn0`, `s0`] >>
      simp[storage_trace_domain_def, gas_origin_ptr_focus_nil]) >>
  rpt gen_tac >> strip_tac >>
  `storage_trace_frame (eval_exprs cx [addr])` by
    simp[evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
  `?more. obs_pre = es.storage_trace ++ more` by
    (pop_assum mp_tac >> rewrite_tac[GSYM APPEND_ASSOC] >>
     rewrite_tac[APPEND_EQ_APPEND] >> strip_tac
     >- metis_tac[] >>
     rename1 `es.storage_trace = obs_pre ++ more` >>
     `LENGTH more = 0` by
       (`LENGTH more + LENGTH obs_pre <= LENGTH obs_pre` by fs[] >>
        pop_assum mp_tac >> decide_tac) >>
     qexists_tac `[]` >> fs[]) >>
  gvs[] >>
  `valid_horizon cx st0 H es.storage_trace` by fs[valid_horizon_def] >>
  metis_tac[]
QED
