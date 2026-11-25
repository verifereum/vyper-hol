(* Apply the list induction hypothesis before any BoolChain operand is peeled. *)
Theory s1PrefixBoolChainOriginalSingleton
Ancestors
  s1PrefixBoolChainNativeStages s1PrefixPreds s1PrefixDefs exprSimSource
  vyperInterpreter vyperAST list

Theorem bool_chain_original_singleton_prefix:
  (!s'' x t.
     type_check (builtin_args_length_ok (BoolChain p n) (LENGTH [e]))
       "Builtin args" s'' = (INL x,t) /\
     BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
     code_slice_source (BoolChain p n) [e] = NONE ==>
     body_exprs_full_ok cx [e]) /\
  (!s'' x t.
     type_check (builtin_args_length_ok (BoolChain p n) (LENGTH [e]))
       "Builtin args" s'' = (INL x,t) /\
     BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
     code_slice_source (BoolChain p n) [e] = NONE ==>
     body_exprs_prefix_ok cx [e]) /\
  type_check (builtin_args_length_ok (BoolChain p n) (LENGTH [e]))
    "Builtin args" check_s = (INL checked,check_t) /\
  expr_type e = BaseT BoolT /\ expr_body_pre cenv cx env e es0 /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es0 /\
  compile_bool_chain_ops compile_expr cenv p rv xl [e] sa = ((),sb) /\
  compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
    [gas_shadow_expr e] shadow_sa = ((),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  (!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
  (!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at sa v) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es0.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es0 s /\ storage_well_formed_on cx es0 (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es0 G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (es0,s,G,tn)
Proof
  strip_tac >>
  `body_exprs_full_ok cx [e] /\ body_exprs_prefix_ok cx [e]` by
    (conj_tac
     >- (qpat_assum `!a b c. _ ==> body_exprs_full_ok _ _`
           (qspecl_then [`check_s`,`checked`,`check_t`] mp_tac) >> simp[]) >>
     qpat_assum `!a b c. _ ==> body_exprs_prefix_ok _ _`
       (qspecl_then [`check_s`,`checked`,`check_t`] mp_tac) >> simp[]) >>
  `body_expr_prefix_ok cx e` by fs[body_exprs_prefix_ok_def] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e es0` by
    (qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE[body_expr_prefix_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  irule bool_chain_singleton_prefix >>
  qpat_assum `compile_bool_chain_ops _ cenv _ _ _ [_] sa = _` (irule_at Any) >>
  qpat_assum `compile_bool_chain_ops _ _ _ _ _ [gas_shadow_expr e] shadow_sa = ((),shadow_sb)`
    (irule_at Any) >>
  qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func` (irule_at Any) >>
  simp[] >> qx_genl_tac [`op`,`sc`,`shadow_sc`] >> strip_tac >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) e es0 (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn)` by
    (drule_then assume_tac expr_body_pre_gas_admissible >>
     pure_rewrite_tac[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_assum `expr_sim_prefix` (drule_then irule o REWRITE_RULE[expr_sim_prefix_def])
QED
