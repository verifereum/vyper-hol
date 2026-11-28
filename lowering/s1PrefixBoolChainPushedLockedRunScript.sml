(* Prefix execution for the selected locked callee body. *)
Theory s1PrefixBoolChainPushedLockedRun
Ancestors
  s1PrefixBoolChainSelectedLockedLift s1PrefixBoolChainCallRankBase
  s1PrefixBoolChainCalleeRounds s1PrefixPreds bodyLoopCalls
  bodyFullIntCallCallee bodyFullPreds bodyInvCodeProps bodySimFullMain
  typedCopyProducer constSubst vyperTypeContract s1PrefixDefs list

Theorem bool_chain_pushed_locked_run_compiled:
  LENGTH (remcode pushed) < rank /\
  (!c ys. LENGTH (remcode c) < rank /\
     (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
        EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
          (vyperTypeCallGraph$int_calls_stmts ys) /\
        stmts_loop_calls_ok [(NONE,ts)] ys) ==>
      body_stmts_prefix_ok c ys) /\
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
    (vyperTypeCallGraph$int_calls_stmts compiled) /\
  MEM (FunctionDecl Internal mut nr raw name args ds ret ss) tops /\
  compiled = subst_consts_stmts (module_consts_env tops []) ss /\
  body_inv tops ctx ce pushed /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmts tops bindings compiled /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) compiled ==>
            occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] pushed env locked /\
  expr_sim_inv ce pushed env locked /\
  ce_locals_declared ce env /\
  locals_alloc_ok ce env /\
  type_stmts env ret compiled = SOME env_after /\
  stmts_exprs_ok ce compiled /\
  call_evaluation_safe pushed (int_calls_stmts compiled) /\
  frame_ret_ok_full (DF,lo,dret,ctx,shadow_ctx,MAP (op_prov G) arg_ops,callee,sf)
    pushed RetQ ce ret /\
  stmt_frag_full_pre (DF,lo,dret,ctx,shadow_ctx,MAP (op_prov G) arg_ops,callee,sf)
    pushed NoLoop RetQ ce (stmts_env ce NoLoop ret compiled)
    (stmts_env (gas_shadow_env T ce) NoLoop ret (MAP gas_shadow_stmt compiled))
    (eval_stmts pushed compiled) locked
    (st0,sa,sb,sha,shb,at_body,Gbody,tnbody,env_end) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
    pushed st0 (eval_stmts pushed compiled) (locked,at_body,Gbody,tnbody)
Proof
  strip_tac >>
  `body_stmts_prefix_ok pushed compiled` by
    (first_x_assum irule >> simp[] >>
     drule selected_port_checker_guards >> strip_tac >>
     fs[body_const_cells_agree_def] >> metis_tac[]) >>
  qpat_x_assum `compiled = _` SUBST_ALL_TAC >>
  qpat_x_assum `body_stmts_prefix_ok _ _`
    (mp_tac o REWRITE_RULE [body_stmts_prefix_ok_def]) >>
  disch_then drule_all >> simp[stmt_frag_prefix_def] >>
  disch_then drule >> simp[NoAsms]
QED

Theorem bool_chain_pushed_locked_run:
  LENGTH (remcode pushed) < rank /\
  (!c ys. LENGTH (remcode c) < rank /\
     (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
        EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
          (vyperTypeCallGraph$int_calls_stmts ys) /\
        stmts_loop_calls_ok [(NONE,ts)] ys) ==>
      body_stmts_prefix_ok c ys) /\
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
    (vyperTypeCallGraph$int_calls_stmts compiled) /\
  MEM (FunctionDecl Internal mut nr raw name args ds ret ss) tops /\
  compiled = subst_consts_stmts (module_consts_env tops []) ss /\
  body_inv tops ctx ce pushed /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmts tops bindings compiled /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) compiled ==>
            occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] pushed env locked /\
  expr_sim_inv ce pushed env locked /\
  ce_locals_declared ce env /\
  locals_alloc_ok ce env /\
  type_stmts env ret compiled = SOME env_after /\
  stmts_exprs_ok ce compiled /\
  call_evaluation_safe pushed (int_calls_stmts compiled) /\
  frame_ret_ok_full (DF,lo,dret,ctx,shadow_ctx,MAP (op_prov G) arg_ops,callee,sf)
    pushed RetQ ce ret /\
  (!gs. eval_stmts pushed ss (locked with gas_obs := gs) =
        eval_stmts pushed compiled (locked with gas_obs := gs)) /\
  stmt_frag_full_pre (DF,lo,dret,ctx,shadow_ctx,MAP (op_prov G) arg_ops,callee,sf)
    pushed NoLoop RetQ ce (stmts_env ce NoLoop ret compiled)
    (stmts_env (gas_shadow_env T ce) NoLoop ret (MAP gas_shadow_stmt compiled))
    (eval_stmts pushed compiled) locked
    (st0,sa,sb,sha,shb,at_body,Gbody,tnbody,env_end) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
    pushed st0 (eval_stmts pushed ss) (locked,at_body,Gbody,tnbody)
Proof
  strip_tac >>
  drule_all bool_chain_pushed_locked_run_compiled >>
  pure_rewrite_tac[gas_prefix_full_def] >>
  qpat_assum `!gs. eval_stmts _ ss _ = _` (pure_rewrite_tac o single) >>
  simp[NoAsms]
QED
