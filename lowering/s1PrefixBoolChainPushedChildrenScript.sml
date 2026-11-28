(* Prefix observations for a selected pushed child. *)
Theory s1PrefixBoolChainPushedChildren
Ancestors
  bodyCallLiveness
  s1PrefixBoolChainCallRankBase
  s1PrefixBoolChainCalleeRounds s1PrefixIntCallStageSingleton
  s1PrefixPreds bodyLoopCalls typedCopyProducer bodyFullSimProjection
  bodyFullIntCallCallee bodyInvCodeProps bodySimFullMain constSubst
  vyperTypeContract bodyFullPreds s1PrefixDefs list

Theorem bool_chain_pushed_default_child:
  LENGTH (remcode pushed) < rank /\
  (!c a. LENGTH (remcode c) < rank /\
       (!ts. ALOOKUP c.sources c.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr a)) ==> body_expr_prefix_ok c a) /\
  body_inv tops ctx dc pushed /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] pushed (tenv with current_src := NONE) ee /\
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
    (vyperTypeCallGraph$int_calls_expr e) /\
  expr_body_pre dc pushed (tenv with current_src := NONE) e ee ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      dc pushed (expr_type e) e ee /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      dc pushed (expr_type e) e ee /\
  (expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      dc pushed (expr_type e) e ee (st0,si,sf,shi,shf,op,s,G,tn) ==>
   gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      pushed st0 (bind (eval_expr pushed e) (read_result pushed)) (ee,s,G,tn)) /\
  (expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      dc pushed (expr_type e) e ee (st0,si,ci,shi,shci,vv,s,G,tn) ==>
   gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      pushed st0 (eval_expr pushed e) (ee,s,G,tn))
Proof
  strip_tac >>
  `body_expr_full_ok pushed e` by
    (irule (cj 5 body_sim_full_mutual) >>
     drule_then strip_assume_tac selected_port_checker_guards >>
     drule_then assume_tac body_const_cells_agree_runtime_check >>
     gvs[] >> first_assum ACCEPT_TAC) >>
  `body_expr_prefix_ok pushed e` by
    (first_x_assum irule >> simp[] >> fs[body_const_cells_agree_def]) >>
  drule_all body_expr_full_ok_simulations >> strip_tac >> simp[] >>
  qpat_x_assum `body_expr_prefix_ok _ _`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  disch_then drule_all >> simp[expr_sim_prefix_def, expr_vv_sim_prefix_def] >>
  metis_tac[]
QED
