(* Native prefix for an internal-call head with a gas-free used default suffix. *)
Theory s1PrefixBoolChainSelectedIntCallHead
Ancestors
  s1PrefixIntCall s1PrefixDefs s1PrefixPreds
  bodyIntCallSource bodyFullPreds bodyFullShadowBodyInv bodySim
  constSubst gasShadow[qualified] vyperAST vyperContext vyperInterpreter vyperState
  supportedExprTraverse supportedProgram finite_map list

Theorem bool_chain_selected_intcall_head_prefix:
  h = Call ann (IntCall (src,name)) es dr /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_body_pre cenv cx env h ee /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) h ee (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) /\
  (~MEM (src,name) cx.stk ==> body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es) /\
  (!mut nr args dflts ret ss.
     get_module_code cx src = SOME tops /\
     lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) ==>
     ~supported_exprs_exists expr_msg_gas_root
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
     (!s1 vs t1.
        ~MEM (src,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
        body_exprs_full_ok (cx with stk updated_by CONS (src,name))
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
            (subst_consts_exprs (module_consts_env tops []) dflts)) /\
        body_exprs_prefix_ok (cx with stk updated_by CONS (src,name))
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
            (subst_consts_exprs (module_consts_env tops []) dflts))) /\
     (!s1 vs t1 sd dvs td penv rtv.
        ~MEM (src,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) /\
        eval_exprs (cx with stk updated_by CONS (src,name))
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
          (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
        bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
        evaluate_type (get_tenv cx) ret = SOME rtv /\
        (nr ==> IS_SOME cx.nonreentrant_slot) /\
        (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
        body_stmts_full_ok (cx with stk updated_by CONS (src,name))
          (subst_consts_stmts (module_consts_env tops []) ss) /\
        body_stmts_prefix_ok (cx with stk updated_by CONS (src,name))
          (subst_consts_stmts (module_consts_env tops []) ss))) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx h) (read_result cx)) (ee,s,G,tn)
Proof
  strip_tac >> qpat_x_assum `h = _` SUBST_ALL_TAC >>
  drule_all body_intcall_source_selection >> strip_tac >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  qpat_x_assum `!mut nr args dflts ret ss. _ ==> _` drule_all >> strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT BoolT) (Call ann (IntCall (NONE,name)) es dr) ee` by
    (irule intcall_sim_prefix >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (strip_tac >> first_x_assum drule >> simp[])
     >- (strip_tac >> first_x_assum drule >> simp[]) >>
     qexistsl_tac [`args`,`dflts`,`mut`,`nr`,`ret`,`rr`,`ss`,`env`,`tops`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     first_assum (fn th => drule_all_then strip_assume_tac th >> first_assum ACCEPT_TAC)) >>
  qhdtm_assum `expr_sim_prefix` (drule_then irule o REWRITE_RULE[expr_sim_prefix_def])
QED
