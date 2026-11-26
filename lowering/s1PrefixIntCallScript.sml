(* Request-prefix companion to bodyFullIntCall. *)
Theory s1PrefixIntCall
Ancestors
  s1PrefixPreds bodyFullIntCall s1PrefixDefs s1PrefixOfVV
  s1PrefixIntCallArgsVV s1PrefixIntCallRestOutcome s1PrefixIntCallRestPrefix

Theorem intcall_vv_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx tenv es0 /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\
  LENGTH es <= LENGTH args /\
  ~supportedExprTraverse$supported_exprs_exists supportedProgram$expr_msg_gas_root
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_prefix_ok cx es) /\
  (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env tops []) dflts))) /\
  (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_prefix_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env tops []) dflts))) /\
  (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
         (subst_consts_stmts (module_consts_env tops []) ss)) /\
  (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_prefix_ok (cx with stk updated_by CONS (NONE,name))
         (subst_consts_stmts (module_consts_env tops []) ss)) ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule intcall_args_vv_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`args`, `dflts`, `mut`, `nr`, `ret`, `rr`, `ss`, `tenv`, `tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qhdtm_x_assum `expr_vv_sim_full_pre`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
      irule intcall_entry_rest_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`G0`, `args`, `cenv`, `d`, `dflts`, `es`, `es0`, `penv`,
                    `ret`, `rr`, `s0`, `sa`, `sb`, `tenv`, `tn0`, `tops`, `vv`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule intcall_entry_rest_outcome >>
  qhdtm_assum `expr_vv_sim_full_pre` (irule_at Any) >>
  qpat_assum `lookup_callable_function _ _ _ = SOME _` (irule_at Any) >>
  qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qexistsl_tac [`tenv`, `rr`, `penv`, `H0`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx tenv es0 /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\
  LENGTH es <= LENGTH args /\
  ~supportedExprTraverse$supported_exprs_exists supportedProgram$expr_msg_gas_root
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_prefix_ok cx es) /\
  (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env tops []) dflts))) /\
  (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_prefix_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env tops []) dflts))) /\
  (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name))
         (subst_consts_stmts (module_consts_env tops []) ss)) /\
  (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_prefix_ok (cx with stk updated_by CONS (NONE,name))
         (subst_consts_stmts (module_consts_env tops []) ss)) ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
Proof
  rpt gen_tac >> disch_tac >>
  irule expr_sim_prefix_of_vv >>
  pop_assum (MATCH_ACCEPT_TAC o MATCH_MP intcall_vv_prefix)
QED
