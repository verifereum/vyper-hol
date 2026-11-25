(* Identity-continuation interface to the request-prefix argument stage. *)
Theory s1PrefixIntCallArgsVV
Ancestors
  s1PrefixIntCallArgs bodyFullIntCall s1PrefixDefs exprSimAccounts
  vyperStorageTrace fragExec compileEnv exprSimDefs

Theorem intcall_args_vv_prefix:
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
  ~supported_exprs_exists supportedProgram$expr_msg_gas_root
    (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_prefix_ok cx es) /\
  (!s1 vs t1.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) ==>
     body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))) /\
  (!s1 vs t1.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) ==>
     body_exprs_prefix_ok (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))) ==>
  (!st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0 prev penv rtv es1 t G tn.
     expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
       cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
       (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) /\
     (!H. valid_horizon cx st0 H es1.storage_trace ==>
        intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
          es sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
          es1 t G tn) /\
     body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
     (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
     (?H. valid_horizon cx st0 H es1.storage_trace) /\
     gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es1 ==>
     gas_outcome_full
       (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
       (cx_tops cx) cx st0
       (intcall_rest cx name mut nr ss prev rtv) (es1, t, G, tn)
       (\H res ee G' tn' z. T) (\H res ee gt r. T)) /\
  (!st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0 prev penv rtv es1 t G tn.
     expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
       cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
       (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) /\
     (!H. valid_horizon cx st0 H es1.storage_trace ==>
        intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
          es sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
          es1 t G tn) /\
     body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
     (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
     (?H. valid_horizon cx st0 H es1.storage_trace) /\
     gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es1 ==>
     gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
       cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1, t, G, tn)) ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
Proof
  rpt gen_tac >>
  disch_then (fn static =>
    let
      val args_vv = MATCH_MP intcall_args_prefix static |> SPEC_ALL
        |> Q.GENL [`kc`, `out`, `f`, `P`, `Q`, `R`]
        |> Q.ISPEC `comp_return : vyper_value -> compile_state -> vyper_value # compile_state`
        |> Q.SPEC `out`
        |> Q.ISPEC `return : eval_result -> evaluation_state -> (eval_result + exception) # evaluation_state`
        |> Q.SPECL [`expr_vv_res_ok`, `\H res ee G' tn' z. T`, `\H res ee gt r. T`]
        |> SIMP_RULE bool_ss [comp_bind_comp_return, bind_return_right,
                            comp_return_def, pairTheory.PAIR_EQ,
                            cs_appends_return, storage_trace_frame_return]
    in
      strip_tac >> rewrite_tac[expr_vv_sim_prefix_def] >>
      rpt gen_tac >> strip_tac >> irule args_vv
    end) >>
  qhdtm_assum `expr_vv_sim_full_pre`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`d`, `vv`, `sa`, `sb`, `shadow_func`, `shadow_sa`,
                `shadow_sb`, `ty`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  first_x_assum irule >>
  qhdtm_assum `expr_vv_sim_full_pre` (irule_at Any) >>
  qpat_x_assum `?H. valid_horizon cx st0 H es1.storage_trace`
    (qx_choose_then `H0` assume_tac) >>
  qexistsl_tac [`penv`, `H0`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
