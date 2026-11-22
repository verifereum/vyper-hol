(* Request-prefix companion to bodyFullIntCallArgs. *)
Theory s1PrefixIntCallArgs
Ancestors
  s1PrefixPreds bodyFullIntCallArgs s1PrefixDefs

Theorem intcall_args_prefix:
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
  !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 kc out f P Q R.
    (!v. storage_trace_frame (f v)) /\
    (!v. cs_appends (kc v)) /\
    comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt))
      kc sa = (out, sb) /\
    comp_bind
      (compile_expr (gas_shadow_env T cenv) ty
         (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)))
      kc shadow_sa = (out, shadow_sb) /\
    gas_shadow_state sa shadow_sa /\
    gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    gas_admissible
      (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
      P es0 /\
    (!e. P (INR e) ==> expr_vv_res_ok (INR e)) /\
    return_buf_frame d cenv sa s0 /\
    alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es0.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es0 s0 /\
      storage_well_formed_on cx es0 (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\
    ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!H res ee gt r.
       expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) /\
    (!vv sm prev penv rtv es1 t G tn.
       compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
         (vv, sm) /\
       kc vv sm = (out, sb) /\
       (!H. valid_horizon cx st0 H es1.storage_trace ==>
          intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
            es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
            es1 t G tn) /\
       body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
       (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
       (?H. valid_horizon cx st0 H es1.storage_trace) /\
       gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
         P es1 ==>
       gas_outcome_full
         (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         (cx_tops cx) cx st0
         (bind (intcall_rest cx name mut nr ss prev rtv) f) (es1, t, G, tn)
         Q R) /\
    (!vv sm prev penv rtv es1 t G tn.
       compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
         (vv, sm) /\
       kc vv sm = (out, sb) /\
       (!H. valid_horizon cx st0 H es1.storage_trace ==>
          intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
            es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
            es1 t G tn) /\
       body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
       (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
       (?H. valid_horizon cx st0 H es1.storage_trace) /\
       gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
         P es1 ==>
      gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
    cx st0 (bind (intcall_rest cx name mut nr ss prev rtv) f)
    (es1, t, G, tn)) ==>
  gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
    cx st0 (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
    (es0, s0, G0, tn0)
Proof
  cheat
QED
