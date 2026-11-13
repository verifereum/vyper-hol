(*
 * The internal call full case's argument stage over the finite-horizon
 * joint judgment.
 *
 * TOP-LEVEL:
 *   intcall_args_full
 *)
Theory bodyFullIntCallArgs
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams bodyFullPreds bodySimFull
  gasOutcomeFull bodyPtrDefs gasShadow gasContext exprSimHypsDefs
  exprLowering vyperInterpreter vyperState vyperAST list

val _ = Parse.hide "body";

(* (a) Arguments and frame setup, at (DF H, lo).  The caller's code up to
   the INVOKE, then any code continuation kc, runs against the source up
   to push_function, then any source continuation f, on one witness: the
   arguments' judgments run their staging, and whatever runs the rest of
   the call and f from an intcall_entry_full state (source, memory and
   pointer facts at t) runs the whole call and f.  A supported callee has
   no defaults (body_intcall_source_selection). *)
Theorem intcall_args_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) ==>
    !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 kc out f P Q R.
      comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt))
        kc sa = (out, sb) /\
      comp_bind
        (compile_expr cenv ty
           (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)))
        kc shadow_sa = (out, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
        ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!H res ee gt r. expr_exit res r ==> R H res ee gt r) /\
      (!vv sm prev penv rtv es1 t G tn.
         compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
           (vv, sm) /\
         kc vv sm = (out, sb) /\
         (!H. valid_horizon cx st0 H es1.storage_trace ==>
            intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
              es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
              es1 t G tn) /\
         (?H. valid_horizon cx st0 H es1.storage_trace) /\
         gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
           P es1 ==>
         gas_outcome_full
           (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
           (cx_tops cx) cx st0
           (bind (intcall_rest cx name mut nr ss prev rtv) f) (es1, t, G, tn)
           Q R) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0
        (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
        (es0, s0, G0, tn0) Q R
Proof
  cheat
QED
