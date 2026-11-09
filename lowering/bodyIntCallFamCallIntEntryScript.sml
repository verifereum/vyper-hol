(* Nested internal call, argument side: from the call's producer premises
   to the INVOKE.  As seam 1 (intcall_args_frame_setup), the continuation
   gets intcall_entry; it also gets the caller's resource invariant at the
   INVOKE, at the caller's scopes and the call's start compile state, and
   the frontier's monotonicity. *)
Theory bodyIntCallFamCallIntEntry
Ancestors
  bodyIntCallJointContract bodyIntCallSeamDefs
Libs
  monadsyntax

Theorem intcall_nested_entry:
  !fp ce env ann name es dflt ty sa sb vv s0 es0 mut args ret ss rr Q R.
    (!e'. expr_size e' < expr_size (Call ann (IntCall (NONE,name)) es dflt) ==>
          intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
          intcall_map_producer fp e') /\
    intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    cenv_module_pins fp.jc_tops ce /\
    expr_body_pre ce fp.jc_cx env (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    supportedExprs$supported_expr fp.jc_tops (Call ann (IntCall (NONE,name)) es dflt) /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner
      (int_calls_expr (Call ann (IntCall (NONE,name)) es dflt)) /\
    lookup_callable_function fp.jc_cx.in_deploy name fp.jc_tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) fp.jc_tops /\
    compile_expr ce ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    gas_admissible (eval_expr fp.jc_cx (Call ann (IntCall (NONE,name)) es dflt))
      expr_vv_res_ok es0 /\
    intcall_expr_res fp ce env es0 sa s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!res ee r. expr_exit res r ==> R res ee r) /\
    (!prev penv rtv es1 t.
       intcall_entry fp.jc_tops fp.jc_ctx fp.jc_func ce fp.jc_cx env name es
         sa sb vv s0 es0 (mut,args,ret,ss,rr) prev penv rtv es1 t /\
       intcall_expr_res fp ce env (es1 with scopes := prev) sa t /\
       s0.vs_alloca_next <= t.vs_alloca_next ==>
       gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
         (intcall_rest fp.jc_cx name mut ss prev rtv) (es1,t) Q R) ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_expr fp.jc_cx (Call ann (IntCall (NONE,name)) es dflt)) (es0,s0) Q R
Proof
  cheat
QED
