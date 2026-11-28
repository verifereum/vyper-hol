(* Supply the nested wrapper's reached-head prefixes from smaller demands. *)
Theory s1PrefixBoolChainNestedDemandStep
Ancestors
  s1PrefixBoolChainNestedEntry s1PrefixBoolChainEqDemand s1PrefixDefs vyperAST

Theorem bool_chain_nested_prefix_of_smaller:
  builtin_args_length_ok (BoolChain p n) (LENGTH [e]) /\
  bool_chain_full_ok [(NONE,cx_tops cx)] [] cx (bool_chain_operands p (n - 1) e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin (BaseT BoolT) (BoolChain p n) [e]) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (BaseT BoolT) (BoolChain p n) [e]) es
    (st0,sa,sb,shadow_sa,shadow_sb,StackValue (BaseT BoolT) (Var rv),s0,G0,tn0) /\
  (!z ety ee ca cb sha shb op' u J tau.
     expr_size z < expr_size (Builtin (BaseT BoolT) (BoolChain p n) [e]) /\
     body_expr_full_ok cx z /\
     value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       tops cenv cx env z ety ee (st0,ca,cb,sha,shb,op',u,J,tau) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx z) (read_result cx)) (ee,u,J,tau)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx (Builtin (BaseT BoolT) (BoolChain p n) [e])) (read_result cx))
    (es,s0,G0,tn0)
Proof
  strip_tac >> pop_assum (mk_asm "smaller") >>
  irule bool_chain_nested_prefix_at_entry >>
  qhdtm_assum `expr_vv_sim_full_pre` (irule_at Any) >>
  qhdtm_assum `body_const_cells_agree` (irule_at Any) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE rpt strip_tac) >>
  asm "smaller" irule >>
  simp[value_read_demand_def] >>
  qhdtm_assum `expr_sim_full_pre` (irule_at Any) >> simp[]
QED
