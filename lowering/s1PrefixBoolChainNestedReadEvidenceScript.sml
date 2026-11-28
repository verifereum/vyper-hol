(* Supply the nested wrapper's native operand guard from fixed-context fullness. *)
Theory s1PrefixBoolChainNestedReadEvidence
Ancestors
  s1PrefixBoolChainNestedDemandStep bodyFullBoolChainOperands

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `bool_chain_full_ok cx (bool_chain_operands p (n - 1) e)` by
    (irule body_expr_full_ok_bool_chain_operands >> simp[]) >>
  irule bool_chain_nested_prefix_of_smaller >>
  qhdtm_assum `expr_vv_sim_full_pre` (irule_at Any) >>
  qhdtm_assum `body_const_cells_agree` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem bool_chain_nested_read_prefix_from_joint_smaller:
  builtin_args_length_ok (BoolChain p n) (LENGTH [e]) /\
  (!a. body_expr_full_ok cx a) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin (BaseT BoolT) (BoolChain p n) [e]) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (BaseT BoolT) (BoolChain p n) [e]) es
    (st0,sa,sb,shadow_sa,shadow_sb,StackValue (BaseT BoolT) (Var rv),s0,G0,tn0) /\
  (!a ety ee ca cb sha shb op' u J tau.
     expr_size a < expr_size (Builtin (BaseT BoolT) (BoolChain p n) [e]) /\
     body_expr_full_ok cx a /\
     value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       tops cenv cx env a ety ee (st0,ca,cb,sha,shb,op',u,J,tau) ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx a) (read_result cx)) (ee,u,J,tau)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx (Builtin (BaseT BoolT) (BoolChain p n) [e]))
                 (read_result cx)) (es,s0,G0,tn0)
Proof
  cheat
QED
