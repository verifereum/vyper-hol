(* The strict BoolChain head rule at the actual paired entry. *)
Theory s1PrefixBoolChainProperHead
Ancestors
  s1PrefixBoolChainProperHeadProjection s1PrefixBoolChainSameContextHead
  s1PrefixBoolChainStrictCalleeHead

Theorem bool_chain_proper_head_prefix:
  !cx p n e DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es
     st0 sa sb shadow_sa shadow_sb rv s0 G0 tn0 sr shadow_sr xl sg shadow_sg
     sf shadow_sf.
    builtin_args_length_ok (BoolChain p n) (LENGTH [e]) /\
    body_expr_prefix_ok cx e /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (vyperTypeCallGraph$int_calls_expr e) /\
    bool_chain_full_ok cx (bool_chain_operands p (n - 1) e) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin (BaseT BoolT) (BoolChain p n) [e]) es /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin (BaseT BoolT) (BoolChain p n) [e]) es
      (st0,sa,sb,shadow_sa,shadow_sb,StackValue (BaseT BoolT) (Var rv),s0,G0,tn0) /\
    fresh_var sa = (rv,sr) /\ fresh_var shadow_sa = (rv,shadow_sr) /\
    fresh_label "bool_exit" sr = (xl,sg) /\
    fresh_label "bool_exit" shadow_sr = (xl,shadow_sg) /\
    compile_bool_chain_ops compile_expr cenv p rv xl
      (bool_chain_operands p (n - 1) e) sg = ((),sf) /\
    compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
      (MAP gas_shadow_expr (bool_chain_operands p (n - 1) e)) shadow_sg = ((),shadow_sf) /\
    gas_shadow_state sg shadow_sg /\
    fn_has_code sg sf func /\ fn_has_code shadow_sg shadow_sf shadow_func /\
    sg.cs_current_bb = sa.cs_current_bb /\ sg.cs_current_insts = sa.cs_current_insts /\
    sg.cs_next_var = sa.cs_next_var + 1 ==>
    !a rest sa sc shadow_sa shadow_sc ee s G tn op.
      bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
        func PG st0 n e sg shadow_sg es s0 G0 tn0 (a::rest) sa shadow_sa ee s G tn /\
      (a <> e \/ rest <> []) /\
      body_expr_full_ok cx a /\ expr_type a = BaseT BoolT /\
      body_const_cells_agree [(NONE,tops)] cx env ee /\ expr_body_pre cenv cx env a ee /\
      expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (BaseT BoolT) a ee (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_expr cx a) (read_result cx)) (ee,s,G,tn)
Proof
  ACCEPT_TAC (MP (MP bool_chain_proper_head_from_steps
    bool_chain_same_context_head_prefix_ok) bool_chain_strict_callee_head_prefix)
QED
