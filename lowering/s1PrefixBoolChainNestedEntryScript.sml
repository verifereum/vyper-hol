(* Execute a nested wrapper using prefixes of the heads reached in its entry. *)
Theory s1PrefixBoolChainNestedEntry
Ancestors
  s1PrefixBoolChainWrapperEntry s1PrefixBoolChainHeadAlternative
  s1PrefixBoolChainActualReach s1PrefixDefs vyperAST

Theorem bool_chain_nested_prefix_at_entry:
  !cx p n e DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es
     st0 sa sb shadow_sa shadow_sb rv s0 G0 tn0.
    builtin_args_length_ok (BoolChain p n) (LENGTH [e]) /\
    bool_chain_full_ok [(NONE,cx_tops cx)] [] cx (bool_chain_operands p (n - 1) e) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin (BaseT BoolT) (BoolChain p n) [e]) es /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin (BaseT BoolT) (BoolChain p n) [e]) es
      (st0,sa,sb,shadow_sa,shadow_sb,StackValue (BaseT BoolT) (Var rv),s0,G0,tn0) /\
    (!sr shadow_sr xl sg shadow_sg sf shadow_sf.
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
         body_expr_full_ok cx a /\ expr_type a = BaseT BoolT /\
         body_const_cells_agree [(NONE,tops)] cx env ee /\ expr_body_pre cenv cx env a ee /\
         expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
           cenv cx (BaseT BoolT) a ee (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn) /\
         expr_size a < expr_size (Builtin (BaseT BoolT) (BoolChain p n) [e]) ==>
         gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           cx st0 (bind (eval_expr cx a) (read_result cx)) (ee,s,G,tn)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx (Builtin (BaseT BoolT) (BoolChain p n) [e]))
                   (read_result cx)) (es,s0,G0,tn0)
Proof
  rpt gen_tac >> strip_tac >> pop_assum (mk_asm "operand") >>
  irule bool_chain_wrapper_prefix_at_entry_from_reached >>
  qhdtm_assum `expr_vv_sim_full_pre` (irule_at Any) >>
  qhdtm_assum `body_const_cells_agree` (irule_at Any) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (rpt gen_tac >> strip_tac)) >>
  qexists_tac `bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo
    ctx shadow_ctx func PG st0 n e sg shadow_sg es s0 G0 tn0` >>
  conj_tac >- MATCH_ACCEPT_TAC bool_chain_actual_reached_root >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `expr_size a < expr_size (Builtin (BaseT BoolT) (BoolChain p n) [e])` by
        (drule bool_chain_reached_list_alternative >> simp[] >>
         strip_tac >> gvs[expr_size_def] >> decide_tac) >>
      asm "operand" irule >>
      qhdtm_assum `bool_chain_actual_reached` (irule_at Any) >>
      qpat_assum `fresh_var sa = _` (irule_at Any) >>
      qpat_assum `fresh_var shadow_sa = _` (irule_at Any) >>
      qhdtm_assum `expr_sim_full_pre` (irule_at Any) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  drule_all bool_chain_actual_reached_advance >> simp[]
QED
