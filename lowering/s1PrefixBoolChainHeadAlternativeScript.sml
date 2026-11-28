(* The remaining operands are either the original singleton or strict children. *)
Theory s1PrefixBoolChainHeadAlternative
Ancestors
  s1PrefixBoolChainActualHistory s1PrefixPreds s1PrefixDefs
  bodyFullBoolChain bodyFullPreds bodyFullShadowBodyInv bodySim
  exprSimHypsDefs vyperTyping ctorCallFreeBoolChain
  exprLowering vyperAST list arithmetic

Theorem bool_chain_root_list_alternative[local]:
  bool_chain_operands p k e = [e] \/
  EVERY (\a. expr_size a < expr_size e) (bool_chain_operands p k e)
Proof
  Cases_on `k` >- simp[bool_chain_operands_def] >>
  Cases_on `e` >> simp[bool_chain_operands_def] >>
  Cases_on `p` >> simp[] >> IF_CASES_TAC >> simp[] >>
  disj2_tac >> simp[EVERY_MEM,expr_size_def] >>
  rpt strip_tac >> drule bool_chain_operand_size >> simp[expr_size_def] >>
  decide_tac
QED

Theorem bool_chain_reached_list_alternative:
  !xs sa shadow_sa es s G tn.
    bool_chain_actual_reached cx cenv p rv xl sf shadow_sf DF lo ctx shadow_ctx
      func PG st0 n e sg shadow_sg es0 s0 G0 tn0 xs sa shadow_sa es s G tn ==>
    xs = [e] \/ EVERY (\a. expr_size a < expr_size e) xs
Proof
  match_mp_tac
    (BETA_RULE (Q.INST [`P` |->
      `\xs sa shadow_sa es s G tn.
        xs = [e] \/ EVERY (\a. expr_size a < expr_size e) xs`]
      bool_chain_actual_reached_induction)) >>
  conj_tac >- simp[bool_chain_root_list_alternative] >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem bool_chain_actual_head_alternative:
  !cx p n e DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es
     st0 sa sb shadow_sa shadow_sb rv s0 G0 tn0 sr shadow_sr xl sg shadow_sg
     sf shadow_sf.
    builtin_args_length_ok (BoolChain p n) (LENGTH [e]) /\
    body_expr_prefix_ok cx e /\
    bool_chain_full_ok [(NONE,cx_tops cx)] [] cx (bool_chain_operands p (n - 1) e) /\
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
      body_expr_full_ok cx a /\ expr_type a = BaseT BoolT /\
      body_const_cells_agree [(NONE,tops)] cx env ee /\ expr_body_pre cenv cx env a ee /\
      expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (BaseT BoolT) a ee (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn) ==>
      expr_size a < expr_size e \/
      (a = e /\ rest = [] /\
       gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         cx st0 (bind (eval_expr cx a) (read_result cx)) (ee,s,G,tn))
Proof
  rpt strip_tac >>
  drule bool_chain_reached_list_alternative >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_assum `body_expr_prefix_ok _ _`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  disch_then drule_all >> simp[expr_sim_prefix_def] >> metis_tac[]
QED
