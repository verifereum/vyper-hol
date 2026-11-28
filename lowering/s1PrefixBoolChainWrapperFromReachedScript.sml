(* Apply the native traversal at the paired caller entry, without assuming
   a prefix theorem for an operand at any other entry. *)
Theory s1PrefixBoolChainWrapperFromReached
Ancestors
  s1PrefixBoolChainWrapperEntry s1PrefixBoolChainUseSite
  s1PrefixBuiltinLeaves s1PrefixOfVV s1PrefixPreds s1PrefixDefs
  boolChainSource boolChainCodeLayout vyperTypeCallGraph
  gasShadowState compileEnv vyperAST vyperInterpreter vyperValueOperation venomState

Theorem bool_chain_wrapper_prefix_from_reached:
  (!cx p n e DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es
      st0 sa sb shadow_sa shadow_sb rv s0 G0 tn0 sr shadow_sr xl sg shadow_sg
      sf shadow_sf.
     builtin_args_length_ok (BoolChain p n) (LENGTH [e]) /\
     body_expr_prefix_ok cx e /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (vyperTypeCallGraph$int_calls_expr e) /\
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
     ?reached.
       reached (bool_chain_operands p (n - 1) e) sg shadow_sg es s0 G0 tn0 /\
       (!e rest sa sc shadow_sa shadow_sc es s G tn op.
          reached (e::rest) sa shadow_sa es s G tn /\
          body_expr_full_ok cx e /\ expr_type e = BaseT BoolT /\
          body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre cenv cx env e es /\
          expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
            cenv cx (BaseT BoolT) e es (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn) ==>
          gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)) /\
       (!c rest sa sc shadow_sa shadow_sc es s G tn op sj sn lt lf
           st shadow_st marks mid G1 tn1 u.
          reached (c::rest) sa shadow_sa es s G tn /\
          lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sc) /\
          lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
            (gas_shadow_expr c) shadow_sa = (op,shadow_sc) /\
          sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
          emit_inst JNZ [op; Label lt; Label lf] [] sj = ((),sn) /\
          fn_has_code sj sn func /\ st.cs_current_bb = (if p then lt else lf) /\
          st.cs_current_insts = [] /\ gas_shadow_state st shadow_st /\
          compile_bool_chain_ops compile_expr cenv p rv xl rest st = ((),sf) /\
          compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
             (MAP gas_shadow_expr rest) shadow_st = ((),shadow_sf) /\
          bind (eval_expr cx c) (read_result cx)
            (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL (BoolV p),mid) /\
          storage_trace_domain cx st0 mid.storage_trace /\
          (!H. valid_horizon cx st0 H mid.storage_trace ==>
            gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              (s,G,tn) marks (OK u,G1,tn1)) ==>
          reached rest st shadow_st mid (jump_to st.cs_current_bb u) G1 tn1)) ==>
  !cx ann p n args.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Builtin ann (BoolChain p n) args))) /\
    (!s'' x t.
       type_check (builtin_args_length_ok (BoolChain p n) (LENGTH args))
         "Builtin args" s'' = (INL x,t) /\
       BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
       code_slice_source (BoolChain p n) args = NONE ==>
       body_exprs_full_ok cx args) /\
    (!s'' x t.
       type_check (builtin_args_length_ok (BoolChain p n) (LENGTH args))
         "Builtin args" s'' = (INL x,t) /\
       BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
       code_slice_source (BoolChain p n) args = NONE ==>
       body_exprs_prefix_ok cx args) ==>
    body_expr_prefix_ok cx (Builtin ann (BoolChain p n) args)
Proof
  disch_then (mk_asm "certificate") >> rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok (BoolChain p n) (LENGTH args)`
  >- (drule_all bool_chain_dispatch_observation >>
      disch_then (qx_choose_then `e` strip_assume_tac) >> gvs[] >>
      ONCE_REWRITE_TAC [body_expr_prefix_ok_def] >> simp[] >>
      rpt gen_tac >> strip_tac >> conj_asm2_tac
      >- (irule expr_sim_prefix_of_vv >> first_assum ACCEPT_TAC) >>
      simp[expr_vv_sim_prefix_def] >> rpt gen_tac >> strip_tac >>
      drule_then strip_assume_tac bool_chain_wrapper_action >>
      qpat_x_assum `!gs. eval_expr cx (Builtin _ _ _) _ = _` kall_tac >>
      gvs[] >>
      qhdtm_assum `expr_vv_sim_full_pre`
        (assume_tac o CONJUNCT1 o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
      `?rv. vv = StackValue (BaseT BoolT) (Var rv)` by
        (drule_then strip_assume_tac bool_chain_root_layout >>
         qpat_assum `vv = StackValue _ (Var rv)` (irule_at Any)) >>
      qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
      once_rewrite_tac[GSYM gas_prefix_full_bind_read_result] >>
      irule bool_chain_wrapper_prefix_at_entry_from_reached >>
      qhdtm_assum `expr_vv_sim_full_pre` (irule_at Any) >>
      qhdtm_assum `body_const_cells_agree` (irule_at Any) >>
      `builtin_args_length_ok (BoolChain p n) (LENGTH [e])` by simp[] >>
      `EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
          (int_calls_expr e)` by
        (fs[bodyFullPredsTheory.body_const_cells_agree_def] >>
         res_tac >> fs[int_calls_expr_def]) >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
        (rpt gen_tac >> strip_tac >>
         asm "certificate" (drule_all_then ACCEPT_TAC)))) >>
  ONCE_REWRITE_TAC [body_expr_prefix_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >> irule builtin_bad_arity_sim_prefix >> simp[]
QED
