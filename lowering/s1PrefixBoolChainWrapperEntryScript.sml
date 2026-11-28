(* Apply the traversal certificate at the paired entry of a singleton wrapper. *)
Theory s1PrefixBoolChainWrapperEntry
Ancestors
  s1PrefixBoolChainNativeStages s1PrefixDefs
  boolChainWrapperRead boolChainSource boolChainCodeLayout
  gasShadowBoolChainOperands gasShadowState gasShadow[qualified]
  bodyFullShared[qualified] bodyMemoryDefs exprLoweringProps freshWrites
  compileEnv vyperAST vyperInterpreter vyperValueOperation venomState

Theorem bool_chain_wrapper_prefix_at_entry_from_reached:
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
       ?reached.
         reached (bool_chain_operands p (n - 1) e) sg shadow_sg es s0 G0 tn0 /\
         (!a rest sa sc shadow_sa shadow_sc ee s G tn op.
            reached (a::rest) sa shadow_sa ee s G tn /\
            body_expr_full_ok cx a /\ expr_type a = BaseT BoolT /\
            body_const_cells_agree [(NONE,tops)] cx env ee /\ expr_body_pre cenv cx env a ee /\
            expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
              cenv cx (BaseT BoolT) a ee (st0,sa,sc,shadow_sa,shadow_sc,op,s,G,tn) ==>
            gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              cx st0 (bind (eval_expr cx a) (read_result cx)) (ee,s,G,tn)) /\
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
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx (Builtin (BaseT BoolT) (BoolChain p n) [e]))
                   (read_result cx)) (es,s0,G0,tn0)
Proof
  rpt gen_tac >> strip_tac >> pop_assum (mk_asm "certificate") >>
  drule_then assume_tac bool_chain_wrapper_read_action >>
  drule_then strip_assume_tac bool_chain_wrapper_action >>
  qpat_x_assum `!gs. eval_expr cx (Builtin _ _ _) _ = _` kall_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)` suffices_by
    simp[gas_prefix_full_def] >>
  qhdtm_assum `expr_vv_sim_full_pre`
    (strip_assume_tac o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  qpat_assum `compile_expr cenv ty (Builtin _ _ _) sa = _`
    (mp_then Any strip_assume_tac bool_chain_root_layout) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_sa = _`
    (strip_assume_tac o MATCH_MP bool_chain_root_layout o
     SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def,
                          gasShadowTheory.gas_shadow_builtin_def]) >>
  gvs[gas_shadow_bool_chain_operands] >>
  rename1 `fresh_var sa = (rv,sr)` >>
  rename1 `fresh_var shadow_sa = (rv,shadow_sr)` >>
  rename1 `fresh_label "bool_exit" sr = (xl,sg)` >>
  rename1 `fresh_label "bool_exit" shadow_sr = (shadow_xl,shadow_sg)` >>
  `gas_shadow_state sr shadow_sr` by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step
       gas_shadow_compiles_fresh_var >> simp[]) >>
  `shadow_xl = xl /\ gas_shadow_state sg shadow_sg` by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step
       gas_shadow_compiles_fresh_label >> simp[]) >>
  qpat_x_assum `shadow_xl = xl` SUBST_ALL_TAC >>
  qpat_assum `!fn. fn_has_code sa sb fn ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!fn. fn_has_code shadow_sa shadow_sb fn ==> _` (drule_then strip_assume_tac) >>
  asm_x "certificate" (drule_all_then strip_assume_tac) >>
  `sa.cs_next_var <= sg.cs_next_var` by simp[] >>
  `local_ptrs_reserved cenv sg` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv sg s0` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  `!v n. cenv.ce_return_buf = SOME (PtrVar (Var v) n) ==> not_fresh_at sg v` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!v n. cenv.ce_return_pc = SOME (PtrVar (Var v) n) ==> not_fresh_at sg v` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  irule bool_chain_ops_prefix_from_reached >>
  qpat_assum `reached (bool_chain_operands _ _ _) sg shadow_sg es s0 G0 tn0`
    (irule_at Any) >>
  qpat_assum `compile_bool_chain_ops _ cenv _ _ _ _ sg = _` (irule_at Any) >>
  qpat_assum `compile_bool_chain_ops _ _ _ _ _ _ shadow_sg = _` (irule_at Any) >>
  qpat_assum `fn_has_code shadow_sg _ shadow_func` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ cx env es` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sg s0` (irule_at Any) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED
