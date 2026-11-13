(* MethodId child composition, conditional on the joint suffix boundary. *)
Theory bodyFullBuiltinEnvMethodIdRuntime
Ancestors
  bodyFullPreds bodySimFull bodyFullExprGeneric exprSimHash exprSimSource
  exprSimHypsDefs gasOutcomeFullCompose gasExemptCert gasShadowCompileStmtHelpers
  gasShadowState gasShadow exprLowering exprLoweringProps exprSimWordArgs
  exprSimMemoryStack vyperTyping vyperTypeSystem builtinHashing
  vyperContext builtinSimple bodyFullGhostFrame vyperStorageTrace vyperStorageFootprint compileEnv
  loweringPosts bodyPtrDefs venomState fragGasSeqPtr vyperAST list
Libs
  pairLib

Theorem method_id_runtime_sim_full_from_suffix:
  (!DF lo d explicit ctx func PG tops cenv cx env ann e es sa sm sb s0 st0 mid v x s G0 tn0 G tn fixed op.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    return_buf_frame d cenv sa s0 /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (?xs. !tail.
      bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
        (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
      expr_store_bound cx (expr_type e) v x s /\
      alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    ==>
    let b = Builtin ann MethodId [e] in
    let vv = if fixed then StackValue ann op
             else LocatedValue ann (mk_ptr op LocMemory) in
    ?r z G' tn'.
      builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
      ~z.vs_halted /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
      local_ptrs_reserved cenv sb /\ return_buf_frame d cenv sb z /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK z,G',tn') /\
        expr_post H ctx func cenv cx b es sa sb s0 mid r op z /\
        expr_store_bound cx (expr_type b) r op z /\
        vv_post H ctx func cenv cx b es sa sb s0 mid (Value r) vv z /\
        vv_store_bound cx (expr_type b) (lowered_value_type cenv b)
          mid (Value r) vv z /\
        s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx mid G' tn' z /\
        ptr_val_ok cx (post_value_type cenv b) r op G' tn' z /\
        ptr_vv_ok cx (post_value_type cenv b) (Value r) vv mid G' tn' z /\
        (~fixed ==> ptr_buf_ok cenv b op G' z) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'))
  ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann e es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
    body_expr_full_ok cx e /\ method_id_literal e = NONE ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann MethodId [e]) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann MethodId [e]) es
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `is_bytes_or_string_type (expr_type e) /\
   (ann = BaseT (BytesT (Fixed 4)) \/ ann = BaseT (BytesT (Dynamic 4)))` by
    (mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `ann`,
      `ts` |-> `[expr_type e]`] hash_builtin_types) >>
     gvs[expr_body_pre_def, well_typed_expr_def] >> metis_tac[]) >>
  qabbrev_tac `fixed = (ann = BaseT (BytesT (Fixed 4)))` >>
  `ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))` by
    (gvs[Abbr `fixed`] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  conj_tac
  >- (rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
      `?x sm op'. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
        compile_method_id_runtime (expr_type e) x fixed sm = (op',sb) /\ op = op'` by
        (qpat_x_assum `lower_value _ _ _ (Builtin _ MethodId _) _ = _` mp_tac >>
         simp[Once lower_value_def, comp_bind_def, compile_method_id_singleton_runtime] >>
         Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
         rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
         Cases_on `compile_method_id_runtime (expr_type e) x fixed sm` >>
         Cases_on `fixed` >>
         gvs[as_stack_val_def, as_ptr_val_def, comp_bind_def,
             unwrap_value_def, comp_return_def, expr_type_def, is_word_type_def]) >>
      qpat_x_assum `op = op'` SUBST_ALL_TAC >>
      `cs_appends (compile_method_id_runtime (expr_type e) x fixed)` by
        simp[cj 5 hash_suffix_appends] >>
      drule_all hash_unary_suffix_cut >> strip_tac >>
      `?sx ss. lower_value compile_expr cenv (expr_type e)
         (gas_shadow_expr e) shadow_sa = (sx,ss)` by metis_tac[pairTheory.PAIR] >>
      `sx = x /\ gas_shadow_state sm ss` by
        (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
          gas_shadow_stmt_lower_value) >> rewrite_tac[gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
      qpat_x_assum `sx = x` SUBST_ALL_TAC >>
      `?sop ssb. compile_method_id_runtime (expr_type e) x fixed ss = (sop,ssb)` by
        metis_tac[pairTheory.PAIR] >>
      `ssb = shadow_sb` by
        (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ MethodId _)) _ = _`
           mp_tac >>
         simp[gas_shadow_expr_def, gas_shadow_builtin_def,
              Once lower_value_def, comp_bind_def, compile_method_id_singleton_runtime] >>
         Cases_on `fixed` >>
         gvs[as_stack_val_def, as_ptr_val_def, comp_bind_def,
             unwrap_value_def, comp_return_def, expr_type_def, is_word_type_def]) >>
      `fn_has_code shadow_sa ss shadow_func` by
        (irule (cj 3 hash_unary_suffix_cut) >>
         goal_assum (drule_at Any) >>
         qexistsl_tac [`compile_method_id_runtime (expr_type e) x fixed`, `sop`, `shadow_sb`] >>
         simp[] >> cheat) >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
        metis_tac[expr_body_pre_gas_admissible] >>
      qpat_x_assum `expr_sim_full _ _ _ _ e es`
        (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
      disch_then (drule_all_then assume_tac) >>
      `eval_expr cx (Builtin ann MethodId [e]) =
         bind (bind (eval_expr cx e) (read_result cx))
          (\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
                      INL r => INL (Value r) | INR ex => INR ex),mid))` by
        (irule eval_expr_unary_builtin_action >> simp[builtin_args_length_ok_def]) >>
      cheat) >>
  cheat
QED
