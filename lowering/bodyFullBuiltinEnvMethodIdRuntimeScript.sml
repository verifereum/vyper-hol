(* MethodId child composition, conditional on the joint suffix boundary. *)
Theory bodyFullBuiltinEnvMethodIdRuntime
Ancestors exprSimDefs[qualified,ignore_grammar]
  bodyFullPreds bodySimFull bodyFullExprGeneric exprSimHash exprSimSource
  exprSimHypsDefs gasOutcomeFull gasOutcomeFullCompose gasExemptCert gasShadowCompileStmtHelpers
  gasShadowState gasShadow exprLowering exprLoweringProps exprSimWordArgs
  exprSimMemoryStack vyperTyping vyperTypeSystem builtinHashing
  vyperContext builtinSimple bodyFullGhostFrame vyperStorageTrace vyperStorageFootprint compileEnv
  loweringPosts bodyPtrDefs venomState fragGasSeqPtr vyperAST list
Libs
  pairLib

Theorem method_id_runtime_joint_outcome_from_suffix:
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
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ann e es
    st0 sa sm sb shadow_sa ss shadow_sb x op fixed s0 G0 tn0.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
    method_id_literal e = NONE /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa = (x,ss) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    compile_method_id_runtime (expr_type e) x fixed ss = (op,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    let b = Builtin ann MethodId [e] in
    let vv = if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory) in
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx b) (read_result cx)) (es,s0,G0,tn0)
      (\H res ee G tn t. ?v. res = INL v /\
        expr_post H ctx func cenv cx b es sa sb s0 ee v op t /\
        expr_store_bound cx (expr_type b) v op t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv b) v op G tn t /\
        (~is_word_type (post_value_type cenv b) ==> ptr_buf_ok cenv b op G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
        vv_post H ctx func cenv cx b es sa sb s0 ee (Value v) vv t /\
        vv_store_bound cx (expr_type b) (lowered_value_type cenv b) ee (Value v) vv t /\
        ptr_vv_ok cx (post_value_type cenv b) (Value v) vv ee G tn t /\
        (~fixed ==> ptr_buf_ok cenv b op G t))
      (\H res ee gt r. expr_exit res r)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  `cs_appends (compile_method_id_runtime (expr_type e) x fixed)` by
    simp[cj 5 hash_suffix_appends] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_shadow_state sm ss` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
      gas_shadow_stmt_lower_value) >> rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `fn_has_code shadow_sa ss shadow_func` by
    (`cs_extends shadow_sa ss` by metis_tac[cj 2 compile_expr_grows] >>
     `cs_extends ss shadow_sb` by metis_tac[fragExecTheory.cs_appends_def] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e es`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (drule_all_then assume_tac) >>
      `eval_expr cx (Builtin ann MethodId [e]) =
         bind (bind (eval_expr cx e) (read_result cx))
          (\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
                      INL r => INL (Value r) | INR ex => INR ex),mid))` by
        (irule eval_expr_unary_builtin_action >> simp[builtin_args_length_ok_def]) >>
      `bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx) =
        bind (bind (eval_expr cx e) (read_result cx))
          (\v mid. (builtin_result cx mid.accounts ann MethodId [expr_type e] [v],mid))` by
        (mp_tac (Q.INST [`bi` |-> `MethodId`, `ann` |-> `ann`, `e` |-> `e`, `cx` |-> `cx`]
           exprSimUnopComposePropsTheory.eval_expr_unop_action_general) >>
         simp[builtin_args_length_ok_def, builtin_result_def, exprSimUnopPropsTheory.unop_result_def,
              vyperInterpreterTheory.precompile_builtin_def]) >>
      pop_assum SUBST1_TAC >>
      qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
      irule gas_outcome_full_bind_all >> rpt conj_tac
      >- simp[storage_trace_frame_def]
      >~ [`storage_trace_frame (bind _ _)`]
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
      >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
          qexistsl_tac [`mid`, `t`, `v`] >> gvs[])
      >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
      qexists_tac `\H res ee G' tn' t. childQ H res ee G' tn' t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
      reverse conj_tac
      >- (irule gas_outcome_full_post_source >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
          conj_tac >- simp[] >>
          simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res` >>
          gvs[exprSimDefsTheory.expr_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
      qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
      BETA_TAC >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by gvs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t /\ _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      simp_tac (srw_ss()) [Abbr `childQ`] >> strip_tac >>
      disj1_tac >> goal_assum (drule_at Any) >> simp[] >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
        expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
        expr_store_bound cx (expr_type e) v x t /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
        ptr_val_ok cx (post_value_type cenv e) v x G1 tn1 t /\
        (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G1 t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
        (rpt strip_tac >>
         qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t /\ _`
           (qspec_then `H` mp_tac) >> simp[]) >>
      Q.SUBGOAL_THEN `?xs. !tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)` assume_tac
      >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
      qpat_x_assum `!DF lo d explicit ctx func PG tops cenv cx env ann e es sa sm sb s0 st0 mid v x s G0 tn0 G tn fixed op. _`
        (drule_all_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`]
          (strip_assume_tac o SIMP_RULE std_ss [LET_THM]))) >>
      irule gas_outcome_full_pure >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`G'`, `mid`, `INL r`, `z`, `tn'`] >>
      `mid with gas_obs := [] = mid` by (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
      gvs[] >> qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `fixed` >> gvs[expr_type_def, is_word_type_def]
QED

Theorem method_id_runtime_sim_full_from_suffix:
  (!DF lo d explicit ctx func PG tops cenv cx env ann e es sa sm sb s0 st0 mid v x s G0 tn0 G tn fixed op.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    return_buf_frame d cenv sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
    (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
      expr_store_bound cx (expr_type e) v x s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    let b = Builtin ann MethodId [e] in
    let vv = if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory) in
    ?r z G' tn'.
      builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
      s.vs_alloca_next <= z.vs_alloca_next /\ local_ptrs_reserved cenv sb /\
      return_buf_frame d cenv sb z /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
        expr_post H ctx func cenv cx b es sa sb s0 mid r op z /\
        expr_store_bound cx (expr_type b) r op z /\
        vv_post H ctx func cenv cx b es sa sb s0 mid (Value r) vv z /\
        vv_store_bound cx (expr_type b) (lowered_value_type cenv b) mid (Value r) vv z /\
        s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G' tn' z /\
        ptr_val_ok cx (post_value_type cenv b) r op G' tn' z /\
        ptr_vv_ok cx (post_value_type cenv b) (Value r) vv mid G' tn' z /\
        (~fixed ==> ptr_buf_ok cenv b op G' z) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')) ==>
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
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  Q.SUBGOAL_THEN `is_bytes_or_string_type (expr_type e) /\
    (ann = BaseT (BytesT (Fixed 4)) \/ ann = BaseT (BytesT (Dynamic 4)))` assume_tac
  >- (mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `ann`, `ts` |-> `[expr_type e]`]
      hash_builtin_types) >>
     gvs[expr_body_pre_def, well_typed_expr_def] >> metis_tac[]) >>
  qabbrev_tac `fixed = (ann = BaseT (BytesT (Fixed 4)))` >>
  `ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))` by
    (gvs[Abbr `fixed`] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
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
             unwrap_value_def, comp_return_def, expr_type_def, is_word_type_def, contextTheory.mk_ptr_def]) >>
      qpat_x_assum `op = op'` SUBST_ALL_TAC >>
      `?sx ss. lower_value compile_expr cenv (expr_type e)
         (gas_shadow_expr e) shadow_sa = (sx,ss)` by metis_tac[pairTheory.PAIR] >>
      `sx = x /\ gas_shadow_state sm ss` by
        (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
          gas_shadow_stmt_lower_value) >> rewrite_tac[gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
      qpat_x_assum `sx = x` SUBST_ALL_TAC >>
      `?sop ssb. compile_method_id_runtime (expr_type e) x fixed ss = (sop,ssb)` by
        metis_tac[pairTheory.PAIR] >>
      `sop = op' /\ ssb = shadow_sb` by
        (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ MethodId _)) _ = _`
           mp_tac >>
         simp[gas_shadow_expr_def, gas_shadow_builtin_def,
              Once lower_value_def, comp_bind_def, compile_method_id_singleton_runtime] >>
         Cases_on `fixed` >>
         gvs[as_stack_val_def, as_ptr_val_def, comp_bind_def,
             unwrap_value_def, comp_return_def, expr_type_def, is_word_type_def, contextTheory.mk_ptr_def]) >>
      qpat_x_assum `sop = op'` SUBST_ALL_TAC >>
      qpat_x_assum `ssb = shadow_sb` SUBST_ALL_TAC >>
      drule_all method_id_runtime_joint_outcome_from_suffix >>
      disch_then (assume_tac o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
      irule gas_outcome_full_post_mono >>
      qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> metis_tac[]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  `?x sm op. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    vv = if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)` by
    (qpat_x_assum `compile_expr _ _ (Builtin _ MethodId _) _ = _` mp_tac >>
     simp[compile_method_id_singleton_runtime] >>
     Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
     rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
     Cases_on `compile_method_id_runtime (expr_type e) x fixed sm` >>
     Cases_on `fixed` >>
     gvs[as_stack_val_def, as_ptr_val_def, comp_bind_def, comp_return_def]) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `?sx ss. lower_value compile_expr cenv (expr_type e)
     (gas_shadow_expr e) shadow_sa = (sx,ss)` by metis_tac[pairTheory.PAIR] >>
  `sx = x /\ gas_shadow_state sm ss` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
      gas_shadow_stmt_lower_value) >> rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  `?sop ssb. compile_method_id_runtime (expr_type e) x fixed ss = (sop,ssb)` by
    metis_tac[pairTheory.PAIR] >>
  `sop = op /\ ssb = shadow_sb` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Builtin _ MethodId _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_method_id_singleton_runtime] >>
     Cases_on `fixed` >>
     gvs[as_stack_val_def, as_ptr_val_def, comp_bind_def, comp_return_def,
         contextTheory.mk_ptr_def]) >>
  qpat_x_assum `sop = op` SUBST_ALL_TAC >>
  qpat_x_assum `ssb = shadow_sb` SUBST_ALL_TAC >>
  drule_all method_id_runtime_joint_outcome_from_suffix >>
  disch_then (assume_tac o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
  `eval_expr cx (Builtin ann MethodId [e]) =
     bind (bind (eval_expr cx e) (read_result cx))
      (\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
                  INL r => INL (Value r) | INR ex => INR ex),mid))` by
    (irule eval_expr_unary_builtin_action >> simp[builtin_args_length_ok_def]) >>
  `bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v mid. (builtin_result cx mid.accounts ann MethodId [expr_type e] [v],mid))` by
    (mp_tac (Q.INST [`bi` |-> `MethodId`, `ann` |-> `ann`, `e` |-> `e`, `cx` |-> `cx`]
       exprSimUnopComposePropsTheory.eval_expr_unop_action_general) >>
     simp[builtin_args_length_ok_def, builtin_result_def, exprSimUnopPropsTheory.unop_result_def,
          vyperInterpreterTheory.precompile_builtin_def]) >>
  dxrule_at Any (Q.INST
    [`f` |-> `\res. case res of INL (v:value) => INL (Value v) | INR ex => INR ex`]
    (INST_TYPE [beta |-> ``:value``, alpha |-> ``:eval_result``] gas_outcome_full_source_map)) >>
  disch_then (qspec_then `eval_expr cx (Builtin ann MethodId [e])` mp_tac) >>
  impl_tac
  >- (simp[] >> qx_gen_tac `ee` >>
      qpat_assum `eval_expr cx (Builtin _ MethodId _) = _` SUBST1_TAC >>
      qpat_assum `bind (eval_expr cx (Builtin _ MethodId _)) _ = _` SUBST1_TAC >>
      simp[Once vyperStateTheory.bind_def] >>
      Cases_on `bind (eval_expr cx e) (read_result cx) ee` >>
      rename1 `bind (eval_expr cx e) (read_result cx) ee = (res,mid)` >>
      Cases_on `res` >> simp[vyperStateTheory.bind_def]) >>
  strip_tac >>
  drule gas_outcome_full_post_mono >> disch_then irule >>
  BETA_TAC >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      Cases_on `fixed` >>
      gvs[expr_type_def, is_word_type_def, contextTheory.vv_location_def, contextTheory.mk_ptr_def]) >>
  rpt gen_tac >> disch_then (qx_choose_then `raw_exit` strip_assume_tac) >>
  Cases_on `raw_exit` >>
  gvs[oneline exprSimDefsTheory.expr_exit_def, AllCaseEqs()]
QED

