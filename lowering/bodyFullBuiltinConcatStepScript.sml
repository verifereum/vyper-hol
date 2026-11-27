(* Shared operand and copy transitions of the Concat loop. *)
Theory bodyFullBuiltinConcatStep
Ancestors bodyFullBuiltinConcatReady bodyFullBuiltinConcatHead
  exprSimFullBundleProps bodyFullPreds bodyFullExprsListFacts bodyFullSimProjection bodySimFull
  bodyFullIfExpReach[qualified,ignore_grammar]
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  exprSimConcatArgs exprSimConcatSource gasShadowCompileStmtHelpers
  gasShadowState gasShadowUnit gasExplicitSites exprLoweringProps
  loweringStateRelDefs loweringPosts compileEnv stateRelProj
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  venomState words list finite_map pred_set
  exprSimHypsDefs[qualified]

Theorem concat_loop_head_entry:
  !mods.
  concat_loop_ready (e::args) P k DF lo d ctx shadow_ctx PG
    tops func shadow_func cenv cx env st0 es sa sb shadow_sa shadow_sb
    s0 G0 tn0 dv ov ow binst B bsz oinst ==>
  expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  ?op sc shadow_sc.
    expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es (st0,sa,sc,shadow_sa,shadow_sc,op,s0,G0,tn0)
Proof
  pure_rewrite_tac [concat_loop_ready_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e es` by
    (qpat_assum `!x st. MEM x (e::args) /\ _ ==> _`
       (qspecl_then [`e`,`es`] mp_tac) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (`body_expr_full_ok cx e` by
        (qpat_assum `body_exprs_full_ok cx (e::args)`
           (ACCEPT_TAC o cj 1 o ONCE_REWRITE_RULE [body_exprs_full_ok_cons])) >>
      irule (cj 1 body_expr_full_ok_simulations) >> asm_rewrite_tac[] >>
      qexistsl_tac [`env`,`tops`] >> simp[]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ _ sa = (op,sc)` >>
  `ci_mono sa sc` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[ci_mono_def]) >>
  `ci_mono sc sb` by
    (irule (SRULE [LET_THM] concat_cons_mono) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`args`,`dv`,`ov`] >> gvs[]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
      (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_lower_value_env >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (shadow_op,shadow_sc)` >>
  `shadow_op = op /\ gas_shadow_state sc shadow_sc` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_op = op` SUBST_ALL_TAC >>
  `ci_mono shadow_sa shadow_sc` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[ci_mono_def]) >>
  `is_bytestring_type (expr_type e) \/ ?m. expr_type e = BaseT (BytesT (Fixed m))` by
    fs[listTheory.EVERY_DEF] >>
  `ci_mono shadow_sc shadow_sb` by
    (qspecl_then [`gas_shadow_env T cenv`,`gas_shadow_expr e`,`MAP gas_shadow_expr args`,
       `dv`,`ov`,`shadow_sa`,`shadow_sb`,`op`,`shadow_sc`] mp_tac concat_cons_mono >>
     (impl_tac >-
       (RULE_ASSUM_TAC (SIMP_RULE bool_ss [LET_THM,listTheory.MAP,
          listTheory.MAP_MAP_o,combinTheory.o_DEF,gasShadowTheory.gas_shadow_expr_type]) >>
        simp_tac bool_ss [LET_THM,listTheory.MAP,listTheory.MAP_MAP_o,
          combinTheory.o_DEF,gasShadowTheory.gas_shadow_expr_type] >>
        rpt conj_tac >> fs[gasShadowTheory.gas_shadow_expr_type])) >> simp[]) >>
  `fn_has_code sa sc func /\ fn_has_code shadow_sa shadow_sc shadow_func` by
    (conj_tac
     >- (qspecl_then [`sa`,`sa`,`sc`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_mid >>
         (impl_tac >- fs[ci_mono_def,cs_extends_refl]) >> disch_then ACCEPT_TAC) >>
     qspecl_then [`shadow_sa`,`shadow_sa`,`shadow_sc`,`shadow_sb`,`shadow_func`]
       mp_tac fragExecTheory.fn_has_code_mid >>
     (impl_tac >- fs[ci_mono_def,cs_extends_refl]) >> disch_then ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule exprSimSourceTheory.expr_body_pre_gas_admissible >> simp[]) >>
  qexistsl [`op`,`sc`,`shadow_sc`] >>
  pure_rewrite_tac [expr_sim_full_hypotheses_def,expr_sim_full_code_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem concat_loop_copy_entry:
  !mods.
  concat_loop_ready (e::args) P k DF lo d ctx shadow_ctx PG
    tops func shadow_func cenv cx env st0 es sa sb shadow_sa shadow_sb
    s0 G0 tn0 dv ov ow binst B bsz oinst /\
  expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sc,shadow_sa,shadow_sc,op,s0,G0,tn0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sc,s0,op,G0,tn0)
      H (INL v) ee G1 tn1 t /\
    (?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK t,G1,tn1)) /\
    ~t.vs_halted /\ ee.gas_obs = []) ==>
  ?s2 shadow_s2 u G2 tn2.
    concat_loop_ready args (P+concat_payload_capacity (expr_type e))
      (k+LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []))
      DF lo d ctx shadow_ctx PG tops func shadow_func cenv cx env st0 ee s2 sb
      shadow_s2 shadow_sb u G2 tn2 dv ov ow binst B bsz oinst /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK u,G2,tn2)) /\
    ~u.vs_halted /\ ee.gas_obs = [] /\
    (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
    ci_mono sa sc /\ ci_mono sc s2 /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    (!name lb lsz. local_region cenv ee.scopes u name lb lsz <=>
      local_region cenv es.scopes s0 name lb lsz) /\
    mem_bytes_at (B+32) (k+LENGTH (case v of BytesV bs => bs
                 | StringV str => MAP (n2w o ORD) str | _ => [])) u.vs_memory =
      mem_bytes_at (B+32) k s0.vs_memory ++
        (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z u = SOME w) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a) /\
    (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
       (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
       (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
                       p+n <= lb \/ lb+lsz <= p) ==>
       mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    locals_kept cenv es ee s0 u /\
    (~expr_has_effect e ==>
      (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
         mem_bytes_at lb lsz u.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
      (!p n. (p+n <= B \/ B+bsz <= p) /\
         (p+n <= w2n ow \/ w2n ow+64 <= p) /\
         (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
            sa.cs_next_id <= inst.inst_id /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
            regions_disjoint p n b sz) ==>
         mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `concat_loop_ready`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [concat_loop_ready_def]) >>
  qhdtm_assum `expr_sim_full_hypotheses`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE
       [expr_sim_full_hypotheses_def,expr_sim_full_code_def]) >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o SIMP_RULE bool_ss
      [expr_sim_full_post_def,expr_sim_full_endpoint_def,sumTheory.INL_11,UNWIND_THM1]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (`well_typed_expr env e` by
       qpat_assum `expr_body_pre _ cx env e _`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     `body_const_cells_agree [(NONE,tops)] cx env (ee with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) _ _ = (_, ee with gas_obs := [])`
       (irule_at Any) >> simp[]) >>
  drule_all concat_head_typed >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` >>
  `post_value_type cenv e = expr_type e` by
    (Cases_on `is_bytestring_type (expr_type e)`
     >- (irule loweringPostsTheory.post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
     `?m. expr_type e = BaseT (BytesT (Fixed m))` by fs[listTheory.EVERY_DEF] >>
     rename1 `expr_type e = BaseT (BytesT (Fixed m))` >>
     `m <= 32` by
       (qpat_assum `evaluate_type _ (expr_type e) = SOME tv` mp_tac >>
        qpat_assum `expr_type e = BaseT (BytesT (Fixed m))` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        gvs[vyperValueTheory.evaluate_type_def,AllCaseEqs()]) >>
     irule loweringPostsTheory.post_value_type_word >>
     fs[compileEnvTheory.is_word_type_def]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `?obs. ee.storage_trace = es.storage_trace ++ obs` by
    (drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `storage_trace_domain cx st0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_prefix] >>
  `body_exprs_full_ok cx args` by
    (qpat_assum `body_exprs_full_ok cx (e::args)`
       (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons]) >>
     qpat_assum `eval_expr cx e _ = (INL _,_)` mp_tac >>
     qpat_assum `read_result cx _ _ = (INL _,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> metis_tac[]) >>
  suspend "arm"
QED

Resume concat_loop_copy_entry[arm]:
  `expr_store_bound cx (expr_type e) v op t` by
    (qpat_assum `post_value_type cenv e = expr_type e` (fn th =>
       qpat_assum `expr_store_bound cx (post_value_type cenv e) v op t`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  mp_tac (Q.INST [`s` |-> `s0`,`G` |-> `G0`,`tn` |-> `tn0`]
    (SPEC_ALL concat_head_arm_full)) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[LET_THM] >>
     BETA_TAC >> asm_rewrite_tac[] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
       (qspec_then `H` mp_tac) >> simp[])) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv _ ctx _ cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi (CONJ inv member))))) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,G1,tn1)`
       (fn path => qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
          qpat_assum `!fn inst z. frag_reachable ctx func _ fn inst z ==> _`
            (fn safe => ACCEPT_TAC (MATCH_MP
               bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
               (LIST_CONJ [path,no_phi,safe])))))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK u,G2,tn2)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
         gas_origin_ptr_path _ _ [] _ /\ _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
         gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2)`
       (drule_then assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2)`
       (fn path => qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
          qpat_assum `!fn inst z. frag_reachable ctx func t fn inst z ==> _`
            (fn safe => ACCEPT_TAC (MATCH_MP
               bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
               (LIST_CONJ [path,no_phi,safe])))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2) /\ _`
       (fn th => qpat_assum `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
         (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
          CONJUNCT1 o CONJUNCT2 o MATCH_MP th))) >>
  suspend "ready"
QED

Resume concat_loop_copy_entry[ready]:
  qpat_assum `EVERY _ (e::args)`
    (map_every assume_tac o CONJUNCTS o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 es.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[storage_trace_domain_def] >>
     metis_tac[cj 1 stmt_state_rel_local_ptrs_alloca]) >>
  `!name lb lsz. local_region cenv ee.scopes u name lb lsz <=>
      local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (irule exprSimPropsTheory.local_region_frame >>
         (conj_tac >- (qexists `func` >> first_assum ACCEPT_TAC)) >>
         qexistsl [`sa`,`ee.scopes`,`u`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl [`s0`,`sa`,`es.scopes`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`s2`,`shadow_s2`,`u`,`G2`,`tn2`] >>
  conj_tac
  >- (pure_rewrite_tac [concat_loop_ready_def] >>
      rpt conj_tac >> asm_simp_tac arith_ss [LET_THM] >>
      rpt strip_tac >> asm_rewrite_tac[]
      >~ [`dalloca_fmp_headroom inst z`]
      >- (qpat_assum `!fn inst z. frag_reachable ctx func u fn inst z ==> _` irule >>
          goal_assum (drule_at Any))
      >~ [`expr_body_pre cenv cx env x st`]
      >- (qpat_assum `!x st. MEM x (e::args) /\ _ ==> _`
            (qspecl_then [`x`,`st`] mp_tac) >> simp[])
      >~ [`not_fresh_at s2 z`, `cenv.ce_return_buf = SOME (PtrVar (Var z) sz)`]
      >- (qpat_assum `!z sz. cenv.ce_return_buf = _ ==> not_fresh_at s2 z`
            (qspecl_then [`z`,`sz`] mp_tac) >> simp[])
      >~ [`not_fresh_at s2 z`, `cenv.ce_return_pc = SOME (PtrVar (Var z) sz)`]
      >- (qpat_assum `!z sz. cenv.ce_return_pc = _ ==> not_fresh_at s2 z`
            (qspecl_then [`z`,`sz`] mp_tac) >> simp[])
      >~ [`B+bsz <= lb \/ lb+lsz <= B`]
      >- (qpat_assum `!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==> _`
            (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[])
      >~ [`w2n ow+64 <= lb \/ lb+lsz <= w2n ow`]
      >- (qpat_assum `!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==> _`
            (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists `tv` >> asm_rewrite_tac[]
QED

Finalise concat_loop_copy_entry
