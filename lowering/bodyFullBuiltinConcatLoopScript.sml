(* Concat evaluates its operands on one joint execution. *)
Theory bodyFullBuiltinConcatLoop
Ancestors
  bodyFullBuiltinConcatHead bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFullGuarded gasExemptCert
  exprSimConcatArgs exprSimConcatSource exprSimWordArgs
  gasShadowCompile gasShadowCompileHelpers gasShadowState gasShadowUnit gasExplicitSites
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr
  exprLoweringProps loweringStateRelDefs loweringPosts compileEnv
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  venomState words list finite_map pred_set

Theorem concat_args_sim_full:
  !args P k DF lo d ctx shadow_ctx PG tops func shadow_func cenv cx env st0
   es sa sb shadow_sa shadow_sb s0 G0 tn0 dv ov ow binst B bsz oinst.
    compile_concat compile_expr cenv args (Var dv)
      (MAP (\e.
         if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                       | _ => (F,32:num)) args) (Var ov) sa = ((),sb) /\
    compile_concat compile_expr cenv (MAP gas_shadow_expr args) (Var dv)
      (MAP (\e.
         if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                       | _ => (F,32:num)) args) (Var ov) shadow_sa = ((),shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
    ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    EVERY (\e. is_bytestring_type (expr_type e) \/
                 ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
    expr_sim_inv cenv cx env es /\
    (!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
       expr_body_pre cenv cx env e st) /\
    body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var dv s0 = SOME (n2w (B+32)) /\ lookup_var ov s0 = SOME ow /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas binst.inst_id = SOME (B,bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B+bsz <= lb \/ lb+lsz <= B) /\
       (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
    (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
    B+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
    B+bsz <= s0.vs_alloca_next /\ w2n ow+64 <= s0.vs_alloca_next /\
    allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\ lo <= B /\ lo <= w2n ow /\
    ptr_covers G0 tn0 dv s0 (bsz-32) /\ ptr_covers G0 tn0 ov s0 32 /\
    (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn0.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn0.t_mem) /\
    mload (w2n ow) s0 = n2w k /\ k <= P /\
    32+P+SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
    32+concat_data_bound P (MAP expr_type args) <= bsz ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
      (\H res ee G tn t. ?vs. res = INL vs /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
         expr_sim_inv cenv cx env ee /\
         stmt_state_rel H ctx func cenv cx ee t /\
         storage_well_formed_on cx ee (FST H) /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
         allocas_from lo t /\ lo <= t.vs_alloca_next /\
         B+bsz <= t.vs_alloca_next /\ w2n ow+64 <= t.vs_alloca_next /\
         return_buf_frame d cenv sb t /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
         MAP FDOM es.scopes = MAP FDOM ee.scopes /\
         (!name lb lsz. local_region cenv ee.scopes t name lb lsz <=>
            local_region cenv es.scopes s0 name lb lsz) /\
         LIST_REL (\e v. ?tv.
           evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v)
           args vs /\
         lookup_var dv t = SOME (n2w (B+32)) /\ lookup_var ov t = SOME ow /\
         FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
         FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
         ptr_covers G tn dv t (bsz-32) /\ ptr_covers G tn ov t 32 /\
         (!i. B+32 <= i /\ i < B+32+k+
            LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs
              | StringV str => MAP (n2w o ORD) str | _ => []) vs)) ==>
            i NOTIN tn.t_mem) /\
         (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
         mem_bytes_at (B+32) (k+LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs
              | StringV str => MAP (n2w o ORD) str | _ => []) vs))) t.vs_memory =
           mem_bytes_at (B+32) k s0.vs_memory ++
             FLAT (MAP (\v. case v of BytesV bs => bs
              | StringV str => MAP (n2w o ORD) str | _ => []) vs) /\
         mload (w2n ow) t = n2w (k+LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs
              | StringV str => MAP (n2w o ORD) str | _ => []) vs))) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
            lookup_var z t = SOME w) /\
         (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
            FLOOKUP t.vs_allocas aid = SOME a) /\
         (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
            (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
            (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
               p+n <= lb \/ lb+lsz <= p) ==>
            mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
         locals_kept cenv es ee s0 t /\
         (~EXISTS expr_has_effect args ==>
           (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
              mem_bytes_at lb lsz t.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
           (!p n. (p+n <= B \/ B+bsz <= p) /\
              (p+n <= w2n ow \/ w2n ow+64 <= p) /\
              (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                 sa.cs_next_id <= inst.inst_id /\
                 FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
                 regions_disjoint p n b sz) ==>
              mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory)))
      (\H res ee gt r. expr_exit res r)
Proof
  Induct >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >- (gvs[exprLoweringTheory.compile_concat_def,comp_return_def] >>
      irule gas_outcome_full_pure >> simp[] >>
      qexistsl [`G0`,`es`,`INL []`,`s0`,`tn0`] >>
      simp[eval_exprs_nil] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
        (drule msg_gas_state_frame >>
         disch_then (qspecl_then [`s0.vs_gas_readings`,`s0.vs_inst_idx`,`[]`] mp_tac) >>
         simp[NoAsms]) >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
        (`(es with gas_obs := []).accounts = es.accounts /\
          (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
         metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
      `ghost_inv_at (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
        (qpat_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         pure_rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
         strip_tac >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      asm_simp_tac arith_ss [fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
        ghost_kept_at_refl]) >>
  rename1 `EVERY _ (e::args)` >>
  qpat_assum `EVERY _ (e::args)`
    (CONJUNCTS_THEN assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  `expr_body_pre cenv cx env e es` by
    (qpat_assum `!x st. MEM x (e::args) /\ _ ==> _`
       (qspecl_then [`e`,`es`] mp_tac) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_exprs_full_ok cx (e::args)`
       (mp_tac o REWRITE_RULE [body_exprs_full_ok_def]) >> strip_tac >>
     qpat_x_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then
       [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
        `cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ _ sa = (op,sc)` >>
  `ci_mono sa sc` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[ci_mono_def]) >>
  `ci_mono sc sb` by
    (qspecl_then [`cenv`,`e`,`args`,`dv`,`ov`,`sa`,`sb`,`op`,`sc`]
       mp_tac concat_cons_mono >>
     (impl_tac >- (pure_rewrite_tac[LET_THM] >> BETA_TAC >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
      (lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e))` by
    (mp_tac (Q.INST [`sh` |-> `T`,`ty` |-> `expr_type e`]
       (MATCH_MP gas_shadow_compiles_lower_value (cj 1 gas_shadow_compile_expr))) >> simp[]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (shadow_op,shadow_sc)` >>
  `shadow_op = op /\ gas_shadow_state sc shadow_sc` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_op = op` SUBST_ALL_TAC >>
  `ci_mono shadow_sa shadow_sc` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _`
       (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[ci_mono_def]) >>
  `ci_mono shadow_sc shadow_sb` by
    (qspecl_then [`cenv`,`gas_shadow_expr e`,`MAP gas_shadow_expr args`,
       `dv`,`ov`,`shadow_sa`,`shadow_sb`,`op`,`shadow_sc`] mp_tac concat_cons_mono >>
     (impl_tac >-
       (RULE_ASSUM_TAC (SIMP_RULE bool_ss [LET_THM,listTheory.MAP,
          listTheory.MAP_MAP_o,combinTheory.o_DEF,gasShadowTheory.gas_shadow_expr_type]) >>
        simp_tac bool_ss [LET_THM,listTheory.MAP,listTheory.MAP_MAP_o,
          combinTheory.o_DEF,gasShadowTheory.gas_shadow_expr_type] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `fn_has_code sa sc func /\ fn_has_code shadow_sa shadow_sc shadow_func` by
    (conj_tac
     >- (qspecl_then [`sa`,`sa`,`sc`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_mid >>
         (impl_tac >- fs[ci_mono_def,cs_extends_refl]) >> disch_then ACCEPT_TAC) >>
     qspecl_then [`shadow_sa`,`shadow_sa`,`shadow_sc`,`shadow_sb`,`shadow_func`]
       mp_tac fragExecTheory.fn_has_code_mid >>
     (impl_tac >- fs[ci_mono_def,cs_extends_refl]) >> disch_then ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (qpat_assum `expr_body_pre cenv cx env e es`
       (ACCEPT_TAC o MATCH_MP exprSimSourceTheory.expr_body_pre_gas_admissible)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\
      ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "continue" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >> simp[Abbr `childR`] >>
  rpt strip_tac >> Cases_on `res` >- fs[] >>
  rename1 `expr_exit (INR ex) r` >> simp[] >>
  qspecl_then [`\v:value. ([]:value list)`,`INR ex : value + exception`]
    (fn th => rewrite_tac[SIMP_RULE (srw_ss()) [] th])
    exprSimDefsTheory.expr_exit_success_map >> first_assum ACCEPT_TAC
QED

Resume concat_args_sim_full[continue]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11,UNWIND_THM1]) >>
  qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  drule_all concat_head_typed >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `?obs. ee.storage_trace = es.storage_trace ++ obs` by
    (drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `storage_trace_domain cx st0 es.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee.storage_trace` mp_tac >>
     qpat_assum `ee.storage_trace = es.storage_trace ++ obs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[vyperStorageFootprintTheory.storage_trace_domain_prefix]) >>
  `body_exprs_full_ok cx args` by
    (qpat_assum `body_exprs_full_ok cx (e::args)`
       (mp_tac o REWRITE_RULE [body_exprs_full_ok_def]) >>
     qpat_assum `eval_expr cx e _ = (INL _,_)` mp_tac >>
     qpat_assum `read_result cx _ _ = (INL _,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> metis_tac[]) >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
     `tops`,`cenv`,`cx`,`env`,`st0`,`e`,`args`,`es`,`ee`,`sa`,`sc`,`sb`,
     `shadow_sa`,`shadow_sc`,`shadow_sb`,`s0`,`t`,`G0`,`tn0`,`G1`,`tn1`,
     `B`,`bsz`,`ow`,`k`,`P`,`binst`,`oinst`,`dv`,`ov`,`v`,`op`,`tv`]
    mp_tac concat_head_arm_full >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[LET_THM] >>
     BETA_TAC >> asm_rewrite_tac[] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
       (qspec_then `H` mp_tac) >> simp[])) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 es.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[storage_trace_domain_def,exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def]) >>
  `!name lb lsz. local_region cenv ee.scopes u name lb lsz <=>
      local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (qspecl_then [`func`,`cenv`,`es.scopes`,`s0`,`sa`,`ee.scopes`,`u`,
            `name`,`lb`,`lsz`] mp_tac exprSimPropsTheory.local_region_frame >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then ACCEPT_TAC) >>
     qspecl_then [`cenv`,`es.scopes`,`sa`,`ee.scopes`,`s0`,`u`,`name`,`lb`,`lsz`]
       mp_tac exprSimPropsTheory.local_region_frame_fwd >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  qpat_assum `!P k DF lo d ctx shadow_ctx PG tops func shadow_func cenv cx env st0
      es sa sb shadow_sa shadow_sb s0 G0 tn0 dv ov ow binst B bsz oinst. _`
    (qspecl_then
      [`P+concat_payload_capacity (expr_type e)`,
       `k+LENGTH (case v of BytesV bs => bs
          | StringV str => MAP (n2w o ORD) str | _ => [])`,
       `DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`tops`,`func`,`shadow_func`,
       `cenv`,`cx`,`env`,`st0`,`ee`,`s2`,`sb`,`shadow_s2`,`shadow_sb`,
       `u`,`G2`,`tn2`,`dv`,`ov`,`ow`,`binst`,`B`,`bsz`,`oinst`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> asm_simp_tac arith_ss [LET_THM] >>
     rpt strip_tac >> asm_rewrite_tac[]
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
           (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]))) >> strip_tac >>
  qmatch_assum_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_exprs cx args) _ tailQ tailR` >>
  drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    (Q.ISPECL [`SUM_MAP (CONS (v:value)) (I:exception->exception)`,
       `bind (eval_exprs cx args) (\vs. return (v::vs))`]
       (Q.GENL [`f`,`source'`] gas_outcome_full_source_map)) >>
  disch_then (qspecl_then [`v`,`args`] mp_tac) >>
  (impl_tac >- (simp[vyperStateTheory.bind_def,vyperStateTheory.return_def] >>
     qx_gen_tac `st` >> Cases_on `eval_exprs cx args st` >>
     rename1 `eval_exprs cx args st = (tailres,tailst)` >>
     Cases_on `tailres` >> simp[])) >>
  strip_tac >>
  qmatch_assum_abbrev_tac
    `gas_outcome_full _ _ _ _ (bind (eval_exprs cx args) _) _ mappedQ mappedR` >>
  `storage_trace_frame (bind (eval_exprs cx args) (\vs. return (v::vs)))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK u,G2,tn2)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
         gas_origin_ptr_path _ _ [] _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`DF` |-> `DF`,`lo` |-> `lo`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`ctx` |-> `ctx`,
     `func` |-> `func`,`PG` |-> `PG`,`tops` |-> `cx_tops cx`,
     `cx` |-> `cx`,`st0` |-> `st0`,
     `es` |-> `ee`,`s0` |-> `t`,`G0` |-> `G1`,`tn0` |-> `tn1`,
     `s1` |-> `u`,`G1` |-> `G2`,`tn1` |-> `tn2`,
     `Q` |-> `mappedQ`,`R` |-> `mappedR`]
      (Q.ISPEC `bind (eval_exprs cx args) (\vs. return (v::vs))`
        (Q.GEN `source`
          gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> disj1_tac >> qexists_tac `v` >> simp[] >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_exprs cx args) _) (ee,t,G1,tn1) _ _`
    (irule_at Any) >>
  conj_tac >- suspend "posts" >>
  simp[Abbr `mappedR`,Abbr `tailR`] >> rpt strip_tac >>
  qpat_assum `res = SUM_MAP (CONS v) I res'` mp_tac >>
  qpat_assum `expr_exit res' r` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[] >> Cases_on `res'` >> fs[]
QED

Resume concat_args_sim_full[posts]:
  rpt gen_tac >> qunabbrev_tac `mappedQ` >> qunabbrev_tac `tailQ` >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `!P k DF lo d ctx shadow_ctx PG tops func shadow_func cenv cx env st0
      es sa sb shadow_sa shadow_sb s0 G0 tn0 dv ov ow binst B bsz oinst. _`
    (K all_tac) >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` (K all_tac)) >>
  qpat_x_assum `res' = INL vs` SUBST_ALL_TAC >>
  qpat_x_assum `res = SUM_MAP (CONS v) I (INL vs)`
    (SUBST_ALL_TAC o SIMP_RULE bool_ss [sumTheory.SUM_MAP_def,combinTheory.I_THM]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (qpat_assum `ci_mono sa sc` mp_tac >>
     qpat_assum `ci_mono sc s2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >> decide_tac) >>
  `s0.vs_alloca_next <= t''.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
     qpat_assum `u.vs_alloca_next = t.vs_alloca_next` mp_tac >>
     qpat_assum `u.vs_alloca_next <= t''.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qexistsl [`G2`,`ee`,`u`,`s2`,`tn2`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z t'' = SOME w` by
    (qx_genl_tac [`z`,`w`] >> strip_tac >>
     `lookup_var z u = SOME w` by
       (qpat_assum `!z w. not_fresh_at sa z /\ _ ==> lookup_var z u = SOME w`
          (qspecl_then [`z`,`w`] mp_tac) >> simp[]) >>
     `not_fresh_at s2 z` by
       (qspecl_then [`sa`,`s2`,`z`] mp_tac freshWritesTheory.not_fresh_at_mono >> simp[]) >>
     qpat_assum `!z w. not_fresh_at s2 z /\ _ ==> lookup_var z t'' = SOME w`
       (qspecl_then [`z`,`w`] mp_tac) >> simp[]) >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t''.vs_allocas aid = SOME a` by
    (qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a`
       mp_tac >>
     qpat_assum `!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> FLOOKUP t''.vs_allocas aid = SOME a`
       mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `locals_kept cenv es ee' s0 t''` by
    (qspecl_then [`cenv`,`es`,`ee`,`ee'`,`sa`,`s0`,`u`,`t''`]
       mp_tac exprBopSimPropsTheory.locals_kept_trans >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  qexists_tac `v::vs` >>
  simp_tac bool_ss [sumTheory.INL_11,listTheory.LIST_REL_CONS1,
    listTheory.MAP,listTheory.FLAT,listTheory.LENGTH_APPEND,
    arithmeticTheory.ADD_ASSOC,listTheory.APPEND_ASSOC] >>
  rpt conj_tac >> asm_rewrite_tac[]
  >- (qexistsl [`v`,`vs`] >> asm_rewrite_tac[])
  >- (qpat_assum `!i. B+32 <= i /\ _ ==> i NOTIN tn'.t_mem` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      qpat_x_assum `!i. _` (qspec_then `i` assume_tac) >>
      full_simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      metis_tac[])
  >- suspend "oldframe" >> suspend "pureframe"
QED

Resume concat_args_sim_full[oldframe]:
  qx_genl_tac [`aid`,`p`,`n`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP u.vs_allocas aid = SOME (p,n)` by
    (qspecl_then [`aid`,`(p,n)`] mp_tac
       (Q.ASSUME `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
          FLOOKUP u.vs_allocas aid = SOME a`) >> simp_tac bool_ss [] >>
     disch_then (fn th => ACCEPT_TAC (MATCH_MP th
       (Q.ASSUME `FLOOKUP s0.vs_allocas aid = SOME (p,n)`)))) >>
  `aid < s2.cs_next_id` by
    (qpat_assum `aid < sa.cs_next_id` mp_tac >>
     qpat_assum `sa.cs_next_id <= s2.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!name lb lsz. local_region cenv ee.scopes u name lb lsz ==> p+n <= lb \/ lb+lsz <= p` by
    (mp_tac (Q.ASSUME `!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
        n+p <= lb \/ lb+lsz <= p`) >>
     mp_tac (Q.ASSUME `!name lb lsz. local_region cenv ee.scopes u name lb lsz <=>
        local_region cenv es.scopes s0 name lb lsz`) >>
     POP_ASSUM_LIST (K all_tac) >>
     full_simp_tac bool_ss [arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qspecl_then [`aid`,`p`,`n`] mp_tac
       (Q.ASSUME `!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
          aid < sa.cs_next_id /\ (p+n <= B \/ B+bsz <= p) /\
          (p+n <= w2n (ow:bytes32) \/ w2n ow+64 <= p) /\
          (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
             p+n <= lb \/ lb+lsz <= p) ==>
          mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory`) >>
     (impl_tac >-
       (CONV_TAC (SIMP_CONV bool_ss [arithmeticTheory.ADD_COMM]) >>
        ACCEPT_TAC (SIMP_RULE bool_ss [arithmeticTheory.ADD_COMM] (LIST_CONJ [
          Q.ASSUME `FLOOKUP s0.vs_allocas aid = SOME (p,n)`,
          Q.ASSUME `aid < sa.cs_next_id`,
          Q.ASSUME `n+p <= B \/ B+bsz <= p`,
          Q.ASSUME `n+p <= w2n (ow:bytes32) \/ w2n ow+64 <= p`,
          Q.ASSUME `!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
             n+p <= lb \/ lb+lsz <= p`])))) >>
     disch_then ACCEPT_TAC) >>
  qspecl_then [`aid`,`p`,`n`] mp_tac
    (Q.ASSUME `!aid p n. FLOOKUP u.vs_allocas aid = SOME (p,n) /\
       aid < s2.cs_next_id /\ (p+n <= B \/ B+bsz <= p) /\
       (p+n <= w2n (ow:bytes32) \/ w2n ow+64 <= p) /\
       (!name lb lsz. local_region cenv ee.scopes u name lb lsz ==>
          p+n <= lb \/ lb+lsz <= p) ==>
       mem_bytes_at p n t''.vs_memory = mem_bytes_at p n u.vs_memory`) >>
  (impl_tac >-
    (CONV_TAC (SIMP_CONV bool_ss [arithmeticTheory.ADD_COMM]) >>
     ACCEPT_TAC (SIMP_RULE bool_ss [arithmeticTheory.ADD_COMM] (LIST_CONJ [
       Q.ASSUME `FLOOKUP u.vs_allocas aid = SOME (p,n)`,
       Q.ASSUME `aid < s2.cs_next_id`,
       Q.ASSUME `n+p <= B \/ B+bsz <= p`,
       Q.ASSUME `n+p <= w2n (ow:bytes32) \/ w2n ow+64 <= p`,
       Q.ASSUME `!name lb lsz. local_region cenv ee.scopes u name lb lsz ==>
          p+n <= lb \/ lb+lsz <= p`])))) >>
  disch_then (fn th => ACCEPT_TAC (TRANS th (Q.ASSUME
    `mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory`)))
QED

Resume concat_args_sim_full[pureframe]:
  simp_tac bool_ss [listTheory.EXISTS_DEF,DE_MORGAN_THM] >> strip_tac >>
  `!id. s2.cs_next_id <= id ==> sa.cs_next_id <= id` by
    (mp_tac (Q.ASSUME `sa.cs_next_id <= s2.cs_next_id`) >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qpat_assum `~expr_has_effect e ==> _` mp_tac >>
  qpat_assum `~EXISTS expr_has_effect args ==> _` mp_tac >>
  qpat_assum `EVERY ($~ o expr_has_effect) args` mp_tac >>
  qpat_assum `~expr_has_effect e` mp_tac >>
  mp_tac (Q.ASSUME `!name lb lsz. local_region cenv ee.scopes u name lb lsz <=>
    local_region cenv es.scopes s0 name lb lsz`) >>
  mp_tac (Q.ASSUME `!aid a. FLOOKUP u.vs_allocas aid = SOME a ==>
    FLOOKUP t''.vs_allocas aid = SOME a`) >>
  qpat_assum `!id. s2.cs_next_id <= id ==> sa.cs_next_id <= id` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt disch_tac >>
  qpat_x_assum `~expr_has_effect e ==> _`
    (fn th => map_every assume_tac (CONJUNCTS (MATCH_MP th
      (Q.ASSUME `~expr_has_effect e`)))) >>
  qpat_x_assum `~EXISTS expr_has_effect args ==> _`
    (fn th => map_every assume_tac (CONJUNCTS (MATCH_MP
      (REWRITE_RULE [listTheory.NOT_EXISTS] th)
      (Q.ASSUME `EVERY ($~ o expr_has_effect) args`)))) >>
  conj_tac
  >- (qpat_assum `!name lb lsz. _ ==> mem_bytes_at lb lsz u.vs_memory = _` mp_tac >>
      qpat_assum `!name lb lsz. _ ==> mem_bytes_at lb lsz t''.vs_memory = _` mp_tac >>
      mp_tac (Q.ASSUME `!name lb lsz. local_region cenv ee.scopes u name lb lsz <=>
        local_region cenv es.scopes s0 name lb lsz`) >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qx_genl_tac [`p`,`n`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      sa.cs_next_id <= inst.inst_id /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
      regions_disjoint p n b sz` by
    (qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz` mp_tac >>
     mp_tac (Q.ASSUME `!aid a. FLOOKUP u.vs_allocas aid = SOME a ==>
       FLOOKUP t''.vs_allocas aid = SOME a`) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      s2.cs_next_id <= inst.inst_id /\ FLOOKUP t''.vs_allocas inst.inst_id = SOME (b,sz) ==>
      regions_disjoint p n b sz` by
    (mp_tac (Q.ASSUME `!inst b sz. MEM inst (fn_insts func) /\
       inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\
       FLOOKUP t''.vs_allocas inst.inst_id = SOME (b,sz) ==> regions_disjoint p n b sz`) >>
     mp_tac (Q.ASSUME `!id. s2.cs_next_id <= id ==> sa.cs_next_id <= id`) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
    (qspecl_then [`p`,`n`] mp_tac) >>
  qpat_assum `!p n. _ ==> mem_bytes_at p n t''.vs_memory = _`
    (qspecl_then [`p`,`n`] mp_tac) >>
  asm_simp_tac bool_ss [arithmeticTheory.ADD_COMM] >>
  metis_tac[]
QED

Finalise concat_args_sim_full
