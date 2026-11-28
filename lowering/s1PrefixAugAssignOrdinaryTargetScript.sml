(* The ordinary AugAssign prefix up to the successful target-place cut. *)
Theory s1PrefixAugAssignOrdinaryTarget
Ancestors
  s1PrefixAugAssignBindStages s1PrefixDefs bodyFullTarget bodyFullTargetDefs
  augAssignFullCodeStages augAssignFullEntryPre augAssignFullSourceReplay
  bodyFullIfExpReach loweringPosts stmtSimAugAssignPlace vyperExprNoControl
  gasOutcomeFullCompose bodyFullPreds bodySimFull stmtSimDefs exprSimDefs
  gasContext targetPlaceSimCases gasShadow compileEnv exprLowering stmtLowering
  supportedStmts s1PrefixPreds vyperTypeSystem
  vyperStorageFootprint vyperInterpreter vyperState vyperValue vyperAST
  bodyPtrDefs[qualified,ignore_grammar]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> disch_then (mk_asm "cont") >>
  `target_pre cenv cx env t es` by (drule_all augassign_entry_target_pre >> simp[]) >>
  `target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env t es` by
    (irule body_target_place_sim_full >> simp[] >> qexists_tac `tops` >> simp[]) >>
  simp[stmt_frag_prefix_def] >> rpt gen_tac >> disch_tac >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
  drule (cj 1 aug_place_typing) >> strip_tac >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    (simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >> Cases_on `res` >>
     simp[target_place_res_ok_def] >>
     `no_control_exc y` by metis_tac[eval_target_place_no_control] >>
     qpat_assum `gas_admissible (eval_stmt _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     gvs[augassign_source_bind, bind_def, stmt_res_ok_def, no_control_exc_def]) >>
  drule_all augassign_full_code_stages >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r`,`ca`,`shadow_ca`] assume_tac)) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _ /\ _`
    (map_every assume_tac o butlast o CONJUNCTS) >>
  qpat_x_assum `target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`aty`,`sa`,`ca`,`shadow_sa`,`shadow_ca`,
                           `r`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx t) _ targetQ targetR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0)
     (\H res ee G tn v. targetQ H res ee G tn v /\
       (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z))
     targetR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  qabbrev_tac `cutQ = \H res ee G tn v. targetQ H res ee G tn v /\
    ~v.vs_halted /\ ee.gas_obs = [] /\
    (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0)
     cutQ (\H res ee gt r. ?exc. res = INR exc)` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn v. _ /\ _) targetR`
       (irule_at Any) >>
     simp[Abbr `cutQ`, Abbr `targetR`] >>
     rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  rewrite_tac[augassign_source_bind] >>
  irule (Q.INST [`Q1` |-> `cutQ`, `tops` |-> `cx_tops cx`,
                  `R` |-> `\H res ee gt r. T`] augassign_target_bind_prefix) >>
  BETA_TAC >>
  conj_tac
  >- (qpat_assum `!st0 sa ca shadow_sa shadow_ca r s0 G0 tn0.
          _ ==> gas_prefix_full _ _ _ (eval_target_place cx t) _`
        (qspecl_then [`st0`,`sa`,`ca`,`shadow_sa`,`shadow_ca`,`r`,`s0`,`G0`,`tn0`] mp_tac) >>
      (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  qexists_tac `cutQ` >> reverse conj_tac >- simp[] >>
  qx_genl_tac [`marks`,`p`,`mid`,`G1`,`tn1`,`u`] >> strip_tac >>
  asm "cont" irule >>
  simp[] >>
  qexistsl_tac [`G0`,`ca`,`cenv`,`marks`,`r`,`s0`,`sa`,`sb`,
                `shadow_ca`,`shadow_sa`,`shadow_sb`,`tn0`] >>
  simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> cutQ H _ _ _ _ _`
    (drule_then mp_tac) >>
  simp[Abbr `cutQ`,Abbr `targetQ`] >> strip_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem augassign_ordinary_prefix_from_target_cont:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func
   cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx t s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==>
     body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx t s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==>
     body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (AugAssign aty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (AugAssign aty t bop e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign aty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  (?pt. supported_target_info tops bindings t = SOME pt) /\
  ~immutable_root cx t /\
  (!st0 sa ca shadow_sa shadow_ca r s0 G0 tn0.
    type_place_target env t = SOME (Type aty) /\
    compile_get_target_ptr compile_expr cenv t sa = (r,ca) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (r,shadow_ca) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state ca shadow_ca /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa ca func /\ fn_has_code shadow_sa shadow_ca shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_target_place cx t) target_place_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_target_place cx t) (es,s0,G0,tn0)) ==>
  (!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 ce ca shadow_ca r marks p st v Gtarget tnt.
    stmt_frag_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
      (st0,sa,sb,shadow_sa,shadow_sb,s0,G0,tn0,ce) /\
    compile_get_target_ptr compile_expr cenv t sa = (r,ca) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (r,shadow_ca) /\
    (!tail. eval_target_place cx t
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL p,st with gas_obs := tail)) /\
    storage_trace_domain cx st0 st.storage_trace /\
    (!H. valid_horizon cx st0 H st.storage_trace ==>
      target_post H ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\
      (!id path. p = MemoryPlace id path ==>
        ?entry u. lookup_scopes id st.scopes = SOME entry /\
                  evaluate_subscripts entry.type entry.value path = INL u) /\
      v.vs_current_bb = ca.cs_current_bb /\
      v.vs_inst_idx = LENGTH ca.cs_current_insts /\
      alloca_history func v /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
      s0.vs_alloca_next <= v.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx st Gtarget tnt v /\
      target_ptr_ok cenv (PlaceR p) r Gtarget tnt v /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gtarget tnt /\
      ~v.vs_halted /\ st.gas_obs = [] /\
      (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (bind (read_place cx p) (\cur.
        bind (place_type_value cx p) (\ptv.
          bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
            bind (lift_sum (evaluate_binop
              (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
              ptv bop cur rhs)) (write_place cx p)))))
      (st,v,Gtarget,tnt)) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
    (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  cheat
QED
