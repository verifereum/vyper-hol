(* Resource boundary and expression/store composition for joint copies. *)
Theory fullAssignCopyCompose
Ancestors
  fullAssignCopyFacts bodySimFull gasOutcomeFullCompose vyperStorageFootprint
  assignBasePtrBoundary exprOperandVar gasShadowCompilePure gasShadowState
  stmtSimForced stmtSimProps stmtLoweringMono exprSimTopLevelProps
  gasExemptCert vyperStorageTrace gasSummary gasShadow fragExec
  exprSimTypedAlloc bodyPtrDefs loweringPosts exprSimMemDefs
  stmtSimDefs exprSimDefs loweringStateRelDefs ptrDiscipline venomState
  valueEncodingProps exprLowering exprLoweringProps compileEnv words arithmetic
Libs monadsyntax

Theorem topcopy_store_entry_resources:
  ~cx.txn.is_static /\
  lowered_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
  0 < type_memory_size tv /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v op s /\
  expr_store_bound cx (expr_type e) v op s /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
  ptr_buf_ok cenv e op G s /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  local_ptrs_reserved cenv sa ==>
  ?root w.
    op = Var root /\ lookup_var root s = SOME w /\
    not_fresh_at sb root /\
    ptr_covers G tn root s (val_store_size tv v) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    w2n w + type_memory_size tv < dimword(:256) /\
    w2n w + val_store_size tv v <= s.vs_alloca_next /\
    op_prov G (Lit slot) = NONE /\ op_taint tn (Lit slot) = {} /\
    eval_operand (Lit slot) s = SOME slot /\
    ~s.vs_call_ctx.cc_static
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_lowered] >>
  `val_store_size tv v = type_memory_size tv` by
    metis_tac[topcopy_val_store_size] >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[assign_base_nonbytes_footprint] >>
  `?w. eval_operand op s = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by simp[] >>
  `val_store_size tv v <= type_memory_bytes cenv (lowered_value_type cenv e)` by simp[] >>
  drule_all assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
  strip_tac >> gvs[] >>
  qexists_tac `w` >>
  simp[op_taint_def, eval_operand_def] >> rpt conj_tac
  >- fs[eval_operand_def]
  >- metis_tac[compile_lower_value_var]
  >- (gvs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def])
  >- (fs[expr_post_def] >> drule_all expr_val_at_bound >> simp[])
  >- (fs[expr_store_bound_def, eval_operand_def] >>
      first_x_assum (qspec_then `tv` mp_tac) >> simp[ADD_COMM]) >>
  fs[expr_post_def, stmt_state_rel_def, state_rel_def, call_ctx_rel_def]
QED

(* The continuation receives the actual source run and a running endpoint. *)
Theorem gas_outcome_full_bind_all_source:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q1
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. source (es with gas_obs :=
                       gas_explicit marks s.vs_gas_readings ++ tail) =
             (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Q1 H res mid G1 tn1 t) /\
     mid.gas_obs = [] /\ ~t.vs_halted ==>
     (?v. res = INL v /\
          gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
            (next v) (mid, t, G1, tn1) Q R) \/
     (?exc. res = INR exc /\
            !H. valid_horizon cx st0 H mid.storage_trace ==>
                Q H (INR exc) mid G1 tn1 t)) /\
  storage_trace_frame source /\
  (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf stop_state.
     gas_exempt_cert T tops (ctx, func) (ignore_bind source (return ()))
       (es, s) marks (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert T tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) marks (err, ee) (leaf, stop_state)) /\
  (!left v mid t right err ee leaf stop_state.
     gas_marked_exec T (ctx, func) source (es, s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert T tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) (left ++ right) (err, ee) (leaf, stop_state)) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (bind source next) (es, s, G, tn) Q R
Proof
  strip_tac >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn)
    (\H res ee G1 tn1 t. Q1 H res ee G1 tn1 t /\
       ee.gas_obs = [] /\ ~t.vs_halted)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ source _ _ _` (irule_at Any) >>
     simp[]) >>
  irule gas_outcome_full_bind_all >>
  qpat_assum `gas_outcome_full _ _ _ _ source _ (\H res ee G1 tn1 t. _ /\ _) _`
    (irule_at Any) >>
  rpt conj_tac >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
  `mid.gas_obs = [] /\ ~t.vs_halted` by metis_tac[] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* Conditional statement boundary. The store continuation chooses one
   endpoint before any final horizon is selected. *)
Theorem compile_assign_copy_frag_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty src id e es
    ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\ ~has_length_word typ /\
    (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    0 < type_slot_size tvt /\
    type_memory_bytes cenv typ = type_memory_size tvt /\
    cenv.ce_hashmap_info (src,id) = NONE /\
    cenv.ce_module_var_type (src,id) = SOME typ /\
    (!gs v es1.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
         (INL v,es1) ==> value_has_type tvt v) /\
    gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
      (lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)) /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
    (!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 sm shadow_sm op vv sV
        shadow_vv shadow_sV marks v ee G1 tn1 t.
       stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) sa = (cenv,sb) /\
       stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src,id))) (gas_shadow_expr e))
           shadow_sa = (cenv,shadow_sb) /\
       gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
       gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
       gas_shadow_function func shadow_func /\
       MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
       fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
       ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
       fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
       ret_pc_ok cenv sa s0 /\
       (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
         not_fresh_at sa x) /\ ~block_is_terminated sa /\
       gas_admissible
         (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
         (stmt_res_ok lctx) es /\
       return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
       (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es s0 /\
         storage_well_formed_on cx es (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
       ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
       compile_expr cenv (expr_type e) e sa = (vv,sV) /\
       unwrap_value cenv vv sV = (op,sm) /\
       lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
       compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa =
         (shadow_vv,shadow_sV) /\
       unwrap_value cenv shadow_vv shadow_sV = (op,shadow_sm) /\
       lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa =
         (op,shadow_sm) /\
       compile_assign_value cenv (Lit (n2w slot))
         (if tr then LocTransient else LocStorage) op F (vv_location vv)
         typ typ (type_memory_bytes cenv typ) sm = ((),sb) /\
       compile_assign_value cenv (Lit (n2w slot))
         (if tr then LocTransient else LocStorage) op F (vv_location shadow_vv)
         typ typ (type_memory_bytes cenv typ) shadow_sm = ((),shadow_sb) /\
       ee.gas_obs = [] /\ ~t.vs_halted /\
       storage_trace_domain cx st0 ee.storage_trace /\
       (!tail. bind (eval_expr cx e) (read_result cx)
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL v,ee with gas_obs := tail)) /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
         expr_store_bound cx (expr_type e) v op t /\
         t.vs_current_bb = sm.cs_current_bb /\
         t.vs_inst_idx = LENGTH sm.cs_current_insts /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
         ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
         (~is_word_type (post_value_type cenv e) ==>
            ptr_buf_ok cenv e op G1 t) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) ==>
       gas_outcome_full
         (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0
         (ignore_bind (record_storage_event (StorageRoot tr slot tvt))
           (write_storage_slot cx tr (n2w slot) tvt v))
         (ee,t,G1,tn1)
         (\H res ef G2 tn2 u. ?cenv''.
           stmt_lands lctx sb res u /\ ~u.vs_halted /\
           (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
           cenv_top_ext cenv cenv'' ef.scopes /\
           stmt_state_rel H ctx func cenv'' cx ef u /\
           storage_well_formed_on cx ef (FST H) /\
           return_buf_frame d cenv'' sb u /\ alloca_history func u /\
           s0.vs_alloca_next <= u.vs_alloca_next /\
           ghost_inv_at (DF H) lo d cenv'' cx ef G2 tn2 u /\
           (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
              lookup_var x u = SOME w) /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP u.vs_allocas aid = SOME b) /\
           (!x. not_fresh_at sa x ==>
              FLOOKUP G2 x = FLOOKUP G0 x /\
              op_taint tn2 (Var x) = op_taint tn0 (Var x)))
         (\H res ef gt r.
           !tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r)) ==>
    stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src,id))) (gas_shadow_expr e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
     ctx func cenv cx es s0` by metis_tac[storage_trace_domain_def] >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by simp[] >>
  drule_all assign_storage_copy_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value _ _ _ e sa = (op,sm)` >>
  `lowered_value_type cenv (gas_shadow_expr e) = expr_type (gas_shadow_expr e)`
    by simp[] >>
  `~(has_length_word (expr_type (gas_shadow_expr e)) /\
      is_empty_value_expr (gas_shadow_expr e))` by simp[] >>
  drule_all assign_storage_copy_code_parts >> strip_tac >> gvs[] >>
  `op' = op /\ gas_shadow_state sm sB` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`, `shadow_sa`] mp_tac o
        REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  gvs[] >>
  `cs_extends sa sm /\ cs_extends shadow_sa sB` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends sB shadow_sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa sB shadow_func` by
    metis_tac[fn_has_code_split] >>
  suspend "bind"
QED

Resume compile_assign_copy_frag_full[bind]:
  `eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
     bind (bind (eval_expr cx e) (read_result cx))
       (\v. ignore_bind (record_storage_event (StorageRoot tr slot tvt))
          (write_storage_slot cx tr (n2w slot) tvt v))` by
    (irule eval_assign_toplevel_action >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es`
    by metis_tac[forced_then_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `sB`, `op`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_tac >>
  qpat_x_assum `eval_stmt _ _ = _` SUBST_ALL_TAC >>
  irule gas_outcome_full_bind_all_source >>
  conj_tac >- simp[storage_trace_frame_ignore_bind,
    storage_trace_frame_event, storage_trace_frame_write_storage_slot] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> BETA_TAC >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
    storage_trace_frame_read_result] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Qrhs _` >>
  qexists_tac `Qrhs` >> reverse conj_tac
  >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> strip_tac >>
      Cases_on `res` >> gvs[] >>
      simp[stmt_exit_ptr_def] >> gen_tac >> disj1_tac >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      rpt (pop_assum kall_tac) >> metis_tac[expr_exit_INR_type]) >>
  suspend "store"
QED

Resume compile_assign_copy_frag_full[store]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `?v. res = INL v` by
    (qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[Abbr `Qrhs`] >> metis_tac[]) >>
  gvs[] >>
  fs[Abbr `Qrhs`] >>
  qpat_x_assum `!st0' sa' sb' shadow_sa' shadow_sb' s0' G0' tn0' sm shadow_sm op' vv' sV' shadow_vv shadow_sV marks v ee G1 tn1 t. _`
    drule_all >>
  simp[]
QED

Finalise compile_assign_copy_frag_full
