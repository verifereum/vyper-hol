(* Sequential owned positional operands for external calls. *)
Theory bodyFullExtCallRequestOperands
Ancestors
  bodyFullExtCallRequestSnapshotFull bodyFullExtCallRequestPositional
  bodyFullGhostFrame exprSimVVFrame exprSimWordArgs exprSimSource
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr fragGasOrigin fragGasMode bodyPtrDefs
  exprLowering compileEnv vyperInterpreter vyperState exprSimHypsDefs
  exprCanMutateProps gasShadowCompile gasShadowCompileHelpers
  gasShadowState gasShadowCompileContext exprLoweringProps exprOperandVar
  bodyFullPreds exprSimProps loweringPosts exprSimDefs
  list gasShadowCompileConvert fragExec vyperStorageTrace vyperStorageFootprint
  vyperStorageBackend
  exprSimCalldataSlice pair wordArgsPtr loweringStateRelDefs
  exprSimAbiEncodeArgsCountedLabels
  bodyFullExtCallRequestSavedStack bodyFullExtCallRequestSavedLocated

Theorem extcall_request_positional_outcome:
  body_exprs_full_ok cx xs /\ body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  EVERY (\e. ~expr_has_effect e) (xs ++ kw_es) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs sa = (svs,sb) /\
  compile_ext_call_args compile_expr cenv (MAP gas_shadow_expr kw_es)
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
    (MAP gas_shadow_expr xs) shadow_sa = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
    (\H res ee G tn t. ?vs.
      res = INL vs /\ LENGTH svs = LENGTH xs /\
      LIST_REL (\(e,sv) v.
        ((?tag op0. sv = StackValue tag op0) \/
         (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
           ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
         (?p si sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
           ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
           lowered_value_type cenv e = expr_type e /\
           compile_expr cenv (expr_type e) e si = (sv,sm0) /\
           sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
           sm0.cs_next_var <= sb.cs_next_var /\ sm0.cs_next_id <= sb.cs_next_id)) /\
        (?raw. read_result cx raw ee = (INL v,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
          vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
          vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
        vv_storage_live H cx sv ee t /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G t) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G t) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)

Proof
  map_every qid_spec_tac [`tn0`, `G0`, `s0`, `es`,
    `shadow_sa`, `sa`, `svs`] >>
  Induct_on `xs` >> rpt gen_tac >> strip_tac
  >- (gvs[compile_ext_call_args_def, comp_return_def] >>
      irule (Q.INST [`res` |-> `INL ([] : value list)`,
        `ee` |-> `es`, `t` |-> `s0`, `G'` |-> `G0`,
        `tn'` |-> `tn0`]
        (INST_TYPE [alpha |-> ``:value list``] gas_outcome_full_pure)) >>
      simp[evaluate_def, return_def] >>
      qexistsl [`G0`, `s0`, `tn0`] >>
      simp[gas_origin_ptr_path_rules, ghost_kept_at_def] >>
      qx_gen_tac `H` >> strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[]) >>
      qpat_x_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      simp[] >> strip_tac >> gvs[ghost_inv_at_def] >>
      first_assum ACCEPT_TAC) >>
  `~exprs_can_mutate cenv (xs ++ kw_es)` by
    (irule (cj 2 extrequest_snapshot_nonmutating) >>
     gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `~exprs_can_mutate cenv
    (MAP gas_shadow_expr xs ++ MAP gas_shadow_expr kw_es)` by
    (pure_rewrite_tac[GSYM MAP_APPEND, gas_shadow_expr_can_mutate] >>
     first_assum ACCEPT_TAC) >>
  qmatch_asmsub_rename_tac `body_exprs_full_ok cx (e::xs)` >>
  qabbrev_tac `head = comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv))` >>
  qabbrev_tac `shadow_head =
    comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e))
      (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))` >>
  `gas_shadow_compiles head shadow_head` by
    (simp[Abbr `head`, Abbr `shadow_head`] >>
     irule gas_shadow_compiles_bind >>
     simp[gas_shadow_compiles_snapshot_vv] >>
     metis_tac[gas_shadow_compile_expr]) >>
  Cases_on `head sa` >> rename1 `head sa = (sv,sm)` >>
  Cases_on `shadow_head shadow_sa` >>
  rename1 `shadow_head shadow_sa = (shadow_sv,shadow_sm)` >>
  `shadow_sv = sv /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_compiles head shadow_head`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >>
     simp[]) >>
  `?tail_svs. svs = sv::tail_svs /\
     compile_ext_call_args compile_expr cenv kw_es
       (MAP (lowered_value_type cenv) xs) xs sm = (tail_svs,sb) /\
     compile_ext_call_args compile_expr cenv (MAP gas_shadow_expr kw_es)
       (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
       (MAP gas_shadow_expr xs) shadow_sm = (tail_svs,shadow_sb)` by
    (qpat_x_assum `compile_ext_call_args _ _ kw_es _ (_::_) _ = _` mp_tac >>
     simp[Once compile_ext_call_args_def] >> strip_tac >>
     qpat_x_assum `compile_ext_call_args _ _ (MAP _ kw_es) _ (MAP _ (_::_)) _ = _`
       mp_tac >>
     simp[Once compile_ext_call_args_def] >> strip_tac >>
     qpat_x_assum `head sa = _` mp_tac >>
     qpat_x_assum `shadow_head shadow_sa = _` mp_tac >>
     simp[Abbr `head`, Abbr `shadow_head`, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
     rpt strip_tac >> gvs[] >>
     rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def])) >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    (conj_tac
     >- (`ci_mono sa (SND (head sa))` suffices_by simp[] >>
         simp_tac bool_ss [Abbr `head`] >> irule ci_mono_bind >>
         simp[ci_mono_compile_snapshot_vv, cj 1 compile_expr_ci_mono]) >>
     `ci_mono shadow_sa (SND (shadow_head shadow_sa))` suffices_by simp[] >>
     simp_tac bool_ss [Abbr `shadow_head`] >> irule ci_mono_bind >>
     simp[ci_mono_compile_snapshot_vv, cj 1 compile_expr_ci_mono]) >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    (qspecl_then [`xs`, `MAP (lowered_value_type cenv) xs`,
       `compile_expr`, `cenv`, `kw_es`, `sm`] mp_tac
       ci_mono_compile_ext_call_args >>
     qspecl_then [`MAP gas_shadow_expr xs`,
       `MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs)`,
       `compile_expr`, `cenv`, `MAP gas_shadow_expr kw_es`, `shadow_sm`] mp_tac
       ci_mono_compile_ext_call_args >>
     simp[cj 1 compile_expr_ci_mono]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[ci_mono_def, fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  `!x. vv_operand sv = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `head sa = (sv,sm)` mp_tac >>
     simp_tac bool_ss [Abbr `head`, comp_bind_def, LET_THM] >> pairarg_tac >>
     rename1 `compile_expr cenv (expr_type e) e sa = (original,si)` >>
     `!x. vv_operand original = Var x ==> not_fresh_at si x` by
       (qspecl_then [`cenv`, `expr_type e`, `e`, `sa`, `original`, `si`]
          mp_tac (cj 1 compiler_compile_var) >> simp[]) >>
     `!x. vv_operand (ext_call_arg_value (lowered_value_type cenv e) original) = Var x ==>
          not_fresh_at si x` by
       (Cases_on `original` >> gvs[ext_call_arg_value_def, contextTheory.vv_operand_def]) >>
     Cases_on `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) original))` >>
     simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def]
     >- (pairarg_tac >> strip_tac >> gvs[contextTheory.vv_operand_def] >>
         drule compiler_unwrap_value_var >>
         Cases_on `ext_call_arg_value (lowered_value_type cenv e) original` >>
         gvs[contextTheory.vv_operand_def]) >>
     strip_tac >> gvs[]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> gvs[ci_mono_def]) >>
  `body_expr_full_ok cx e /\ expr_body_pre cenv cx env e es /\
   ~expr_has_effect e` by
    (gvs[Once body_exprs_full_ok_def] >>
     gvs[EVERY_MEM] >> metis_tac[MEM]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule (Q.INST [`sb` |-> `sm`, `shadow_sb` |-> `shadow_sm`,
    `sv` |-> `sv`] extcall_request_snapshot_classified_cps_full) >>
  gvs[Abbr `head`, Abbr `shadow_head`] >>
  conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qexistsl_tac [`cenv`, `d`, `env`, `sa`, `shadow_func`,
    `shadow_sa`, `shadow_sm`, `sm`, `shadow_sv`, `tops`] >>
  simp[] >>
  map_every qx_gen_tac [`marks`, `v`, `mid`, `G1`, `tn1`, `t`] >>
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_x_assum `!tail. _ = (INL v,_)` (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by
    (qspecl_then [`cenv`, `cx`, `env`, `e`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `INL v`, `mid with gas_obs := []`]
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) expr_body_pre_eval >>
     impl_tac >- (conj_tac >- simp[] >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  `body_exprs_full_ok cx xs` by
    (drule_at (Pat `bind _ _ _ = _`)
       (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_read_INL) >>
     strip_tac >> gvs[Once body_exprs_full_ok_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by gvs[ci_mono_def] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sm x)` by
    (conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  (qpat_x_assum `!svs sa shadow_sa es s0 G0 tn0. _`
    (qspecl_then [`tail_svs`, `sm`, `shadow_sm`, `mid`, `t`, `G1`, `tn1`]
      mp_tac) >>
  impl_tac
  >- simp[] >>
  disch_tac) >>
  (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
     (Q.INST [`Q'` |-> `\H res ee G' tn' u.
        (?tail_marks. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (s,G,tn) tail_marks (OK u,G',tn')) /\ Q H res ee G' tn' u`,
       `R'` |-> `R`] gas_outcome_full_post_path) >>
   impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[]) >>
   disch_tac) >>
  (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
     (Q.INST [`f` |-> `SUM_MAP (CONS v) I`,
       `source'` |-> `bind (eval_exprs cx xs) (\vs. return (v::vs))`]
       (INST_TYPE [alpha |-> ``:value list``, beta |-> ``:value list``]
         gas_outcome_full_source_map)) >>
   disch_then (qspecl_then [`xs`, `v`] mp_tac) >>
   impl_tac
   >- (simp[] >> qx_gen_tac `src` >>
       Cases_on `eval_exprs cx xs src` >>
       rename1 `eval_exprs cx xs src = (rs,ee)` >>
       Cases_on `rs` >> simp[bind_def, return_def]) >>
   disch_tac) >>
  (irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_exprs cx xs) _) _ _ _`
    (irule_at Any) >>
  reverse conj_tac
  >- (simp[] >> rpt strip_tac >> gvs[] >>
      rename1 `expr_exit (SUM_MAP (CONS v) I rv) stop` >>
      Cases_on `rv` >> fs[expr_exit_def])) >>
  qx_genl_tac [`H`, `res`, `ee`, `G2`, `tn2`, `u`] >>
  BETA_TAC >> strip_tac >> gvs[] >>
  `u.vs_labels = t.vs_labels` by
    (qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) _ (OK u,G2,tn2)`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     `gas_marked_path F ctx func t (LENGTH tail_marks) (OK u)` by
       (simp[gas_marked_path_def] >>
        metis_tac[gas_origin_path_erase, gas_marked_path_exec]) >>
     drule abi_args_marked_path_labels >> simp[]) >>
  `storage_trace_frame (bind (eval_exprs cx xs) (\vs. return (v::vs)))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qpat_assum `!tail. bind (eval_exprs cx xs) _ _ = _`
    (qspec_then `[]` assume_tac) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (rename1 `bind (eval_exprs cx xs) _ (mid with gas_obs := readings ++ []) = _` >>
     fs[] >>
     drule_all (SIMP_RULE (srw_ss()) []
       (Q.INST [`st` |-> `mid with gas_obs := readings`,
                `st'` |-> `ee with gas_obs := []`] valid_horizon_frame)) >>
     simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th) >> strip_assume_tac th) >>
  `mid.scopes = es.scopes` by
    (qpat_assum
       `mid with <|outcomes := NONE; gas_obs := []; storage_trace := []|> = _`
       (mp_tac o AP_TERM ``\st:evaluation_state. st.scopes``) >> simp[]) >>
  `ee.scopes = mid.scopes /\ ee.accounts = mid.accounts /\
   ee.tStorage = mid.tStorage /\ ee.immutables = mid.immutables` by
    (qpat_assum
       `ee with <|outcomes := NONE; gas_obs := []; storage_trace := []|> = _`
       (mp_tac o AP_TERM
         ``\st:evaluation_state. (st.scopes,st.accounts,st.tStorage,st.immutables)``) >>
     qpat_assum
       `mid with <|outcomes := NONE; gas_obs := []; storage_trace := []|> = _`
       (mp_tac o AP_TERM
         ``\st:evaluation_state. (st.scopes,st.accounts,st.tStorage,st.immutables)``) >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `!n b sz. local_region cenv mid.scopes t n b sz <=>
            local_region cenv ee.scopes u n b sz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (qspecl_then [`cenv`, `mid.scopes`, `sm`, `ee.scopes`, `t`, `u`,
          `n`, `b`, `sz`] mp_tac local_region_frame_fwd >> simp[]) >>
     qspecl_then [`func`, `cenv`, `mid.scopes`, `t`, `sm`, `ee.scopes`, `u`,
       `n`, `b`, `sz`] mp_tac local_region_frame >> simp[] >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
       (mp_tac o SRULE [stmt_state_rel_def, state_rel_def]) >>
     simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by gvs[ci_mono_def] >>
  `pure_frame cenv func es sa s0 u` by
    (qspecl_then [`cenv`, `func`, `es`, `mid`, `sa`, `sm`, `s0`, `t`, `u`]
       mp_tac pure_frame_trans >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x u = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     `lookup_var x t = SOME w` by
       (qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _` irule >> simp[]) >>
     qpat_x_assum `!x w. not_fresh_at sm x /\ _ ==> _` irule >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all (SIMP_RULE (srw_ss()) []
       (Q.INST [`st` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                `st'` |-> `mid with gas_obs := []`] valid_horizon_frame)) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_tac o SRULE [stmt_state_rel_def, state_rel_def]) >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv mid.scopes t n b sz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (qspecl_then [`cenv`, `es.scopes`, `sa`, `mid.scopes`, `s0`, `t`,
          `n`, `b`, `sz`] mp_tac local_region_frame_fwd >> simp[]) >>
     qspecl_then [`func`, `cenv`, `es.scopes`, `s0`, `sa`, `mid.scopes`, `t`,
       `n`, `b`, `sz`] mp_tac local_region_frame >> simp[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
   ghost_kept cenv mid sm G1 tn1 t G2 tn2` by
    (conj_tac
     >- (PURE_REWRITE_TAC [ghost_kept_def] >>
         qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
           (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     PURE_REWRITE_TAC [ghost_kept_def] >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (drule_all wordArgsPtrTheory.ghost_kept_trans >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G2 tn2`
       (mp_tac o REWRITE_RULE [ghost_kept_def]) >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
     rpt (pop_assum kall_tac) >> simp[ghost_kept_at_def] >> metis_tac[]) >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
       (mp_tac o SRULE [stmt_state_rel_def, state_rel_def]) >> simp[]) >>
  qpat_assum `!x. vv_operand _ = Var x ==> not_fresh_at sm x`
    (assume_tac o SRULE [contextTheory.vv_operand_def])
  >| [
    rename1 `vv_at cenv cx _ sa sm mid _ (StackValue saved_tag saved_op) t` >>
    mp_tac (Q.INST [`op` |-> `saved_op`, `tag` |-> `saved_tag`]
      (INST_TYPE [alpha |-> ``:256``]
        extcall_request_saved_stack_endpoint)) >>
    (impl_tac >- simp[contextTheory.vv_operand_def]) >>
    disch_then (map_every assume_tac o CONJUNCTS),
    mp_tac (Q.INST [`D` |-> `DF H`]
      (INST_TYPE [alpha |-> ``:256``]
        extcall_request_saved_located_endpoint)) >>
    (impl_tac >-
      simp[contextTheory.vv_operand_def, contextTheory.vv_location_def,
           vv_storage_live_def]) >>
    disch_then (map_every assume_tac o CONJUNCTS o
      SRULE [contextTheory.vv_operand_def, contextTheory.vv_location_def,
             vv_storage_live_def, arithmeticTheory.ADD_COMM]),
    rename1 `compile_expr cenv (expr_type e) e sa = (_,saved_end)` >>
    qpat_assum `lowered_value_type cenv e = expr_type e` (fn eq =>
      mp_tac (REWRITE_RULE [eq] (Q.INST [`D` |-> `DF H`]
        (INST_TYPE [alpha |-> ``:256``]
          extcall_request_saved_located_endpoint)))) >>
    (impl_tac >-
      (simp[contextTheory.vv_operand_def, contextTheory.vv_location_def,
            vv_storage_live_def] >>
       qexistsl_tac [`sa`, `saved_end`] >> simp[])) >>
    disch_then (map_every assume_tac o CONJUNCTS o
      SRULE [contextTheory.vv_operand_def, contextTheory.vv_location_def,
             vv_storage_live_def, arithmeticTheory.ADD_COMM])
  ] >>
  simp[contextTheory.vv_operand_def, contextTheory.vv_location_def,
       vv_storage_live_def, arithmeticTheory.ADD_COMM] >>
  rpt conj_tac
  >>~- ([`LIST_REL _ (ZIP (xs,tail_svs)) vs (* g *)`],
    irule LIST_REL_mono >>
    qpat_assum `LIST_REL _ (ZIP (xs,tail_svs)) vs` (irule_at Any) >>
    simp[pairTheory.FORALL_PROD] >> rpt gen_tac >> disch_tac >>
    pop_assum mp_tac >>
    qpat_assum `sa.cs_next_var <= sm.cs_next_var` mp_tac >>
    qpat_assum `sa.cs_next_id <= sm.cs_next_id` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
    imp_res_tac exprSimCalldataSliceTheory.vv_at_start_mono >>
    metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >>~- ([`s0.vs_alloca_next <= u.vs_alloca_next (* g *)`],
    metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >>~- ([`!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _ (* g *)`],
    metis_tac[])
  >>~- ([`?raw. read_result cx raw ee = (INL v,ee) /\ _ (* g *)`],
    first_assum ACCEPT_TAC)
  >> qpat_assum `compile_expr cenv (expr_type e) e sa = (_,_)` (irule_at Any) >>
  simp[] >>
  qpat_assum `ci_mono sm sb` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
  rpt strip_tac >> decide_tac
QED
