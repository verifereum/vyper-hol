(* Sequential positional operands at a common physical endpoint. *)
Theory bodyFullExtCallPosList
Ancestors
  bodyFullShadowBodyInv
  bodyFullExtCallPosWord bodyFullExtCallPosAggregate bodyFullExtCallPosTransport
  bodyFullPreds bodySimFull gasOutcomeFullCompose gasExemptCert fragGasOriginPtr bodyFullIfExpReach
  exprLowering exprLoweringProps compileEnv context gasShadowCompile
  gasShadowCompileHelpers gasShadowState gasShadowCompileContext fragExec
  vyperInterpreter vyperState vyperStorageFootprint vyperStorageTrace
  exprSimHypsDefs exprSimMemDefs loweringPosts bodyPtrDefs wordArgsPtr
  stateRelProj exprOperandVar exprSimSource exprSimWordArgs list
  bodyFullExtCallDefaultKeyword targetPureWalkSource bodyStorageCases
  vyperEvalExprPreservesScopesDom vyperMachineFrame

(* No delayed copy is needed for an effect-free suffix. *)
Theorem positional_post_source_labels[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R /\
  (!H res ee G' tn' t.
     (?xs. !tail. source (es with gas_obs := xs ++ tail) =
                   (res,ee with gas_obs := tail)) /\
     valid_horizon cx st0 H ee.storage_trace /\ t.vs_labels = s.vs_labels /\
     Q H res ee G' tn' t ==> Q' H res ee G' tn' t) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gasOutcomeFullTheory.gas_outcome_full_def]) >>
  rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      qx_gen_tac `H` >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >> conj_tac
          >- (qexists_tac `gas_explicit marks s.vs_gas_readings` >> simp[]) >>
          drule gas_origin_ptr_path_projections >> strip_tac >>
          drule fragGasOriginTheory.gas_origin_path_erase >>
          disch_then (mp_tac o MATCH_MP fragGasModeTheory.gas_marked_path_exec) >>
          metis_tac[fragGasPathFrameMemTheory.gas_path_code_labels]) >>
      disj2_tac >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem extcall_request_positional_packing_outcome:
  body_exprs_full_ok cx xs /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
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
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_no_wrap inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
        (?si sm ss vv raw copy.
          compile_expr cenv (expr_type e) e si = (vv,sm) /\
          compile_snapshot_vv cenv copy
            (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
          (~copy ==> ~exprs_can_mutate cenv kw_es) /\
          (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
            ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) t = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
                SOME (w2n w,type_memory_size tv) /\
              sm.cs_next_id < ss.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes t n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
          sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
          sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
          ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
          local_ptrs_reserved cenv si /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          ((?tag op0. sv = StackValue tag op0) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
             lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
          read_result cx raw ee = (INL v,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
          vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
          vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
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
      wb_frame cenv es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv cenv cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  map_every qid_spec_tac [`tn0`, `G0`, `s0`, `es`, `shadow_sa`, `sa`, `svs`] >>
  Induct_on `xs` >> rpt gen_tac >> strip_tac
  >- (gvs[compile_ext_call_args_def, comp_return_def] >>
      irule (Q.INST [`res` |-> `INL ([] : value list)`, `ee` |-> `es`,
                    `t` |-> `s0`, `G'` |-> `G0`, `tn'` |-> `tn0`]
        (INST_TYPE [alpha |-> ``:value list``] gas_outcome_full_pure)) >>
      simp[evaluate_def, return_def] >>
      qexistsl [`G0`, `s0`, `tn0`] >>
      simp[gas_origin_ptr_path_rules, ghost_kept_at_refl] >>
      qx_gen_tac `H` >> strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
        (irule storage_well_formed_on_backends >> simp[]) >>
      qpat_x_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      simp[] >> strip_tac >> gvs[ghost_inv_at_def, wb_frame_refl] >>
      first_assum ACCEPT_TAC) >>
  qmatch_asmsub_rename_tac `body_exprs_full_ok cx (e::xs)` >>
  qabbrev_tac `copy = exprs_can_mutate cenv (xs ++ kw_es)` >>
  `exprs_can_mutate cenv (MAP gas_shadow_expr xs ++ MAP gas_shadow_expr kw_es) = copy` by
    simp[Abbr `copy`, GSYM MAP_APPEND, gas_shadow_expr_can_mutate] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,si)` >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa = (shvv,shadow_si)` >>
  `shvv = vv /\ gas_shadow_state si shadow_si` by
    (qspecl_then [`cenv`, `expr_type e`, `e`, `T`] mp_tac
       (cj 1 gas_shadow_compile_expr) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >> rename1 `compile_expr cenv (expr_type e) e sa = (vv,si)` >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
        lowered_value_type cenv e` by
    metis_tac[extcall_operand_snapshot_type] >>
  `is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type] >>
  qabbrev_tac `snap = compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)` >>
  `gas_shadow_compiles snap snap` by
    simp[Abbr `snap`, gasShadowCompileConvertTheory.gas_shadow_compiles_snapshot_vv] >>
  Cases_on `snap si` >> rename1 `snap si = (sv,sm)` >>
  Cases_on `snap shadow_si` >> rename1 `snap shadow_si = (shsv,shadow_sm)` >>
  `shsv = sv /\ gas_shadow_state sm shadow_sm` by
    (qpat_assum `gas_shadow_compiles snap snap`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`si`, `shadow_si`] mp_tac) >> simp[]) >>
  gvs[] >> rename1 `snap si = (sv,sm)` >>
  `?tail_svs. svs = sv::tail_svs /\
     compile_ext_call_args compile_expr cenv kw_es
       (MAP (lowered_value_type cenv) xs) xs sm = (tail_svs,sb) /\
     compile_ext_call_args compile_expr cenv (MAP gas_shadow_expr kw_es)
       (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
       (MAP gas_shadow_expr xs) shadow_sm = (tail_svs,shadow_sb)` by
    (qpat_x_assum `compile_ext_call_args _ _ kw_es _ (_::_) _ = _`
       (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def]) >>
     qpat_x_assum `compile_ext_call_args _ _ (MAP _ kw_es) _ (_::_) _ = _`
       (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def]) >>
     simp[comp_bind_def, comp_return_def, Abbr `snap`] >>
     rpt (pairarg_tac >> gvs[]) >>
     rpt strip_tac >> gvs[]) >>
  `ci_mono sa si /\ ci_mono shadow_sa shadow_si` by
    (conj_tac
     >- (qspec_then `sa` mp_tac (Q.SPECL [`cenv`, `expr_type e`, `e`]
          (cj 1 compile_expr_ci_mono)) >> simp[]) >>
     qspec_then `shadow_sa` mp_tac
       (Q.SPECL [`cenv`, `expr_type e`, `gas_shadow_expr e`]
          (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono si sm /\ ci_mono shadow_si shadow_sm` by
    (qunabbrev_tac `snap` >>
     qspecl_then [`cenv`, `copy`, `ext_call_arg_value (lowered_value_type cenv e) vv`, `si`]
       mp_tac ci_mono_compile_snapshot_vv >>
     qspecl_then [`cenv`, `copy`, `ext_call_arg_value (lowered_value_type cenv e) vv`, `shadow_si`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by metis_tac[ci_mono_trans] >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    (qspecl_then [`xs`, `MAP (lowered_value_type cenv) xs`,
       `compile_expr`, `cenv`, `kw_es`, `sm`] mp_tac ci_mono_compile_ext_call_args >>
     qspecl_then [`MAP gas_shadow_expr xs`,
       `MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs)`,
       `compile_expr`, `cenv`, `MAP gas_shadow_expr kw_es`, `shadow_sm`]
       mp_tac ci_mono_compile_ext_call_args >> simp[cj 1 compile_expr_ci_mono]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[ci_mono_def, fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at si x` by
    (qspecl_then [`cenv`, `expr_type e`, `e`, `sa`, `vv`, `si`]
       mp_tac (cj 1 compiler_compile_var) >> simp[]) >>
  `!x. vv_operand (ext_call_arg_value (lowered_value_type cenv e) vv) = Var x ==>
    not_fresh_at si x` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_operand_def]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at sm x` by
    (qunabbrev_tac `snap` >>
     qpat_x_assum `compile_snapshot_vv _ _ _ si = _` mp_tac >>
     Cases_on `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` >>
     simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def]
     >- (pairarg_tac >> strip_tac >> gvs[vv_operand_def] >>
         drule compiler_unwrap_value_var >>
         Cases_on `ext_call_arg_value (lowered_value_type cenv e) vv` >>
         gvs[vv_operand_def]) >>
     Cases_on `copy` >> simp[comp_bind_def, comp_return_def]
     >- (pairarg_tac >> strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
         drule compiler_materialize_vv_var >> simp[]) >>
     strip_tac >> gvs[]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at sb x` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
  `body_expr_full_ok cx e /\ expr_body_pre cenv cx env e es` by
    (gvs[Once body_exprs_full_ok_def] >> metis_tac[]) >>
  `(is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) <=>
     is_word_type (expr_type e)) /\
   (~is_word_type (expr_type e) ==>
    compile_materialize_vv cenv (lowered_value_type cenv e)
      (ext_call_arg_value (lowered_value_type cenv e) vv) =
    compile_materialize_vv cenv (lowered_value_type cenv e) vv)` by
    metis_tac[extcall_operand_materialize_retag] >>
  `is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
              aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
        ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) t = SOME w /\
          evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
          val_wf tv v /\
          FLOOKUP t.vs_allocas si.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          si.cs_next_id < sm.cs_next_id /\
          (!n b sz. local_region cenv ee.scopes t n b sz ==>
            regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\
         compile_expr cenv (expr_type e) e sa = (sv,sm))) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sm ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
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
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sm t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))` by
    (qunabbrev_tac `snap` >>
     Cases_on `is_word_type (expr_type e)`
     >- (`compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv)
            si = (sv,sm) /\
          compile_snapshot_vv cenv F (ext_call_arg_value (lowered_value_type cenv e) vv)
            shadow_si = (sv,shadow_sm)` by fs[compile_snapshot_vv_def] >>
         irule gas_outcome_full_post_mono >> irule_at Any extcall_request_snapshot_word_owned_full >>
         qexistsl [`tops`,`sv`,`shadow_sm`,`shadow_sa`,`shadow_func`,
                   `sm`,`sa`,`env`,`d`,`cenv`] >>
         simp[comp_bind_def] >> rpt gen_tac >> strip_tac >>
         gvs[vv_location_def, vv_storage_live_def, vv_store_bound_def] >> metis_tac[]) >>
     reverse (Cases_on `copy`)
     >- (`si = sm /\ shadow_si = shadow_sm` by
           fs[compile_snapshot_vv_def, comp_return_def] >>
         irule gas_outcome_full_post_source >> irule_at Any extcall_pos_aggregate_outcome >>
         qexistsl [`tops`,`sv`,`shadow_sa`,`shadow_func`,
                   `shadow_sm`,`sa`,`sm`,`env`,`d`,`cenv`] >>
         simp[] >> rpt gen_tac >> strip_tac >> qexists_tac `v` >> simp[] >>
         qpat_assum `?raw. read_result cx raw ee = (INL v,ee) /\ _`
           (qx_choose_then `raw` strip_assume_tac) >>
         `!tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv ==>
            val_wf tv v` by
           (rpt strip_tac >>
            qpat_x_assum `?obs. !tail. _` (qx_choose_then `obs` assume_tac) >>
            qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
              (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
            drule_all (REWRITE_RULE [ETA_AX] abiEncodeArgsCaseTheory.abi_args_success_ready) >>
            simp[] >> metis_tac[]) >>
         qexists_tac `raw` >> simp[] >>
         irule extcall_saved_physical_store_bound >> metis_tac[]) >>
     `compile_materialize_vv cenv (lowered_value_type cenv e)
         (ext_call_arg_value (lowered_value_type cenv e) vv) =
       compile_materialize_vv cenv (lowered_value_type cenv e) vv` by
       metis_tac[extcall_operand_materialize_retag] >>
     `?op. compile_materialize_vv cenv (lowered_value_type cenv e) vv si = (op,sm) /\
       compile_materialize_vv cenv (lowered_value_type cenv e) vv shadow_si = (op,shadow_sm) /\
       sv = LocatedValue (lowered_value_type cenv e) (mk_ptr op LocMemory)` by
       (qpat_assum `compile_snapshot_vv cenv T _ si = _` mp_tac >>
        qpat_assum `compile_snapshot_vv cenv T _ shadow_si = _` mp_tac >>
        simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
        rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[]) >>
     strip_tac >>
     irule gas_outcome_full_initial_domain >>
     simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
          storage_trace_frame_read_result] >>
     strip_tac >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
       (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
          fs[storage_trace_domain_def] >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func cenv cx es s0 /\ _`
          (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
        qpat_assum `stmt_state_rel _ ctx func cenv cx es s0`
          (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
     irule gas_outcome_full_post_mono >> irule_at Any extcall_operand_materialized_full >>
     rpt (first_assum (irule_at Any)) >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qexists_tac `v` >> simp[vv_location_def, vv_storage_live_def, vv_operand_def, mk_ptr_def] >>
     qpat_assum `?w aid tv. _` (qx_choosel_then [`w`,`aid`,`tv`] strip_assume_tac) >>
     `w2n w + type_memory_size tv <= t.vs_alloca_next` by
       (irule allocaSiteResourceTheory.alloca_site_registered_below >> conj_tac
        >- metis_tac[stmt_state_rel_local_ptrs_alloca] >>
        qexists_tac `aid` >> simp[]) >>
     `val_footprint tv v <= type_memory_size tv` by simp[exprSimPropsTheory.val_footprint_le] >>
     `val_in_memory tv v (w2n w) t.vs_memory` by
       (drule_all bodyPtrBopHashFootprintTheory.ptr_mem_ok_robust >>
        simp[valueEncodingDefsTheory.mem_agree_outside_def]) >>
     qpat_assum `?x. op = Var x` (qx_choose_then `p` SUBST_ALL_TAC) >>
     conj_tac >- (qexistsl_tac [`p`,`w`,`tv`] >> simp[]) >>
     conj_tac
     >- (qexists_tac `Value v` >>
         (mp_tac (Q.INST [`cenv` |-> `cenv`, `e` |-> `e`, `cut` |-> `sm`,
            `a` |-> `si`, `si` |-> `sa`, `ss` |-> `sm`,
            `mid` |-> `ee`, `ee` |-> `ee`, `t` |-> `t`, `u` |-> `t`,
            `G1` |-> `G`, `G2` |-> `G`, `tn1` |-> `tn`, `tn2` |-> `tn`,
            `input` |-> `ext_call_arg_value (lowered_value_type cenv e) vv`,
            `saved` |-> `sv`, `x` |-> `p`, `w` |-> `w`,
            `tv` |-> `tv`, `aid` |-> `aid`, `sz` |-> `type_memory_size tv`,
            `lo` |-> `lo`, `cx` |-> `cx`, `v` |-> `v`]
            extcall_request_materialized_endpoint) >>
          simp[wb_frame_refl, ghost_kept_at_refl, vv_operand_def, mk_ptr_def,
               loweringStateRelDefsTheory.regions_disjoint_def] >>
          fs[ci_mono_def] >> metis_tac[])) >>
     simp[wb_frame_def]) >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl [`mid`, `t`, `v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[cj 6 evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qexists_tac `headQ` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `headR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[] >> strip_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  strip_tac >> disj1_tac >>
  qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)`
    (mk_asm "head_path") >>
  qunabbrev_tac `headQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- fs[storage_trace_domain_def]) >>
  disch_then (qx_choose_then `v` (SUBST_ALL_TAC o CONJUNCT1)) >>
  qexists_tac `v` >> simp[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v, mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `body_exprs_full_ok cx xs` by
    (drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
     strip_tac >> fs[Once body_exprs_full_ok_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `head_v` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP body_inv_no_phi (CONJ inv member))))) >>
  asm_x "head_path"
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_no_wrap inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func s0 fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_no_wrap o
            CONJ path o CONJ no_phi)))) >>
  qpat_x_assum `!svs' sa' shadow_sa' es' s0' G0' tn0'. _ ==> gas_outcome_full _ _ _ _ (eval_exprs cx xs) _ _ _`
    (qspecl_then [`tail_svs`, `sm`, `shadow_sm`, `mid`, `t`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qx_choose_then `hv` (MAP_EVERY assume_tac o CONJUNCTS)) >>
    simp[])) >>
  disch_tac >>
  `!src. bind (eval_exprs cx xs) (\vs. return (v::vs)) src =
     (sum$SUM_MAP (CONS v) I (FST (eval_exprs cx xs src)),
      SND (eval_exprs cx xs src))` by
    (gen_tac >> Cases_on `eval_exprs cx xs src` >>
     rename1 `eval_exprs cx xs src = (rs,ee)` >>
     Cases_on `rs` >> simp[bind_def, return_def, sumTheory.SUM_MAP_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_exprs cx xs) _ _ _`
    (mp_then (Pos last)
       (mp_tac o BETA_RULE o Q.ISPECL
         [`bind (eval_exprs cx xs) (\vs. return ((v:value)::vs))`,
          `sum$SUM_MAP (CONS (v:value)) (I : exception -> exception)`])
       gas_outcome_full_source_map) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[sumTheory.SUM_MAP_def])) >>
  disch_tac >>
  irule positional_post_source_labels >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_exprs cx xs) _) _ _ _`
    (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> simp[sumTheory.SUM_MAP_def] >>
      disch_then (qx_choose_then `orig` strip_assume_tac) >> Cases_on `orig` >>
      gvs[] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  BETA_TAC >> qx_genl_tac [`H`, `out`, `ee`, `G2`, `tn2`, `u`] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `obs` assume_tac)
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `orig` (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `vs` (MAP_EVERY assume_tac o CONJUNCTS))))))) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (`valid_horizon cx st0 H (mid with gas_obs := obs).storage_trace` suffices_by simp[] >>
     qpat_assum `!tail. bind (eval_exprs cx xs) _ _ = _`
       (qspec_then `[]` (mp_then Any mp_tac valid_horizon_frame)) >>
     simp[] >> disch_then irule >> simp[] >> irule storage_trace_frame_bind_all >>
     simp[cj 6 evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `hv` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `?rs. eval_exprs cx xs (mid with gas_obs := obs) =
         (rs,ee with gas_obs := [])` by
    (qpat_assum `!tail. bind (eval_exprs cx xs) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     simp[] >>
     Cases_on `eval_exprs cx xs (mid with gas_obs := obs)` >> simp[]) >>
  strip_tac >>
  `MAP FDOM ee.scopes = MAP FDOM mid.scopes /\
   MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (conj_tac
     >- (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
     drule eval_read_preserves_scopes_dom >> simp[]) >>
  `~copy ==> ~exprs_can_mutate cenv kw_es /\
    ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
    (!tr. get_storage cx ee tr = get_storage cx mid tr)` by
    (strip_tac >>
     `~exprs_can_mutate cenv xs /\ ~exprs_can_mutate cenv kw_es` by
       fs[Abbr `copy`, exprs_can_mutate_append] >>
     `EVERY (\c. FST c = NONE /\
         IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs xs)` by
       (simp[body_exprs_main_calls_every, EVERY_MEM] >> rpt strip_tac >>
        `expr_body_pre cenv cx env e' mid` by metis_tac[] >>
        fs[expr_body_pre_def, body_inv_def, EVERY_MEM] >> metis_tac[]) >>
     drule_all nonmutating_exprs_source_frame >>
     simp[machine_frame_def] >> strip_tac >> gen_tac >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  `!n b sz. local_region cenv mid.scopes t n b sz <=>
             local_region cenv ee.scopes u n b sz` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee sm t u` (irule_at Any) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (`valid_horizon cx st0 H es.storage_trace` suffices_by simp[] >>
     `valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace`
       suffices_by simp[] >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,_)`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[] >> disch_then irule >> simp[] >> irule storage_trace_frame_bind_all >>
     simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
   si.cs_next_var <= sb.cs_next_var /\ si.cs_next_id <= sb.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es ee sa s0 u` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee sm t u` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >> simp[]) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x u = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP u.vs_allocas aid = SOME b)` by
    (conj_tac >> rpt strip_tac
     >- (rename1 `lookup_var x u = SOME w` >>
         `not_fresh_at sm x` by
           (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
         `lookup_var x t = SOME w` by simp[] >> simp[]) >>
     rename1 `FLOOKUP u.vs_allocas aid = SOME b` >>
     `FLOOKUP t.vs_allocas aid = SOME b` by simp[] >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >> simp[]) >>
  (* The suffix changes the physical endpoint, not the head's compiler cuts. *)
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `(?raw. read_result cx raw ee = (INL hv,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
      vv_at cenv cx (lowered_value_type cenv e) sa sm ee raw sv u /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv u) /\
   vv_storage_live H cx sv ee u /\
   (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
     ptr_buf_ok cenv e op G2 u) /\
   (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G2 u) /\
   (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand (vv_operand sv) u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
         val_in_memory rt hv (w2n w) mem))` by
    (namedCases_on `sv` ["tag op", "tag p"] >>
     simp[vv_location_def, Excl "vv_storage_live_def"]
     >- (simp[vv_storage_live_def] >> irule extcall_request_saved_stack_endpoint >>
         simp[ci_mono_refl, vv_operand_def] >>
         qexistsl_tac [`G1`,`func`,`lo`,`mid`,`sm`,`t`,`tn1`] >>
         Cases_on `is_word_type (lowered_value_type cenv e)` >> simp[] >>
         `~copy` by
           (CCONTR_TAC >> qpat_assum `copy /\ _ ==> _` mp_tac >>
            simp[vv_location_def]) >>
         disj2_tac >> qexistsl_tac [`env`,`H`,`H`,`ctx`] >> simp[]) >>
     `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by
       (qpat_assum `(?tag' op0. LocatedValue tag p = StackValue tag' op0) \/ _`
          mp_tac >> simp[NoAsms] >> strip_tac >> simp[]) >>
     qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
     Cases_on `p.ptr_location = LocMemory`
     >- (Cases_on `copy`
         >- (qpat_assum `T /\ _ ==> ?p w tv. _` (mp_tac o SRULE []) >>
             disch_then (qx_choosel_then [`x`,`w`,`tv`] strip_assume_tac) >>
             `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
                lowered_value_type cenv e` by
               (qpat_assum `compile_snapshot_vv cenv T _ si = _` mp_tac >>
                simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
                pairarg_tac >> simp[] >> rpt strip_tac >> gvs[]) >>
             `ptr_val_ok cx (lowered_value_type cenv e) hv (Var x) G1 tn1 t /\
              val_in_memory tv hv (w2n w) t.vs_memory` by
               (qpat_assum `?raw. read_result cx raw mid = (INL hv,mid) /\ _`
                  (qx_choose_then `raw0` strip_assume_tac) >>
                gvs[vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def, vv_operand_def]) >>
             `w2n w + type_memory_size tv <= t.vs_alloca_next` by
               (irule allocaSiteResourceTheory.alloca_site_registered_below >> conj_tac
                >- metis_tac[stmt_state_rel_local_ptrs_alloca] >>
                qexists_tac `si.cs_next_id` >> simp[]) >>
             mp_tac (Q.INST [`cenv` |-> `cenv`, `e` |-> `e`, `cut` |-> `sm`,
                `a` |-> `si`, `si` |-> `sa`, `ss` |-> `sm`,
                `mid` |-> `mid`, `ee` |-> `ee`, `t` |-> `t`, `u` |-> `u`,
                `G1` |-> `G1`, `G2` |-> `G2`, `tn1` |-> `tn1`, `tn2` |-> `tn2`,
                `input` |-> `ext_call_arg_value (lowered_value_type cenv e) vv`,
                `saved` |-> `LocatedValue (lowered_value_type cenv e) p`,
                `x` |-> `x`, `w` |-> `w`, `tv` |-> `tv`, `aid` |-> `si.cs_next_id`,
                `sz` |-> `type_memory_size tv`, `lo` |-> `lo`, `cx` |-> `cx`,
                `v` |-> `hv`] extcall_request_materialized_endpoint) >>
             simp[exprSimPropsTheory.val_footprint_le, vv_operand_def,
                  loweringStateRelDefsTheory.regions_disjoint_def] >>
             disch_then (fn th => qexists_tac `Value hv` >> mp_tac th) >> simp[]) >>
         simp[] >> irule extcall_request_saved_memory_endpoint >>
         qexistsl_tac [`G1`,`func`,`lo`,`mid`,`sm`,`t`,`tn1`] >>
         simp[ci_mono_refl, vv_operand_def] >>
         disj2_tac >> qexistsl_tac [`env`,`H`,`H`,`ctx`] >> simp[]) >>
     `~copy` by
       (strip_tac >> qpat_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
        simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
        pairarg_tac >> simp[mk_ptr_def] >> strip_tac >> gvs[]) >>
     Cases_on `?tr. p.ptr_location = slot_loc tr`
     >- (qpat_x_assum `?tr. p.ptr_location = slot_loc tr` (qx_choose_then `tr` assume_tac) >>
         `p.ptr_location <> LocCode` by (Cases_on `tr` >> fs[slot_loc_def]) >>
         simp[Excl "vv_storage_live_def"] >> irule extcall_request_saved_slot_endpoint >>
         simp[Excl "vv_storage_live_def"] >> conj_tac
         >- (qexistsl_tac [`ctx`,`func`] >> simp[]) >>
         qexistsl_tac [`DF H`,`G1`,`d`,`lo`,`mid`,`sm`,`t`,`tn1`,`tr`] >>
         simp[vv_operand_def, Excl "vv_storage_live_def"] >>
         qpat_assum `?raw. read_result cx raw mid = (INL hv,mid) /\ _`
           (qx_choose_then `raw0` strip_assume_tac) >>
         qexists_tac `raw0` >> simp[]) >>
     Cases_on `p.ptr_location = LocCode`
     >- (simp[vv_operand_def] >> conj_asm1_tac
         >- (irule (cj 1 extcall_request_saved_code_endpoint) >> simp[] >>
             qexistsl_tac [`G1`,`lo`,`mid`,`sm`,`t`,`tn1`] >> simp[vv_operand_def] >>
             qpat_assum `?raw. read_result cx raw mid = (INL hv,mid) /\ _`
               (qx_choose_then `raw0` strip_assume_tac) >>
             qexists_tac `raw0` >> simp[]) >>
         disch_tac >>
         `!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
           eval_operand p.ptr_operand u = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
             val_in_memory rt hv (w2n w) mem)`
           suffices_by simp[arithmeticTheory.ADD_COMM] >>
         MATCH_MP_TAC (Q.INST [`H` |-> `H`, `D` |-> `DF H`, `G` |-> `G2`,
                               `entry` |-> `mid`, `env` |-> `env`, `d` |-> `d`,
                               `ctx` |-> `ctx`, `func` |-> `func`, `tops` |-> `tops`]
           (INST_TYPE [alpha |-> ``:256``] extcall_request_saved_ctor_read)) >>
         simp[] >>
         qpat_assum `?raw. read_result cx raw ee = (INL hv,ee) /\ _`
           (qx_choose_then `raw0` strip_assume_tac) >>
         qexists_tac `raw0` >> simp[]) >>
     `p.ptr_location <> LocStorage /\ p.ptr_location <> LocTransient` by
       (qpat_assum `~(?tr. p.ptr_location = slot_loc tr)`
          (fn th => let val no_slot = CONV_RULE NOT_EXISTS_CONV th in
             mp_tac (Q.SPEC `T` no_slot) >> mp_tac (Q.SPEC `F` no_slot) end) >>
        simp[slot_loc_def]) >>
     `p.ptr_location = LocCalldata` by
       (qpat_assum `p.ptr_location <> LocMemory` mp_tac >>
        qpat_assum `p.ptr_location <> LocCode` mp_tac >>
        qpat_assum `p.ptr_location <> LocStorage` mp_tac >>
        qpat_assum `p.ptr_location <> LocTransient` mp_tac >>
        Cases_on `p.ptr_location` >> simp[NoAsms]) >>
     qpat_x_assum `?raw. read_result cx raw mid = (INL hv,mid) /\ _`
       (qx_choose_then `raw0` strip_assume_tac) >>
     qpat_x_assum `vv_holds _ _ _ raw0 _ mid t`
       (mp_tac o REWRITE_RULE [vv_holds_def]) >> simp[]) >>
  `hv = v` by (qpat_assum `INL v = INL hv` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qunabbrev_tac `snap` >>
  qexists_tac `v::vs` >>
  simp[sumTheory.SUM_MAP_def, ZIP, arithmeticTheory.ADD_COMM] >>
  reverse (rpt conj_tac)
  >- (irule LIST_REL_mono >>
      qpat_assum `LIST_REL _ (ZIP (xs,tail_svs)) vs` (irule_at Any) >>
      Cases >> simp[] >> rpt gen_tac >>
      disch_then (CONJUNCTS_THEN2
        (qx_choosel_then [`se`,`sx`,`ss`,`evv`,`rawi`,`cp`] (MAP_EVERY assume_tac o CONJUNCTS))
        (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qexistsl_tac [`se`,`sx`,`ss`,`evv`,`rawi`,`cp`] >> simp[])
  >~ [`cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==> _`]
  >- (pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      qpat_assum `cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. _ /\ eval_operand (vv_operand sv) u = SOME w ==> _ /\ _`
        (ACCEPT_TAC o cj 1)) >>
  qmatch_asmsub_rename_tac
    `vv_at cenv cx (lowered_value_type cenv e) sa sm ee rawh sv u` >>
  qexistsl_tac [`sa`,`si`,`sm`,`vv`,`rawh`,`copy`] >> simp[] >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `copy /\ _ ==> ?p w tv. _` mp_tac >>
      impl_tac >- simp[] >>
      disch_then (qx_choosel_then [`p`,`w`,`tv`] strip_assume_tac) >>
      qexistsl_tac [`p`,`w`,`tv`] >>
      fs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  qpat_assum `(?tag op0. sv = StackValue tag op0) \/ _` strip_assume_tac >>
  simp[] >>
  `sv = vv` by
    (qpat_assum `compile_expr cenv (expr_type e) e sa = (sv,sm)` mp_tac >>
     qpat_assum `compile_expr cenv (expr_type e) e sa = (vv,si)`
       (fn th => simp[NoAsms, th])) >>
  gvs[]
QED
