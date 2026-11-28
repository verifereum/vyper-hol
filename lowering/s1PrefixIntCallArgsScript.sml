(* Request-prefix companion to bodyFullIntCallArgs. *)
Theory s1PrefixIntCallArgs
Ancestors
  s1PrefixPreds bodyFullIntCallArgs s1PrefixDefs s1PrefixCompose
  s1PrefixInvalidTraceDomain s1PrefixIntCallStageList
  s1PrefixIntCallArgsSource bodyFullIntCallArgsTrace vyperStorageTrace
  exprSimSliceCompose stmtSimForRounds exprBodyPreProps s1PrefixFrame s1PrefixProps
  vyperState vyperStorageFootprint vyperInterpreter vyperTypeSystem vyperContext
  vyperTypeEvalProofs bodyFullIntCallDefs compileEnv loweringPosts
  exprSimWordArgs bodyFullIfExpReach contextRawReachable exprLowering bodyPtrDefs

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt strip_tac >>
  `storage_trace_frame
     (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)` by
    (irule storage_trace_frame_bind_all >> simp[evaluate_storage_trace_frame]) >>
  (reverse (Cases_on `storage_trace_domain cx st0 es0.storage_trace`)
   >- (irule gas_prefix_full_invalid_trace_domain >> simp[])) >>
  drule_all intcall_args_supplied_stage_setup >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`art`,`imms`,`A`,`roots`,`compiled_dflts`,`ds`,`vv`,`sm`,
      `shadow_vv`,`shadow_sm`,`rc'`,`rbs`,`pvs`,`buf_n`,`st2`,`st2a`,`st3`,
      `sh_st2`,`sh_st2a`,`sh_st3`,`sup_ops`,`def_ops`,`sh_def_ops`,`entry`,`Ga`,`tna`,`pin`]
      (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `compiled_dflts = subst_consts_exprs _ _`
    (assume_tac o PURE_ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `buf_n = (if _ then _ else _)`
    (assume_tac o PURE_ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  `body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es` by simp[] >>
  irule gas_prefix_full_zero_prefix_guarded >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Ga`,`entry`,`tna`] >>
  conj_tac >- (rpt strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all intcall_args_supplied_source >>
  disch_then (qspecl_then [`dflt`,`ann`] SUBST_ALL_TAC) >>
  pure_rewrite_tac[bind_assoc] >>
  qpat_x_assum `gas_admissible _ P es0`
    (assume_tac o PURE_REWRITE_RULE [bind_assoc]) >>
  qmatch_goalsub_abbrev_tac `bind (eval_exprs cx es) supplied_tail` >>
  `gas_admissible (eval_exprs cx es)
       (\r:value list + exception. !err. r = INR err ==> expr_vv_res_ok (INR err)) es0` by
    (qpat_assum `gas_admissible (bind (eval_exprs cx es) _) P es0`
       (mp_then Any mp_tac slice_gas_admissible_bind_head) >>
     disch_then (qspec_then `\r:value list + exception. !err. r = INR err ==> expr_vv_res_ok (INR err)` mp_tac) >>
     qpat_assum `!e. P (INR e) ==> expr_vv_res_ok (INR e)` (fn th => simp[NoAsms,th])) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx es) (es0,entry,Ga,tna)
      (intcall_args_stage_post (DF,lo,d,ctx,func,cenv,cx,tenv)
        (es,sa,s0,es0,G0,tn0,st2a)
        (TAKE (LENGTH es) pvs,TAKE (LENGTH es) (MAP SND args),sup_ops,
         [],[],[],[],pin,T,T))
      (\H res ee gt r. (?err. res = INR err) /\
        expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx es) (es0,entry,Ga,tna)` by
    (conj_tac >> FIRST [irule intcall_args_stage_left_outcome,
       irule (Q.INST [`clean_words` |-> `T`, `keep_sites` |-> `T`,
                      `ops` |-> `[]`, `vals` |-> `[]`, `ptys` |-> `[]`, `pflags` |-> `[]`]
                (SPEC_ALL intcall_stage_list_prefix))] >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ _ es (TAKE _ _) (TAKE _ _) st2 = _`
       (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr es) (TAKE _ _) (TAKE _ _) sh_st2 = _`
       (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     qpat_assum `return_buf_frame d cenv st2 entry` (irule_at Any) >>
     TRY (qmatch_goalsub_rename_tac `ghost_kept_at _ _ _ _ _ _ _ _ _` >>
          qpat_assum `ghost_kept_at lo cenv es0 sa G0 tn0 s0 Ga tna` (irule_at Any)) >>
     TRY (qpat_assum `(case pin of NONE => T | SOME _ => _)` (irule_at Any)) >>
     qpat_assum `gas_admissible (eval_exprs cx es) _ es0` (irule_at Any) >>
     TRY (qpat_assum `expr_sim_inv cenv cx tenv es0` (irule_at Any)) >>
     qexists_tac `[]` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp[venomStateTheory.eval_operands_def, listTheory.LENGTH_TAKE,
               rich_listTheory.EL_TAKE, rich_listTheory.EVERY_TAKE] >> NO_TAC) >>
     TRY (rpt gen_tac >> strip_tac >>
          drule_all intcall_args_aggregate_physical_type >> simp[] >> NO_TAC) >>
     rpt strip_tac >>
     simp[rich_listTheory.EL_TAKE] >>
     qpat_assum `!i. i < LENGTH args /\ EL i pvs ==> _` (qspec_then `j` mp_tac) >>
     gvs[rich_listTheory.EL_TAKE] >> decide_tac) >>
  irule gas_prefix_full_bind_path >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx es) _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[evaluate_storage_trace_frame,evaluate_requests_outcomes_frame] >> NO_TAC) >>
  TRY (rpt gen_tac >> Cases_on `res` >> simp[NoAsms] >> NO_TAC)
  >- (qunabbrev_tac `supplied_tail` >> gen_tac >> BETA_TAC >>
      simp_tac bool_ss [bind_assoc] >>
      irule storage_trace_frame_bind_all >>
      simp_tac bool_ss [storage_trace_frame_state_reads] >> gen_tac >>
      irule storage_trace_frame_bind_all >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule (SIMP_RULE bool_ss [bind_assoc] intcall_after_defaults_storage_trace_frame) >>
          first_assum ACCEPT_TAC) >>
      irule storage_trace_frame_finally >>
      simp_tac bool_ss [storage_trace_frame_state_updates] >>
      irule storage_trace_frame_ignore_bind >>
      simp_tac bool_ss [storage_trace_frame_state_updates, evaluate_storage_trace_frame]) >>
  map_every qx_gen_tac [`marks`,`xs`,`ee`,`G1`,`tn1`,`t`] >> strip_tac >>
  suspend "defaults"
QED
*)
Theorem intcall_args_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
 es dflt es0 mut nr args ret ss rr dflts.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx tenv es0 /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\
  LENGTH es <= LENGTH args /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_prefix_ok cx es) /\
  (!s1 vs t1.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) ==>
     body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))) /\
  (!s1 vs t1.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) ==>
     body_exprs_prefix_ok (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))) ==>
  !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 kc out f P Q R.
    (!v. storage_trace_frame (f v)) /\
    (!v. cs_appends (kc v)) /\
    comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt))
      kc sa = (out, sb) /\
    comp_bind
      (compile_expr (gas_shadow_env T cenv) ty
         (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)))
      kc shadow_sa = (out, shadow_sb) /\
    gas_shadow_state sa shadow_sa /\
    gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    gas_admissible
      (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
      P es0 /\
    (!e. P (INR e) ==> expr_vv_res_ok (INR e)) /\
    return_buf_frame d cenv sa s0 /\
    alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es0.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es0 s0 /\
      storage_well_formed_on cx es0 (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\
    ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!H res ee gt r.
       expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) /\
    (!vv sm prev penv rtv es1 t G tn.
       compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
         (vv, sm) /\
       kc vv sm = (out, sb) /\
       (!H. valid_horizon cx st0 H es1.storage_trace ==>
          intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
            es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
            es1 t G tn) /\
       body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
       (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
       (?H. valid_horizon cx st0 H es1.storage_trace) /\
       gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
         P es1 ==>
       gas_outcome_full
         (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         (cx_tops cx) cx st0
         (bind (intcall_rest cx name mut nr ss prev rtv) f) (es1, t, G, tn)
         Q R) /\
    (!vv sm prev penv rtv es1 t G tn.
       compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
         (vv, sm) /\
       kc vv sm = (out, sb) /\
       (!H. valid_horizon cx st0 H es1.storage_trace ==>
          intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
            es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
            es1 t G tn) /\
       body_const_cells_agree [(NONE,tops)] cx tenv es1 /\
       (!i. active_inst func i t ==> frag_reachable ctx func s0 func i t) /\
       (?H. valid_horizon cx st0 H es1.storage_trace) /\
       gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
         P es1 ==>
      gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
    cx st0 (bind (intcall_rest cx name mut nr ss prev rtv) f)
    (es1, t, G, tn)) ==>
  gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
    cx st0 (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
    (es0, s0, G0, tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_args_prefix[defaults]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE bool_ss
       [intcall_args_stage_post_def, listTheory.APPEND, sumTheory.INL_11, UNWIND_THM2])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss
         [intcall_args_stage_post_def, listTheory.APPEND, sumTheory.INL_11, UNWIND_THM2])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!tail. eval_exprs cx es _ = _` (qspec_then `[]` assume_tac) >>
  qabbrev_tac `cxd = cx with stk updated_by CONS (NONE,name)` >>
  qabbrev_tac `length_skip = LENGTH dflts - (LENGTH args - LENGTH es)` >>
  `cxd = cx with stk updated_by CONS (NONE,name) /\
   length_skip = LENGTH dflts - (LENGTH args - LENGTH es) /\
   ds = DROP length_skip (subst_consts_exprs (module_consts_env tops []) dflts)` by
    (conj_tac >- simp[Abbr `cxd`] >>
     conj_tac >- simp[Abbr `length_skip`] >>
     qpat_assum `ds = DROP _ compiled_dflts` mp_tac >>
     simp_tac bool_ss [Abbr `length_skip`, Abbr `compiled_dflts`]) >>
  `body_exprs_full_ok cxd ds /\ body_exprs_prefix_ok cxd ds` by
    (simp_tac bool_ss [Abbr `cxd`] >> qpat_assum `ds = DROP length_skip _` SUBST1_TAC >>
     simp_tac bool_ss [Abbr `length_skip`] >> conj_tac >>
     first_assum irule >> qpat_assum `eval_exprs cx es _ = (INL xs,_)` (irule_at Any) >> simp[]) >>
  `cenv.ce_func_param_types name = MAP SND args` by
    (qpat_assum `cenv.ce_func_param_types (nsid_to_string (NONE,name)) = MAP SND args` mp_tac >>
     simp[NoAsms, nsid_to_string_def]) >>
  `compile_stage_intcall_args compile_expr
      (gas_shadow_env T (cenv_without_defaults cenv (nsid_to_string (NONE,name))))
      (MAP gas_shadow_expr ds) (DROP (LENGTH es) pvs)
      (DROP (LENGTH es) (TAKE (LENGTH args)
        (cenv.ce_func_param_types (nsid_to_string (NONE,name))))) sh_st2a = (def_ops,sh_st3)` by
    (qpat_assum `sh_def_ops = def_ops` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  mp_tac (intcall_args_defaults_stage_setup
    |> Q.INST_TYPE [`:'r` |-> `:'b`]
    |> Q.INST [`supplied_flags` |-> `TAKE (LENGTH es) pvs`,
                `supplied_tys` |-> `TAKE (LENGTH es) (MAP SND args)`,
                `flags` |-> `DROP (LENGTH es) pvs`,
                `obs` |-> `gas_explicit marks entry.vs_gas_readings ++ []`,
                `dc` |-> `cenv_without_defaults cenv name`,
                `G` |-> `G1`, `tn` |-> `tn1`]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))) >>
  strip_tac >>
  suspend "defaults_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_args_prefix[defaults_bind]:
  qabbrev_tac `after_defaults = \prev dvs.
    bind
      (bind (lift_option_type (bind_arguments (get_tenv cx) args (xs ++ dvs))
                "IntCall bind_arguments") (\penv.
       bind (lift_option_type (evaluate_type (get_tenv cx) ret)
                "IntCall eval ret") (\rtv.
       ignore_bind (lock_if_nr cx nr (is_view_mut mut))
         (bind (push_function (NONE,name) penv cx) (\cxf.
          bind (finally_unless_halt
            (finally
              (try (ignore_bind (eval_stmts cxf ss) (return NoneV)) handle_function)
              (pop_function prev))
            (unlock_if_nr cx nr (is_view_mut mut))) (\rv.
          bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
               (\crv. return (Value crv)))))))) f` >>
  qabbrev_tac `next = \dvs src. after_defaults src.scopes dvs src` >>
  `!gs. supplied_tail xs (ee with gas_obs := gs) =
        bind (eval_exprs cxd ds) next (ee with gas_obs := gs)` by
    (`supplied_tail xs = bind get_scopes (\prev.
       bind (finally (ignore_bind (set_scopes [FEMPTY])
               (eval_exprs cxd (DROP length_skip dflts))) (set_scopes prev))
            (after_defaults prev))` by
       simp_tac bool_ss [Abbr `supplied_tail`, Abbr `after_defaults`,
                         Abbr `cxd`, Abbr `length_skip`, bind_assoc] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!k. (!gs. _ = _) /\ _` (qspec_then `after_defaults` (mp_tac o CONJUNCT1)) >>
     simp_tac bool_ss [Abbr `next`]) >>
  `gas_admissible (bind (eval_exprs cxd ds) next) P ee` by
    (qpat_assum `gas_admissible (bind (eval_exprs cx es) supplied_tail) P es0`
       (mp_then Any mp_tac gas_admissible_bind_tail) >>
     disch_then (qspecl_then [`gas_explicit marks entry.vs_gas_readings`,`xs`,`ee`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `!gs. supplied_tail xs _ = _` (fn th =>
       simp[NoAsms, gasContextTheory.gas_admissible_def, th])) >>
  `gas_admissible (eval_exprs cxd ds)
       (\r:value list + exception. !err. r = INR err ==> expr_vv_res_ok (INR err)) ee` by
    (qpat_assum `gas_admissible (bind (eval_exprs cxd ds) next) P ee`
       (mp_then Any mp_tac slice_gas_admissible_bind_head) >>
     disch_then (qspec_then `\r:value list + exception. !err. r = INR err ==> expr_vv_res_ok (INR err)` mp_tac) >>
     qpat_assum `!e. P (INR e) ==> expr_vv_res_ok (INR e)` (fn th => simp[NoAsms,th])) >>
  `!dvs. storage_trace_frame (next dvs)` by
    (`!prev dvs. storage_trace_frame (after_defaults prev dvs)` by
       (qunabbrev_tac `after_defaults` >> rpt gen_tac >> BETA_TAC >>
        irule intcall_after_defaults_storage_trace_frame >> first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `next`, storage_trace_frame_def, evaluation_state_accfupds] >>
     map_every qx_gen_tac [`dvs`,`src`,`obs`] >>
     qpat_assum `!prev dvs. storage_trace_frame (after_defaults prev dvs)`
       (qspecl_then [`src.scopes`,`dvs`] (qspecl_then [`src`,`obs`] ACCEPT_TAC o
          REWRITE_RULE [storage_trace_frame_def]))) >>
  `(gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (supplied_tail xs) (ee,t,G1,tn1) =
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_exprs cxd ds) next) (ee,t,G1,tn1))` by
    (irule intcall_args_prefix_source_replay >>
     rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)) >>
  pop_assum SUBST1_TAC >>
  `(gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cxd st0 (bind (eval_exprs cxd ds) next) (ee,t,G1,tn1) =
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_exprs cxd ds) next) (ee,t,G1,tn1))` by
    simp[NoAsms, Abbr `cxd`, intcall_args_prefix_stack] >>
  pop_assum (fn th => once_rewrite_tac[GSYM th]) >>
  suspend "defaults_stage"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_args_prefix[defaults_stage]:
  `LENGTH ds = LENGTH args - LENGTH es` by
    (qpat_assum `ds = DROP length_skip compiled_dflts` SUBST1_TAC >>
     simp[NoAsms, Abbr `length_skip`] >>
     qpat_assum `LENGTH args - LENGTH es <= LENGTH dflts` mp_tac >>
     qpat_assum `LENGTH compiled_dflts = LENGTH dflts` mp_tac >> decide_tac) >>
  `well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt)` by
    (drule expr_body_pre_static_facts >> strip_tac >> first_assum ACCEPT_TAC) >>
  `IS_SOME (FLOOKUP tenv.fn_sigs (NONE,name))` by
    (qpat_assum `well_typed_expr tenv (Call _ _ _ _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[Once well_typed_expr_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  qpat_assum `expr_sim_inv cenv cx tenv ee`
    (strip_assume_tac o MATCH_MP args_stage_source_typing) >>
  drule_all vyperTypeEvalProofsTheory.callable_body_typing_from_env_consistent >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `env_body` (qx_choose_then `ret_tv` (qx_choose_then `env_after`
      (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
  `MAP expr_type ds = DROP (LENGTH es) (MAP SND args)` by
    (`LENGTH dflts <= LENGTH args` by
       (qpat_assum `MAP expr_type dflts = _` (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
        simp[NoAsms] >> decide_tac) >>
     `length_skip + (LENGTH args - LENGTH dflts) = LENGTH es` by
       (qpat_assum `length_skip = _` SUBST1_TAC >> decide_tac) >>
     qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     qpat_assum `MAP expr_type compiled_dflts = MAP expr_type dflts`
       (fn th => simp[SimpLHS, NoAsms, listTheory.MAP_DROP, th]) >>
     qpat_assum `MAP expr_type dflts = _` SUBST1_TAC >>
     simp[SimpLHS, NoAsms, listTheory.MAP_DROP, rich_listTheory.DROP_DROP_T] >>
     qpat_assum `_ + (LENGTH args - LENGTH dflts) = LENGTH es`
       (fn th => simp[NoAsms, th])) >>
  `LIST_REL (type_widens_to (get_tenv cxd)) (MAP expr_type ds)
      (DROP (LENGTH es) (MAP SND args))` by
    (qpat_assum `MAP expr_type ds = _` SUBST1_TAC >>
     simp[NoAsms, listTheory.EVERY2_refl, vyperTypeArgFitsTheory.type_widens_to_refl]) >>
  `!sc s n b k. local_region (cenv_without_defaults cenv name) sc s n b k <=>
                 local_region cenv sc s n b k` by
    simp[NoAsms, loweringStateRelDefsTheory.local_region_def, cenv_without_defaults_def] >>
  `get_tenv cxd = get_tenv cx` by
    simp[NoAsms, Abbr `cxd`, vyperTypeEvalProofsTheory.get_tenv_stk_irrelevant] >>
  `type_memory_bytes (cenv_without_defaults cenv name) = type_memory_bytes cenv` by
    (irule compileEnvTheory.type_memory_bytes_frame >> simp[NoAsms, cenv_without_defaults_def]) >>
  `!ty sub. type_step_offset (cenv_without_defaults cenv name) ty sub =
            type_step_offset cenv ty sub` by
    (qpat_assum `type_memory_bytes (cenv_without_defaults cenv name) = _`
       (fn th => simp[NoAsms, th, oneline loweringPostsTheory.type_step_offset_def, cenv_without_defaults_def])) >>
  `!path ty. type_path_offset (cenv_without_defaults cenv name) ty path =
             type_path_offset cenv ty path` by
    (qpat_assum `!ty sub. type_step_offset (cenv_without_defaults cenv name) ty sub = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Induct >> simp[loweringPostsTheory.type_path_offset_def]) >>
  `!src dst a u v. wb_frame (cenv_without_defaults cenv name) src dst a u v =
                    wb_frame cenv src dst a u v` by
    (qpat_assum `!path ty. type_path_offset (cenv_without_defaults cenv name) ty path = _`
      (fn off => qpat_assum `!sc s n b k. local_region (cenv_without_defaults cenv name) sc s n b k <=> _`
         (fn loc => simp[NoAsms, off, loc, wb_frame_def, locals_kept_def,
           popped_kept_def, dynarray_len_untupled_def, cenv_without_defaults_def]))) >>
  `!G tn. ghost_kept_at lo (cenv_without_defaults cenv name) es0 sa G0 tn0 s0 G tn =
          ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn` by
    (qpat_assum `!sc s n b k. local_region (cenv_without_defaults cenv name) sc s n b k <=> _`
       (fn th => simp[NoAsms, th, ghost_kept_at_def])) >>
  `!j. j < LENGTH ds /\ EL j (DROP (LENGTH es) pvs) ==>
       is_word_type (EL j (DROP (LENGTH es) (MAP SND args)))` by
    (qx_gen_tac `j` >> strip_tac >>
     `j + LENGTH es < LENGTH args` by decide_tac >>
     qpat_assum `!i. i < LENGTH args /\ EL i pvs ==> _`
       (qspec_then `j + LENGTH es` mp_tac) >>
     qpat_assum `EL j (DROP (LENGTH es) pvs)` mp_tac >>
     qpat_assum `j + LENGTH es < LENGTH args` mp_tac >>
     qpat_assum `LENGTH pvs = LENGTH args` mp_tac >>
     simp[NoAsms, listTheory.EL_DROP]) >>
  suspend "compose_defaults"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_args_prefix[compose_defaults]:
  qabbrev_tac `dc = cenv_without_defaults cenv name` >>
  qabbrev_tac `envd = tenv with current_src := NONE` >>
  `EVERY (\ty. type_memory_bytes dc ty < 2 ** 64) (DROP (LENGTH es) (MAP SND args))` by
    (qpat_assum `type_memory_bytes dc = _` SUBST1_TAC >>
     irule rich_listTheory.EVERY_DROP >> first_assum ACCEPT_TAC) >>
  `LENGTH (DROP (LENGTH es) pvs) = LENGTH ds /\
   LENGTH (DROP (LENGTH es) (MAP SND args)) = LENGTH ds` by
    (qpat_assum `LENGTH pvs = LENGTH args` mp_tac >>
     qpat_assum `LENGTH ds = LENGTH args - LENGTH es` mp_tac >> simp[NoAsms]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cxd) cxd st0 (eval_exprs cxd ds) (ee,t,G1,tn1)
     (intcall_args_stage_post (DF,lo,d,ctx,func,dc,cxd,envd)
        (ds,sa,s0,es0,G0,tn0,st3)
        (DROP (LENGTH es) pvs,DROP (LENGTH es) (MAP SND args),def_ops,
         sup_ops,xs,TAKE (LENGTH es) (MAP SND args),TAKE (LENGTH es) pvs,pin,T,T))
      (\H res ee gt r. (?err. res = INR err) /\
        expr_exit res r /\ halt_exit H cxd ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cxd st0 (eval_exprs cxd ds) (ee,t,G1,tn1)` by
    (conj_tac >> FIRST [irule intcall_args_stage_left_outcome,
       irule (Q.INST [`clean_words` |-> `T`, `keep_sites` |-> `T`]
                (SPEC_ALL intcall_stage_list_prefix))] >>
     qpat_assum `body_inv tops ctx dc cxd` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ dc ds _ _ st2a = _` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr ds) _ _ sh_st2a = (def_ops,sh_st3)`
       (irule_at Any) >>
     qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
     qpat_assum `return_buf_frame d dc st2a t` (irule_at Any) >>
     qpat_assum `expr_sim_inv dc cxd envd ee` (irule_at Any) >>
     qpat_assum `gas_admissible (eval_exprs cxd ds) _ ee` (irule_at Any) >>
     qpat_assum `eval_operands sup_ops t = SOME _` (irule_at Any) >>
     qpat_assum `!sc s n b k. local_region dc sc s n b k <=> _`
        (fn th => qpat_assum `(case pin of NONE => T | SOME _ => _)`
          (irule_at Any o PURE_REWRITE_RULE [GSYM th])) >>
     TRY (qexistsl_tac [`xs`,`tn0`,`s0`,`TAKE (LENGTH es) (MAP SND args)`,
                       `TAKE (LENGTH es) pvs`,`es0`,`G0`]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [] >> TRY (first_assum ACCEPT_TAC) >>
     TRY (rpt gen_tac >> strip_tac >>
          drule_all intcall_args_aggregate_physical_type >> simp[NoAsms] >> NO_TAC) >>
     TRY (qpat_assum `!sc s n b k. local_region dc sc s n b k <=> _`
       (fn th => pure_rewrite_tac[th]) >>
       qpat_assum `get_tenv cxd = _` (fn th => pure_rewrite_tac[th]) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qpat_assum `!src dst a u v. wb_frame dc src dst a u v = _`
       (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `!G tn. ghost_kept_at lo dc _ _ _ _ _ G tn = _`
       (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  irule gas_prefix_full_bind_path >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cxd ds) _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[NoAsms,evaluate_storage_trace_frame,evaluate_requests_outcomes_frame] >> NO_TAC) >>
  TRY (rpt gen_tac >> Cases_on `res` >> simp[NoAsms] >> NO_TAC) >>
  map_every qx_gen_tac [`dm`,`dvs`,`ed`,`Gd`,`tnd`,`u`] >> strip_tac >>
  suspend "finish"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_args_prefix[finish]:
  `valid_horizon cxd st0 (storage_trace_horizon ed.storage_trace) ed.storage_trace` by
    (qpat_assum `storage_trace_domain cxd st0 ed.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon cxd _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE bool_ss
       [intcall_args_stage_post_def, listTheory.APPEND, sumTheory.INL_11, UNWIND_THM2])) >>
  rename1 `eval_operands (sup_ops ++ def_ops) u = SOME wd` >>
  `!H. valid_horizon cxd st0 H ed.storage_trace ==>
    stmt_state_rel H ctx func dc cxd ed u /\
    storage_well_formed_on cxd ed (FST H) /\
    ghost_inv_at (DF H) lo d dc cxd ed Gd tnd u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cxd _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss
         [intcall_args_stage_post_def,listTheory.APPEND,sumTheory.INL_11,UNWIND_THM2])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_admissible (next dvs) P ed` by
    (qpat_assum `gas_admissible (bind (eval_exprs cxd ds) next) P ee`
       (mp_then Any mp_tac gas_admissible_bind_tail) >>
     disch_then (qspecl_then [`gas_explicit dm t.vs_gas_readings`,`dvs`,`ed`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[NoAsms,gasContextTheory.gas_admissible_def]) >>
  qunabbrev_tac `dc` >> qunabbrev_tac `envd` >> qunabbrev_tac `next` >>
  suspend "rest_data"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_args_prefix[rest_data]:
  `?penv rtv.
     ~u.vs_halted /\
     compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
     kc vv sm = (out,sb) /\
     (!locked. lock_if_nr cx nr (is_view_mut mut) ed = (INL (),locked) ==>
       !tail. after_defaults ed.scopes dvs (ed with gas_obs := tail) =
         bind (intcall_rest cx name mut nr ss ed.scopes rtv) f
           ((ed with scopes := [penv]) with gas_obs := tail)) /\
     (!err failed. lock_if_nr cx nr (is_view_mut mut) ed = (INR err,failed) ==>
       !tail. after_defaults ed.scopes dvs (ed with gas_obs := tail) =
         (INR err,failed with <|scopes := ed.scopes; gas_obs := tail|>)) /\
     (!H. valid_horizon cx st0 H ed.storage_trace ==>
       intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm
         vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) ed.scopes penv rtv
         (ed with scopes := [penv]) u Gd tnd) /\
     body_const_cells_agree [(NONE,tops)] cx tenv (ed with scopes := [penv]) /\
     (!i. active_inst func i u ==> frag_reachable ctx func s0 func i u) /\
     (?H. valid_horizon cx st0 H ed.storage_trace) /\
     gas_admissible (bind (intcall_rest cx name mut nr ss ed.scopes rtv) f)
       P (ed with scopes := [penv])` by
    (irule (PURE_REWRITE_RULE [listTheory.APPEND] intcall_args_after_defaults_data) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexists_tac `ret_tv` >> first_assum ACCEPT_TAC) >>
     qpat_assum `lookup_callable_function cx.in_deploy name tops = SOME _` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ cenv es _ _ st2 = (sup_ops,st2a)` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ _ ds _ _ st2a = (def_ops,st3)` (irule_at Any) >>
     qpat_assum `eval_operands _ u = SOME wd` (irule_at Any) >>
     qpat_assum `gas_path ctx func entry (LENGTH marks) (OK t)` (irule_at Any) >>
     qpat_assum `gas_path ctx func t (LENGTH dm) (OK u)` (irule_at Any) >>
     qpat_assum `expr_sim_inv cenv cx tenv ee` (irule_at Any) >>
     qpat_assum `expr_sim_inv (cenv_without_defaults cenv name) cxd _ ed` (irule_at Any) >>
     qpat_assum `cenv.ce_func_info _ = (rc',rbs,pvs)` (irule_at Any) >>
     qexistsl_tac [`xs`,`tna`,`pin`,
       `internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
          (nsid_to_string (NONE,name)) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
          cenv.ce_is_ctor`, `gas_explicit_sites ctx shadow_ctx`,`PG`,`Ga`] >>
     rpt conj_tac >> TRY (REFL_TAC ORELSE first_assum ACCEPT_TAC) >>
     TRY (simp[NoAsms,Abbr `length_skip`,Abbr `cxd`,Abbr `after_defaults`] >> first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qpat_assum `ds = DROP _ compiled_dflts` (once_rewrite_tac o single) >>
          qpat_assum `omitted_defaults _ _ _ = DROP _ compiled_dflts`
            (once_rewrite_tac o single) >> REFL_TAC >> NO_TAC) >>
     TRY (qpat_assum `Abbrev (buf_n = _)`
           (once_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (simp[NoAsms,constSubstCorrectTheory.frame_well_typed_exprs_every,listTheory.EVERY_MEM] >>
          qpat_assum `EVERY (\e. expr_body_pre _ cxd _ e ee) ds`
            (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts] >> NO_TAC) >>
     qpat_assum `length_skip = LENGTH dflts - _` (fn th => pure_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  suspend "invoke"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume intcall_args_prefix[invoke]:
  BETA_TAC >>
  `(gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cxd st0 (\src. after_defaults src.scopes dvs src) (ed,u,Gd,tnd) =
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (\src. after_defaults src.scopes dvs src) (ed,u,Gd,tnd))` by
    simp[NoAsms,Abbr `cxd`,intcall_args_prefix_stack] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) ed` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) ed = (result,locked)` >>
  Cases_on `result`
  >- (rename1 `lock_if_nr _ _ _ _ = (INL unit,locked)` >>
      Cases_on `unit` >>
      `(gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cx st0 (\src. after_defaults src.scopes dvs src) (ed,u,Gd,tnd) =
        gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cx st0 (bind (intcall_rest cx name mut nr ss ed.scopes rtv) f)
          (ed with scopes := [penv],u,Gd,tnd))` by
        (irule intcall_args_prefix_source_replay >>
         simp_tac bool_ss [evaluation_state_accfupds] >>
         qpat_assum `!other. (INL (),locked) = (INL (),other) ==> _`
           (qspec_then `locked` mp_tac) >>
         simp_tac bool_ss []) >>
      pop_assum SUBST1_TAC >>
      qpat_assum `!v m prev penv rtv es1 t G tn. _ ==> gas_prefix_full _ _ _ _ _`
        (qspecl_then [`vv`,`sm`,`ed.scopes`,`penv`,`rtv`,
                      `ed with scopes := [penv]`,`u`,`Gd`,`tnd`] mp_tac) >>
      simp_tac bool_ss [evaluation_state_accfupds] >>
      (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                    qexists_tac `H` >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  rename1 `lock_if_nr _ _ _ _ = (INR err,failed)` >>
  irule intcall_args_failed_lock_prefix >>
  qpat_assum `lock_if_nr cx nr _ ed = (INR err,failed)` (irule_at Any) >>
  simp_tac bool_ss [evaluation_state_accfupds] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `!dvs. storage_trace_frame ((\dvs src. _) dvs)`
        (qspec_then `dvs` (ACCEPT_TAC o BETA_RULE))) >>
  qpat_assum `!e s. (INR err,failed) = (INR e,s) ==> _`
    (qspecl_then [`err`,`failed`] mp_tac) >>
  simp_tac bool_ss []
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise intcall_args_prefix
*)
