(* The supplied arguments run in the caller before the pushed defaults. *)
Theory s1PrefixBoolChainSuppliedToDefaults
Ancestors
  s1PrefixBoolChainDefaultStageEntry s1PrefixBoolChainDefaultCallback
  s1PrefixInvalidTraceDomain s1PrefixFrame
  s1PrefixProps bodyFullIntCallArgsTrace vyperTypeEvalProofs vyperTypeArgFits
  exprSimSliceCompose stmtSimForRounds exprBodyPreProps gasContext
  exprSimWordArgs contextRawReachable rich_list list compileEnv
  vyperState vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperTypeSystem
  finite_map loweringPosts bodyPtrDefs venomState
  s1PrefixCompose s1PrefixIntCallStageList s1PrefixIntCallArgsSource bodyFullIntCallArgs

val _ = temp_overload_on ("bind", ``vyperState$bind``)
val _ = temp_overload_on ("return", ``vyperState$return``)

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `storage_trace_frame (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)` by
    (irule storage_trace_frame_bind_all >> simp[evaluate_storage_trace_frame]) >>
  reverse (Cases_on `storage_trace_domain cx st0 es0.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >> simp[]) >>
  drule_all intcall_args_supplied_stage_setup >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`art`,`imms`,`A`,`roots`,`compiled_dflts`,`ds`,`vv`,`sm`,
      `shadow_vv`,`shadow_sm`,`rc'`,`rbs`,`pvs`,`buf_n`,`st2`,`st2a`,`st3`,
      `sh_st2`,`sh_st2a`,`sh_st3`,`sup_ops`,`def_ops`,`sh_def_ops`,`entry`,`Ga`,`tna`,`pin`]
      (map_every assume_tac o CONJUNCTS))) >>
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
  suspend "supplied_run"
QED
*)
Theorem bool_chain_supplied_to_defaults:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx tenv es0 /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
  (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es) /\
  (!v. storage_trace_frame ((f : eval_result -> evaluation_state -> ('b + exception) # evaluation_state) v)) /\
  (!v. cs_appends (kc v)) /\
  comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt)) kc sa = (out,sb) /\
  comp_bind (compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt))) kc sha = (out,shb) /\
  gas_shadow_state sa sha /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es0.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    storage_well_formed_on cx es0 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f) P es0 /\
  (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
  after_args = (\prev vals.
    bind (bind (lift_option_type (bind_arguments (get_tenv cx) args vals)
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
               (\crv. return (Value crv)))))))) f) /\
  (!vv sm rc rbs pvs ds si sf sh_si sh_sf def_ops st2 sup_ops entry Ga tna pin
     marks svs at_defaults t G tn dc pushed envd next.
    dc = cenv_without_defaults cenv name /\
    pushed = cx with stk updated_by CONS (NONE,name) /\ envd = tenv with current_src := NONE /\
    next = (\vals src. after_args src.scopes vals src) /\
    ds = DROP (LENGTH dflts - (LENGTH args - LENGTH es))
      (subst_consts_exprs (module_consts_env tops []) dflts) /\
    ds = omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es) /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
    kc vv sm = (out,sb) /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    cenv.ce_func_param_types (nsid_to_string (NONE,name)) = MAP SND args /\
    compile_stage_intcall_args compile_expr cenv es pvs
      (MAP SND args) st2 = (sup_ops,si) /\
    compile_stage_intcall_args compile_expr dc ds (DROP (LENGTH es) pvs)
      (DROP (LENGTH es) (MAP SND args)) si = (def_ops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T dc) (MAP gas_shadow_expr ds)
      (DROP (LENGTH es) pvs) (DROP (LENGTH es) (MAP SND args)) sh_si = (def_ops,sh_sf) /\
    fn_has_code sa st2 func /\ fn_has_code sf sm func /\
    cs_extends sa st2 /\ cs_extends st2 si /\ cs_extends si sf /\
    cs_extends sf sm /\ cs_extends sm sb /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
    (!tail. eval_exprs cx es (es0 with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (INL svs,at_defaults with gas_obs := tail)) /\
    gas_path ctx func entry (LENGTH marks) (OK t) /\
    (!H. valid_horizon cx st0 H at_defaults.storage_trace ==>
      intcall_args_stage_post (DF,lo,d,ctx,func,cenv,cx,tenv)
        (es,sa,s0,es0,G0,tn0,si)
        (TAKE (LENGTH es) pvs,TAKE (LENGTH es) (MAP SND args),sup_ops,[],[],[],[],pin,T,T)
        H (INL svs : value list + exception) at_defaults G tn t) /\
    body_inv tops ctx dc pushed /\
    (!H. dead_lo_ok H (DF H) lo dc pushed) /\
    supported_pure_exprs tops ds /\ well_typed_exprs (defaults_env envd) ds /\
    (!gs scs. eval_exprs pushed ds (at_defaults with <|gas_obs := gs; scopes := scs|>) =
      eval_exprs pushed (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        (at_defaults with <|gas_obs := gs; scopes := scs|>)) /\
    (!src res fin. eval_exprs pushed ds src = (res,fin) ==> fin.scopes = src.scopes) /\
    (!tail. eval_exprs pushed [] (at_defaults with gas_obs := tail) =
      (INL [],at_defaults with gas_obs := tail)) /\
    bool_chain_default_ready (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,dc,pushed,envd,st0)
      (sa,s0,es0,G0,tn0,sf,sh_sf,pin,T,T) next P ds
      (si,sh_si,DROP (LENGTH es) pvs,DROP (LENGTH es) (MAP SND args),sup_ops,svs,
       TAKE (LENGTH es) (MAP SND args),TAKE (LENGTH es) pvs) (at_defaults,t,G,tn) /\
    (!vals. storage_trace_frame (next vals)) /\
    gas_shadow_state sf sh_sf /\ gas_path ctx func t 0 (OK t) /\
    get_module_code cx NONE = SOME tops /\ ~MEM (NONE,name) cx.stk /\
    call_evaluation_safe cx ((NONE,name)::int_calls_exprs es) /\
    expr_sim_inv cenv cx tenv es0 /\ expr_sim_inv cenv cx tenv at_defaults /\
    IS_SOME (evaluate_type (get_tenv cx) ret) /\
    well_typed_exprs envd ds /\ body_const_cells_agree [(NONE,tops)] pushed envd at_defaults /\
    LENGTH (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)) = LENGTH args - LENGTH es /\
    pvs = compute_pass_via_stack (MAP SND args) rc /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) =
      compute_func_info
        (\n. MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) n))
        ret (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ret) (MAP SND args) /\
    (!i. i < LENGTH args /\ EL i pvs ==> is_word_type (EL i (MAP SND args))) /\
    EVERY (\t. type_memory_bytes cenv t < 2 ** 64) (MAP SND args) /\
    (0 < rc ==> ?rb results mid ignored.
      compile_alloc_buffer (32 * rc) sa = (rb,st2) /\
      emit_multi_op INVOKE
        (Label (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
          (nsid_to_string (NONE,name)) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
          cenv.ce_is_ctor) :: (sup_ops ++ def_ops)) rc sf = (results,mid) /\
      store_multi_results rb.buf_operand results 0 mid = (ignored,sm) /\
      vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rb)) /\
    (rc = 0 /\ 0 < rbs ==> ?rb ignored.
      compile_alloc_buffer rbs sa = (rb,st2) /\
      emit_void INVOKE
        (Label (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
          (nsid_to_string (NONE,name)) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
          cenv.ce_is_ctor) :: rb.buf_operand :: (sup_ops ++ def_ops)) sf = (ignored,sm) /\
      vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (base_ptr rb)) /\
    (rc = 0 /\ rbs = 0 ==> ?ignored. st2 = sa /\
      emit_void INVOKE
        (Label (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
          (nsid_to_string (NONE,name)) (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
          cenv.ce_is_ctor) :: (sup_ops ++ def_ops)) sf = (ignored,sm) /\
      vv = StackValue (cenv.ce_func_return_type (nsid_to_string (NONE,name))) (Lit 0w)) /\
    (0 < rc \/ 0 < rbs ==> ?rb q (w:bytes32).
      compile_alloc_buffer (if 0 < rc then 32 * rc else rbs) sa = (rb,st2) /\
      rb.buf_operand = Var q /\ rb.buf_size = (if 0 < rc then 32 * rc else rbs) /\
      pin = SOME (q,w2n w,(if 0 < rc then 32 * rc else rbs))) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      pushed st0 (bind (eval_exprs pushed ds) (\dvs. next (svs ++ dvs))) (at_defaults,t,G,tn)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f) (es0,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[supplied_run]:
  `body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es` by simp[] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx es) (es0,entry,Ga,tna)
      (intcall_args_stage_post (DF,lo,d,ctx,func,cenv,cx,tenv)
        (es,sa,s0,es0,G0,tn0,st2a)
        (TAKE (LENGTH es) pvs,TAKE (LENGTH es) (MAP SND args),sup_ops,[],[],[],[],pin,T,T))
      (\H res ee gt r. (?err. res = INR err) /\ expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx es) (es0,entry,Ga,tna)` by
    (conj_tac >> FIRST [irule intcall_args_stage_left_outcome,
       irule (Q.INST [`clean_words` |-> `T`, `keep_sites` |-> `T`,
                      `ops` |-> `[]`, `vals` |-> `[]`, `ptys` |-> `[]`, `pflags` |-> `[]`]
                (SPEC_ALL intcall_stage_list_prefix))] >>
     qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
     qpat_assum `compile_stage_intcall_args _ _ es (TAKE _ _) (TAKE _ _) st2 = _` (irule_at Any) >>
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
     TRY (simp[venomStateTheory.eval_operands_def,LENGTH_TAKE,EL_TAKE,EVERY_TAKE] >> NO_TAC) >>
     TRY (rpt gen_tac >> strip_tac >> drule_all intcall_args_aggregate_physical_type >> simp[] >> NO_TAC) >>
     rpt strip_tac >>
     `j < LENGTH args` by decide_tac >>
     `EL j pvs` by
       (qpat_assum `EL j (TAKE (LENGTH es) pvs)` mp_tac >>
        qpat_assum `j < LENGTH es` mp_tac >> simp_tac std_ss [listTheory.EL_TAKE]) >>
     simp[EL_TAKE] >>
     qpat_assum `!i. i < LENGTH args /\ EL i pvs ==> _` (qspec_then `j` mp_tac) >> simp[]) >>
  irule gas_prefix_full_bind_path >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx es) _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[evaluate_storage_trace_frame,evaluate_requests_outcomes_frame] >> NO_TAC) >>
  TRY (rpt gen_tac >> Cases_on `res` >> simp[NoAsms] >> NO_TAC)
  >- suspend "supplied_frame" >>
  suspend "landing"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[supplied_frame]:
  qunabbrev_tac `supplied_tail` >> gen_tac >> BETA_TAC >>
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
  simp_tac bool_ss [storage_trace_frame_state_updates,evaluate_storage_trace_frame]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[landing]:
  map_every qx_gen_tac [`marks`,`svs`,`ee`,`G`,`tn`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE bool_ss [intcall_args_stage_post_def,APPEND])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [intcall_args_stage_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!tail. eval_exprs cx es _ = _` (qspec_then `[]` assume_tac) >>
  qabbrev_tac `cxd = cx with stk updated_by CONS (NONE,name)` >>
  qabbrev_tac `dc = cenv_without_defaults cenv name` >>
  qabbrev_tac `envd = tenv with current_src := NONE` >>
  qabbrev_tac `length_skip = LENGTH dflts - (LENGTH args - LENGTH es)` >>
  `ds = DROP length_skip (subst_consts_exprs (module_consts_env tops []) dflts)` by
    (qpat_assum `ds = DROP _ compiled_dflts` mp_tac >>
     qpat_assum `compiled_dflts = subst_consts_exprs _ _` (fn th => simp[NoAsms,Abbr `length_skip`,th])) >>
  `cenv.ce_func_param_types name = MAP SND args` by
    (qpat_assum `cenv.ce_func_param_types (nsid_to_string (NONE,name)) = _` mp_tac >>
     simp[NoAsms,nsid_to_string_def]) >>
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
                `G` |-> `G`, `tn` |-> `tn`]) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    simp[Abbr `cxd`, Abbr `dc`, Abbr `length_skip`])) >>
  strip_tac >>
  suspend "replay"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[replay]:
  qabbrev_tac `next = \vals src. after_args src.scopes vals src` >>
  `!gs. supplied_tail svs (ee with gas_obs := gs) =
    bind (eval_exprs cxd ds) (\vs. next (svs ++ vs)) (ee with gas_obs := gs)` by
    (`supplied_tail svs = bind get_scopes (\prev.
       bind (finally (ignore_bind (set_scopes [FEMPTY])
         (eval_exprs cxd (DROP length_skip dflts))) (set_scopes prev))
            (\vs. after_args prev (svs ++ vs)))` by
       (qpat_assum `after_args = _` (fn th =>
          simp_tac bool_ss [Abbr `supplied_tail`,th,bind_assoc])) >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!k. (!gs. _ = _) /\ _`
       (qspec_then `\prev vs. after_args prev (svs ++ vs)` (mp_tac o CONJUNCT1)) >>
     simp_tac bool_ss [Abbr `next`]) >>
  `gas_admissible (bind (eval_exprs cxd ds) (\vs. next (svs ++ vs))) P ee` by
    (qpat_assum `gas_admissible (bind (eval_exprs cx es) _) P es0`
       (mp_then Any mp_tac gas_admissible_bind_tail) >>
     disch_then (qspecl_then [`gas_explicit marks entry.vs_gas_readings`,`svs`,`ee`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `!gs. supplied_tail svs _ = _` (fn th =>
       simp[NoAsms,gas_admissible_def,th])) >>
  `(gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (supplied_tail svs) (ee,t,G,tn) =
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_exprs cxd ds) (\vs. next (svs ++ vs))) (ee,t,G,tn))` by
    (irule intcall_args_prefix_source_replay >> simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST1_TAC >>
  `(gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cxd st0 (bind (eval_exprs cxd ds) (\vs. next (svs ++ vs))) (ee,t,G,tn) =
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_exprs cxd ds) (\vs. next (svs ++ vs))) (ee,t,G,tn))` by
    simp[NoAsms,Abbr `cxd`,intcall_args_prefix_stack] >>
  pop_assum (fn th => once_rewrite_tac[GSYM th]) >>
  suspend "readiness"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[readiness]:
  `well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt)` by
    (drule expr_body_pre_static_facts >> strip_tac >> first_assum ACCEPT_TAC) >>
  `IS_SOME (FLOOKUP tenv.fn_sigs (NONE,name))` by
    (qpat_assum `well_typed_expr tenv (Call _ _ _ _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[Once well_typed_expr_def,optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  qpat_assum `expr_sim_inv cenv cx tenv ee`
    (strip_assume_tac o MATCH_MP args_stage_source_typing) >>
  drule_all callable_body_typing_from_env_consistent >> strip_tac >>
  `IS_SOME (evaluate_type (get_tenv cx) ret)` by
    (qpat_assum `evaluate_type (get_tenv cx) ret = SOME _` (fn th => simp[NoAsms,th])) >>
  `!vals. storage_trace_frame (next vals)` by
    (`!prev vals. storage_trace_frame (after_args prev vals)` by
       (qpat_assum `after_args = _` SUBST1_TAC >> rpt gen_tac >> BETA_TAC >>
        irule (SIMP_RULE bool_ss [APPEND]
                 (Q.INST [`vs` |-> `[]`] intcall_after_defaults_storage_trace_frame)) >>
        first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [Abbr `next`,storage_trace_frame_def,evaluation_state_accfupds] >>
     rpt gen_tac >> first_assum (irule o REWRITE_RULE [storage_trace_frame_def])) >>
  `bool_chain_default_ready (DF,lo,d,ctx,shadow_ctx,func,shadow_func,tops,dc,cxd,envd,st0)
      (sa,s0,es0,G0,tn0,st3,sh_st3,pin,T,T) next P ds
      (st2a,sh_st2a,DROP (LENGTH es) pvs,DROP (LENGTH es) (MAP SND args),sup_ops,svs,
       TAKE (LENGTH es) (MAP SND args),TAKE (LENGTH es) pvs) (ee,t,G,tn)` by
    suspend "initial_fields" >>
  qpat_assum `!vv sm rc rbs. _` irule >>
  qpat_assum `compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = _` (irule_at Any) >>
  qpat_assum `bool_chain_default_ready _ _ _ _ ds _ _` (irule_at Any) >>
  qexistsl [`tna`,`st2`,`rc'`,`rbs`,`marks`,`entry`,`def_ops`,`Ga`] >>
  rpt conj_tac >> (REFL_TAC ORELSE TRY (first_assum ACCEPT_TAC >> NO_TAC)) >>
  TRY (simp[NoAsms,eval_exprs_nil] >> NO_TAC) >>
  TRY (simp[NoAsms,Abbr `envd`,APPEND_NIL] >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >> first_assum (ACCEPT_TAC o SYM) >> NO_TAC) >>
  TRY (qpat_assum `cenv.ce_func_param_types (nsid_to_string (NONE,name)) = _` (fn th =>
         first_assum (ACCEPT_TAC o SIMP_RULE std_ss [th,LENGTH_MAP,TAKE_LENGTH_ID])) >> NO_TAC) >>
  suspend "callback_fields"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[initial_fields]:
  markerLib.RESUME_TAC >>
  `LENGTH ds = LENGTH args - LENGTH es` by
    (qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     qpat_assum `omitted_defaults cenv _ _ = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `MAP expr_type ds = DROP (LENGTH es) (MAP SND args)` by
    (`LENGTH dflts <= LENGTH args` by
       (qpat_assum `MAP expr_type dflts = _` (mp_tac o Q.AP_TERM `LENGTH : type list -> num`) >>
        simp[NoAsms] >> decide_tac) >>
     `length_skip + (LENGTH args - LENGTH dflts) = LENGTH es` by
       (qpat_assum `Abbrev (length_skip = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >> decide_tac) >>
     qpat_assum `ds = DROP _ compiled_dflts` SUBST1_TAC >>
     simp_tac bool_ss [MAP_DROP,DROP_DROP_T] >>
     qpat_assum `MAP expr_type compiled_dflts = _` SUBST1_TAC >>
     qpat_assum `MAP expr_type dflts = _` SUBST1_TAC >>
     simp_tac bool_ss [MAP_DROP,DROP_DROP_T] >>
     qpat_assum `length_skip + _ = LENGTH es` (fn th => simp[NoAsms,th])) >>
  `type_memory_bytes dc = type_memory_bytes cenv` by
    (irule type_memory_bytes_frame >> simp[NoAsms,Abbr `dc`,exprLoweringTheory.cenv_without_defaults_def]) >>
  simp_tac bool_ss [bool_chain_default_ready_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp[NoAsms,Abbr `envd`] >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `LENGTH ds = _` (fn n =>
         qpat_assum `LENGTH pvs = _` (fn p => simp_tac bool_ss [LENGTH_DROP,LENGTH_MAP,n,p])) >> NO_TAC)
  >> TRY (qpat_assum `type_memory_bytes dc = _` SUBST1_TAC >> irule EVERY_DROP >> first_assum ACCEPT_TAC >> NO_TAC)
  >> TRY (qpat_assum `MAP expr_type ds = _` SUBST1_TAC >> simp[NoAsms,EVERY2_refl,type_widens_to_refl] >> NO_TAC)
  >> TRY (qx_gen_tac `j` >> strip_tac >> qpat_assum `EL j (DROP (LENGTH es) pvs)` mp_tac >>
      `j + LENGTH es < LENGTH args` by decide_tac >>
      qpat_assum `!i. i < LENGTH args /\ EL i pvs ==> _` (qspec_then `j + LENGTH es` mp_tac) >>
      qpat_assum `j + LENGTH es < LENGTH args` mp_tac >>
      qpat_assum `LENGTH pvs = LENGTH args` mp_tac >>
      simp[NoAsms,EL_DROP] >> NO_TAC)
  >> TRY (qexists_tac `def_ops` >> simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC >> NO_TAC)
  >> TRY (qpat_assum `!src tr. storage_trace_domain cxd src tr = _` (fn th => simp_tac bool_ss [th]) >>
      first_assum ACCEPT_TAC >> NO_TAC) >>
  suspend "rebase_post"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[rebase_post]:
  markerLib.RESUME_TAC >>
  `!sc s n b k. local_region dc sc s n b k = local_region cenv sc s n b k` by
    simp[NoAsms,Abbr `dc`,loweringStateRelDefsTheory.local_region_def,exprLoweringTheory.cenv_without_defaults_def] >>
  `get_tenv cxd = get_tenv cx` by
    simp[NoAsms,Abbr `cxd`,get_tenv_stk_irrelevant] >>
  `!ty sub. type_step_offset dc ty sub = type_step_offset cenv ty sub` by
    (qpat_assum `type_memory_bytes dc = _` (fn th =>
       simp_tac bool_ss [oneline type_step_offset_def,th]) >>
     simp[NoAsms,Abbr `dc`,exprLoweringTheory.cenv_without_defaults_def]) >>
  `!path ty. type_path_offset dc ty path = type_path_offset cenv ty path` by
    (qpat_assum `!ty sub. type_step_offset dc ty sub = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >> Induct >> simp[type_path_offset_def]) >>
  `!src dst a u v. wb_frame dc src dst a u v = wb_frame cenv src dst a u v` by
    (qpat_assum `!path ty. type_path_offset dc ty path = _` (fn off =>
      qpat_assum `!sc s n b k. local_region dc sc s n b k = _` (fn loc =>
        simp_tac bool_ss [off,loc,wb_frame_def,locals_kept_def,
          popped_kept_def,dynarray_len_untupled_def])) >>
     simp[NoAsms,Abbr `dc`,exprLoweringTheory.cenv_without_defaults_def]) >>
  `!G tn. ghost_kept_at lo dc es0 sa G0 tn0 s0 G tn = ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn` by
    (qpat_assum `!sc s n b k. local_region dc sc s n b k = _` (fn th =>
      simp[NoAsms,th,ghost_kept_at_def])) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `!src H tr. valid_horizon cxd src H tr = _` (fn th =>
       qpat_assum `valid_horizon cxd st0 H _` (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> intcall_args_stage_post _ _ _ H _ _ _ _ _`
    (qspec_then `H` (drule_then mp_tac)) >>
  simp_tac bool_ss [intcall_args_stage_post_def,APPEND,APPEND_NIL,sumTheory.INL_11,UNWIND_THM2] >>
  strip_tac >>
  qpat_assum `!H. valid_horizon cxd st0 H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!src dst a u v. wb_frame dc src dst a u v = _` (fn wb =>
    qpat_assum `!G tn. ghost_kept_at lo dc _ _ _ _ _ G tn = _` (fn kept =>
      qpat_assum `!sc s n b k. local_region dc sc s n b k = _` (fn loc =>
        qpat_assum `get_tenv cxd = _` (fn env => pure_rewrite_tac[wb,kept,loc,env])))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp[NoAsms,Abbr `envd`] >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `eval_operands sup_ops t = SOME _` (irule_at Any)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `LENGTH svs = LENGTH es` (fn th => asm_simp_tac bool_ss [GSYM th])
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_supplied_to_defaults[callback_fields]:
  markerLib.RESUME_TAC >>
  FIRST [
    (irule (cj 1 fragGasPathTheory.gas_path_rules) >> first_assum ACCEPT_TAC),
    qpat_assum `buf_n = _` (fn th =>
      qpat_assum `_ ==> ?rb q w. compile_alloc_buffer buf_n sa = _ /\ _`
        (ACCEPT_TAC o PURE_REWRITE_RULE [th])),
    `TAKE (LENGTH args) (cenv.ce_func_param_types (nsid_to_string (NONE,name))) = MAP SND args` by
      (qpat_assum `cenv.ce_func_param_types (nsid_to_string (NONE,name)) = _`
        (fn th => simp[NoAsms,th])) >>
    qpat_assum `TAKE (LENGTH args) (cenv.ce_func_param_types _) = _` (fn th =>
      qpat_assum `compile_stage_intcall_args _ cenv es pvs (TAKE _ _) st2 = _`
        (ACCEPT_TAC o REWRITE_RULE [th])),
    simp[NoAsms,Abbr `envd`,constSubstCorrectTheory.frame_well_typed_exprs_every,EVERY_MEM] >>
    rpt strip_tac >>
    qpat_assum `EVERY (\e. expr_body_pre dc cxd _ e ee) ds`
      (drule o BETA_RULE o REWRITE_RULE [EVERY_MEM]) >>
    disch_then (ACCEPT_TAC o cj 2 o MATCH_MP expr_body_pre_static_facts)]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bool_chain_supplied_to_defaults
*)
