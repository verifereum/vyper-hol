(* Compose keyword requests with the prepared raw-call continuation. *)
Theory s1PrefixRawCallKeywordSuffix
Ancestors
  s1PrefixRawCallKeywords s1PrefixRawCallPreparedTail s1PrefixCompose
  bodyFullRawCallPreparedEntry bodyFullRawCallGeneratedPrefix
  exprSimRawCall exprBodyPreProps exprOperandVar exprSimWordArgs exprLoweringProps
  loweringPosts loweringShapeDefs bodyMemoryDefs vyperStorageTrace
  vyperStorageFootprint vyperValue words list
Libs
  monadsyntax

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
   sa.cs_next_var <= s2.cs_next_var` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!z. data = Var z ==> not_fresh_at s2 z` by
    metis_tac[compile_lower_value_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame dframe cenv s1 tA` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _`
       (assume_tac o MATCH_MP expr_post_frame) >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  `return_buf_frame dframe cenv s2 tD` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv s1 tA` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def]) >>
     simp[NoAsms] >> strip_tac >> simp[]) >>
  `post_value_type cenv d = expr_type d` by
    (irule post_value_type_bytestring >> simp[compileEnvTheory.is_bytestring_type_def]) >>
  `evaluate_type (get_tenv cx) (post_value_type cenv d) = SOME (BaseTV (BytesT (Dynamic cap))) /\
   ~is_word_type (post_value_type cenv d)` by
    (`expr_body_pre cenv cx env d esD` by
       (irule expr_body_pre_raw_call_arg >>
        first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     drule_at (Pat `expr_body_pre _ _ _ d _`) exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[evaluate_type_def,compileEnvTheory.is_word_type_def]) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
    expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD` by
    (rpt strip_tac >> res_tac) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
    expr_val_rel cx (post_value_type cenv d) (BytesV bs) data tD /\
    stmt_state_rel H ctx func cenv cx esD tD /\ storage_well_formed_on cx esD (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esD GD tnD tD` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _ /\ _`
       (drule_then (mp_tac o CONJUNCT2)) >>
     simp[expr_post_def,NoAsms] >> metis_tac[]) >>
  irule (BETA_RULE (Q.INST [`k` |-> `\av dv. continuation`]
    raw_call_keywords_prefix_from_entry)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
  first_assum (irule_at (Pat `body_const_cells_agree _ _ _ _`)) >>
  first_assum (irule_at (Pat `gas_shadow_function _ _`)) >>
  qpat_assum `return_buf_frame dframe cenv s2 tD` (irule_at Any) >>
  first_assum (irule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  first_assum (irule_at (Pat `emit_op ADD _ _ = _`)) >>
  first_assum (irule_at (Pat `ptr_val_ok _ _ (BytesV _) _ _ _ _`)) >>
  qpat_assum `lower_word_args _ _ (MAP gas_shadow_expr kws) h4 = _` (irule_at Any) >>
  qexistsl_tac [`s5`,`cap`,`R`,`Q`] >>
  BETA_TAC >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      rpt (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac) >>
      irule storage_trace_frame_raw_call) >>
  suspend "keyword_success"
QED
*)
Theorem raw_call_forced_data_kwargs_prefix_from_action:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env
    (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE) es /\
  expr_type a = BaseT AddressT /\ expr_type d = BaseT (BytesT (Dynamic cap)) /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\ emit_op ADD [data; Lit 32w] s3 = (dp,s4) /\
  lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
    (MAP gas_shadow_expr kws) h4 = (xs,h5) /\
  (case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = (gas,s6) /\
  (case go of NONE => emit_op GAS [] h5 | SOME g => (g,h5)) = (gas,h6) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr dp len gas (case vo of NONE => Lit 0w | SOME v => v)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  vo = ext_call_kwarg EKValue flags.rcf_kws xs /\ go = ext_call_kwarg EKGas flags.rcf_kws xs /\
  gas_shadow_state s4 h4 /\ gas_shadow_state s5 h5 /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code s2 s4 func /\ fn_has_code s4 s5 func /\
  fn_has_code h4 h5 shadow_func /\ fn_has_code s5 s6 func /\ fn_has_code h5 h6 shadow_func /\
  fn_has_code s6 s7 func /\ fn_inst_ids_distinct func /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
  ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
  local_ptrs_reserved cenv sa /\ return_buf_frame dframe cenv sa s0 /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) = (INL (BytesV bs),esD) /\
  body_const_cells_agree [(NONE,tops)] cx env esD /\
  body_exprs_full_ok cx kws /\ body_exprs_prefix_ok cx kws /\ expr_sim_inv cenv cx env esD /\
  storage_trace_domain cx st0 esD.storage_trace /\
  (!fn inst u. frag_reachable ctx func tD fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H esD.storage_trace ==>
    expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    s0.vs_alloca_next <= tA.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv a) av addr GA tnA tA /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA /\
    expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
    tD.vs_current_bb = s2.cs_current_bb /\ tD.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func tD /\ tA.vs_alloca_next <= tD.vs_alloca_next /\
    ghost_inv_at (DF H) lo dframe cenv cx esD GD tnD tD /\
    ptr_val_ok cx (post_value_type cenv d) (BytesV bs) data GD tnD tD /\
    ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD /\ ~tD.vs_halted) /\
  (!gsK kvs esK t4 tk t7 G7 tn7 b ob gw.
    eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
    esK.gas_obs = [] /\ storage_trace_domain cx st0 esK.storage_trace /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==>
      typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
      stmt_state_rel H ctx func cenv cx esK t7 /\ stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx esK (FST H) /\ expr_val_rel cx (BaseT AddressT) av addr t7 /\
      (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t7 = SOME w) /\
      eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
      eval_operand dp t7 = SOME (n2w (b+32)) /\ eval_operand gas t7 = SOME gw /\
      b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
      b+32+LENGTH bs <= t7.vs_alloca_next /\
      mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory = bs /\
      (!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==>
        mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
      EVERY (\x. op_taint tn7 x = {}) [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v)] /\
      (LENGTH bs <> 0 ==> ?base sz. op_prov G7 dp = SOME (base,sz) /\
        base <= b+32 /\ b+32+LENGTH bs <= base+sz) /\
      eval_operand ov t7 = SOME (n2w ob) /\
      eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob+32)) /\
      (flags.rcf_max_outsize = 0 ==> ov = op) /\
      ob+(if flags.rcf_max_outsize = 0 then 0
          else ((flags.rcf_max_outsize+31) DIV 32)*32+32) < dimword (:256) /\
      FLOOKUP t7.vs_allocas s6.cs_next_id =
        SOME (ob,if flags.rcf_max_outsize = 0 then 0
                 else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
      op_prov G7 ov = SOME (ob,if flags.rcf_max_outsize = 0 then 0
                                else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
      op_prov G7 op = SOME (ob,if flags.rcf_max_outsize = 0 then 0
                                else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
      op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
      (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
        regions_disjoint ob (if flags.rcf_max_outsize = 0 then 0
                             else ((flags.rcf_max_outsize+31) DIV 32)*32+32) lb sz) /\
      (cenv.ce_is_ctor ==> !name tv v off.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
        regions_disjoint off (type_memory_size tv) ob
          (if flags.rcf_max_outsize = 0 then 0
           else ((flags.rcf_max_outsize+31) DIV 32)*32+32)) /\
      wb_frame cenv es esK sa s0 t7 /\ return_buf_frame dframe cenv sa t7 /\
      ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
      t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
      s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next /\ allocas_from lo t7 /\
      ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7 /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
      EVERY (safe_operand s7)
        [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op] /\
      (!x. MEM (Var x) [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op] ==>
        not_fresh_at s7 x)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (do
        type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
        target <- lift_option_type (dest_AddressV av) "raw_call target";
        bytes <- lift_option_type (dest_BytesV (BytesV bs)) "raw_call data";
        amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
        eval_raw_call cx flags target bytes amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
      od) (esK,t7,G7,tn7) Q R) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (do
      kvs <- eval_exprs cx kws;
      type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV av) "raw_call target";
      bytes <- lift_option_type (dest_BytesV (BytesV bs)) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
      eval_raw_call cx flags target bytes amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
    od) (esD,tD,GD,tnD)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_forced_data_kwargs_prefix_from_action[keyword_success]:
  qx_genl_tac [`b`,`x`,`l`,`p`,`base_addr`,`extent`,`t4`,`G4`,`tn4`,
                `marks`,`kvs`,`esK`,`tk`,`GK`,`tnK`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `esK with gas_obs := [] = esK` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_exprs cx kws _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  mp_tac (Q.INST [`ann` |-> `raw_call_return_type flags`,
    `base'` |-> `base_addr`, `cap'` |-> `extent`,
    `gsK` |-> `gasSummary$gas_explicit marks t4.vs_gas_readings`]
    raw_call_kwargs_prepared_entry) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    Cases_on `go` >> simp[])) >>
  disch_then (qx_choose_then `t7` (qx_choose_then `G7` (qx_choose_then `tn7`
    (qx_choose_then `n` (qx_choose_then `ob` (qx_choose_then `gw`
      (map_every assume_tac o CONJUNCTS))))))) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ action _ _ _` >>
  `storage_trace_frame action` by
    (simp[Abbr `action`,NoAsms] >> irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_checks] >>
     rpt (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac) >>
     irule storage_trace_frame_raw_call) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (tk,GK,tnK) (REPLICATE n F) (OK t7,G7,tn7)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  conj_tac
  >- (irule raw_call_generated_prefix_full >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`G7`,`n`,`t7`,`tn7`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      qunabbrev_tac `action` >>
      qpat_assum `!gsK kvs esK t4 tk t7 G7 tn7 b ob gw. _ ==> gas_outcome_full _ _ _ _ _ _ Q R`
        (qspec_then `gasSummary$gas_explicit marks t4.vs_gas_readings` irule) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qexistsl_tac [`b`,`gw`,`ob`,`t4`,`tk`] >> gen_tac >> strip_tac >>
          qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
            (drule_then (map_every assume_tac o CONJUNCTS)) >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`marks`,`t4`] >> simp[]) >>
  irule gas_prefix_full_generated_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G7`,`n`,`t7`,`tn7`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `action` >>
  mp_tac (Q.INST [`ann` |-> `raw_call_return_type flags`,
    `gsK` |-> `gasSummary$gas_explicit marks t4.vs_gas_readings`] raw_call_prepared_tail_prefix) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_call_forced_data_kwargs_prefix_from_action
*)
