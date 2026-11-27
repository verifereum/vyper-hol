(* A single prepared execution for the raw_call arguments and buffers. *)
Theory bodyFullRawCallPrefix
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull bodyFullWordArgs bodyFullIfExpReach stateRelProj
  bodyFullRawCallForcedArgs bodyFullIntCallReturnFrame
  bodyFullRawCallHeader bodyFullRawCallGas bodyFullRawCallOutbuf bodyFullHashKeccakFixed
  bodyFullRawCallGeneratedPrefix bodyFullRawCallPreparedEntry bodyFullRawCallKeywordSuffix
  gasOutcomeFullCompose gasOutcomeFullGuarded exprSimRawCall
  exprSimSource wordArgsPtr gasShadowCompileStmtHelpers gasShadowCompileHelpers
  gasShadowState gasShadowCompileBuiltinSystem representationCleanPtr gasExemptCert
  vyperEvalExprPreservesScopesDom exprLoweringProps exprSimWordArgs fragExec list gasShadow vyperStorageTrace
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]

(* Factor both compilation paths at the argument and preparation boundaries. *)
Theorem raw_call_code_spans:
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (RawCallTarget flags) (a::d::kws) NONE))
    shadow_sa = (vv,shadow_sb) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data;Lit 32w] s3 = (dp,s4) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 =
    ((vo,go,ignored),s5) /\
  lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  (case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = (gas,s6) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr dp len gas (case vo of NONE => Lit 0w | SOME v => v)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  gas_shadow_state sa shadow_sa /\
  EVERY (\kw. kw = EKValue \/ kw = EKGas) flags.rcf_kws /\
  LENGTH kws = LENGTH flags.rcf_kws /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?h1 h2 h4 h5 h6.
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
       (gas_shadow_expr a) shadow_sa = (addr,h1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type d)
       (gas_shadow_expr d) h1 = (data,h2) /\
    lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
      (MAP gas_shadow_expr kws) h4 = (xs,h5) /\
    (case go of NONE => emit_op GAS [] h5 | SOME g => (g,h5)) = (gas,h6) /\
    gas_shadow_state s1 h1 /\ gas_shadow_state s2 h2 /\
    gas_shadow_state s4 h4 /\ gas_shadow_state s5 h5 /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
    ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 s4 func /\
    fn_has_code s4 s5 func /\ fn_has_code s5 s6 func /\ fn_has_code s6 s7 func /\
    fn_has_code shadow_sa h1 shadow_func /\ fn_has_code h1 h2 shadow_func /\
    fn_has_code h4 h5 shadow_func /\ fn_has_code h5 h6 shadow_func
Proof
  strip_tac >>
  `?h1. lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
       (gas_shadow_expr a) shadow_sa = (addr,h1) /\ gas_shadow_state s1 h1` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (BaseT AddressT) a)
       (lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
          (gas_shadow_expr a))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (mp_tac o Q.SPECL [`sa`, `shadow_sa`] o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `?h2. lower_value compile_expr (gas_shadow_env T cenv) (expr_type d)
       (gas_shadow_expr d) h1 = (data,h2) /\ gas_shadow_state s2 h2` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type d) d)
       (lower_value compile_expr (gas_shadow_env T cenv) (expr_type d)
          (gas_shadow_expr d))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (mp_tac o Q.SPECL [`s1`, `h1`] o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `?h3. emit_op MLOAD [data] h2 = (len,h3) /\ gas_shadow_state s3 h3` by
    (mp_tac (Q.INST [`opc` |-> `MLOAD`, `opc'` |-> `MLOAD`, `ops` |-> `[data]`]
       gas_shadow_compiles_emit_op) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s2`, `h2`] mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `?h4. emit_op ADD [data;Lit 32w] h3 = (dp,h4) /\ gas_shadow_state s4 h4` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `opc'` |-> `ADD`, `ops` |-> `[data;Lit 32w]`]
       gas_shadow_compiles_emit_op) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s3`, `h3`] mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `gas_shadow_compiles
     (compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws)
     (compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) NoneT flags.rcf_kws
       (MAP gas_shadow_expr kws))` by
    (irule (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwargs_env
              |> SIMP_RULE (srw_ss()) []) >>
     simp[cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env]) >>
  `?h5. compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) NoneT flags.rcf_kws
       (MAP gas_shadow_expr kws) h4 = ((vo,go,ignored),h5) /\
       gas_shadow_state s5 h5` by
    (qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s4`, `h4`] mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `?h6. (case go of NONE => emit_op GAS [] h5 | SOME g => (g,h5)) = (gas,h6) /\
         gas_shadow_state s6 h6` by
    (Cases_on `go` >> gvs[] >-
     (mp_tac (Q.INST [`opc` |-> `GAS`, `opc'` |-> `GAS`, `ops` |-> `[]`]
        gas_shadow_compiles_emit_op) >>
      rewrite_tac[gas_shadow_compiles_def] >>
      disch_then (qspecl_then [`s5`, `h5`] mp_tac) >>
      simp[] >> metis_tac[pairTheory.PAIR]) >> metis_tac[]) >>
  `?h7. compile_raw_call_outbuf flags.rcf_max_outsize h6 = ((ov,op),h7) /\
         gas_shadow_state s7 h7` by
    (mp_tac (Q.INST [`max_outsize` |-> `flags.rcf_max_outsize`]
       gas_shadow_compiles_raw_call_outbuf) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s6`, `h6`] mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `gas_shadow_compiles
     (lower_word_args cenv (K (BaseT (UintT 256))) kws)
     (lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
        (MAP gas_shadow_expr kws))` by
    simp[gas_shadow_compiles_lower_word_args] >>
  `lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
     (MAP gas_shadow_expr kws) h4 = (xs,h5)` by
    (qpat_x_assum `compile_ext_call_kwargs _ _ _ _ kws s4 = _` kall_tac >>
     drule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)
       exprSimRawCallTheory.raw_call_kwargs_word_args >>
     simp[] >> strip_tac >>
     qpat_x_assum `gas_shadow_compiles (lower_word_args _ _ _) _`
       (mp_tac o Q.SPECL [`s4`,`h4`] o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  `?shadow_result.
   compile_raw_call_finish addr dp len gas (case vo of NONE=>Lit 0w | SOME v=>v)
     (if flags.rcf_is_delegate then DelegateCall
      else if flags.rcf_is_static then StaticCall else RegularCall)
     flags.rcf_max_outsize flags.rcf_revert_on_failure ov op h7=(shadow_result,shadow_sb)` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_expr_def,listTheory.MAP,optionTheory.OPTION_MAP_DEF] >>
     disch_then (strip_assume_tac o MATCH_MP compile_expr_raw_call) >>
     gvs[gas_shadow_expr_type]) >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\ ci_mono s7 sb /\
   ci_mono shadow_sa h1 /\ ci_mono h1 h2 /\ ci_mono h2 h3 /\ ci_mono h3 h4 /\
   ci_mono h4 h5 /\ ci_mono h5 h6 /\ ci_mono h6 h7 /\ ci_mono h7 shadow_sb` by
    (rpt conj_tac >> FIRST
      [ metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND],
        metis_tac[ci_mono_emit_op,pairTheory.SND],
        metis_tac[ci_mono_lower_word_args],
        metis_tac[ci_mono_compile_raw_call_outbuf,pairTheory.SND],
        metis_tac[ci_mono_compile_raw_call_finish,pairTheory.SND],
        (Cases_on `go` >> gvs[] >> metis_tac[ci_mono_emit_op,pairTheory.SND,ci_mono_refl]) ]) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\
   cs_extends s6 s7 /\ cs_extends s7 sb /\
   cs_extends shadow_sa h1 /\ cs_extends h1 h2 /\ cs_extends h2 h3 /\
   cs_extends h3 h4 /\ cs_extends h4 h5 /\ cs_extends h5 h6 /\
   cs_extends h6 h7 /\ cs_extends h7 shadow_sb` by
    (rpt conj_tac >> irule (cj 1 (iffLR ci_mono_def)) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`h1`,`h2`,`h4`,`h5`,`h6`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt (qhdtm_x_assum `cs_extends` mp_tac) >>
  rpt (qhdtm_x_assum `fn_has_code` mp_tac) >> POP_ASSUM_LIST (K all_tac) >>
  rpt strip_tac >> irule fn_has_code_mid >>
  first_assum (irule_at (Pat `fn_has_code _ _ _`)) >>
  metis_tac[compileEnvTheory.cs_extends_refl,compileEnvTheory.cs_extends_trans]
QED

Theorem raw_call_prefix_prepared_full:
 !DF lo dframe PG tops ctx shadow_ctx func shadow_func cenv env cx ty ann flags
  a d kws st0 sa sb shadow_sa shadow_sb vv addr data len ptr vo go ignored
  gas ov op result s1 s2 s3 s4 s5 s6 s7 xs es s0 G0 tn0 k Q R.
 (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
 body_exprs_full_ok_mods mods exps cx (a::d::kws) /\
 body_const_cells_agree mods cx env es /\
 expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
 compile_expr cenv ty (Call ann (RawCallTarget flags) (a::d::kws) NONE) sa=(vv,sb) /\
 compile_expr (gas_shadow_env T cenv) ty
   (gas_shadow_expr (Call ann (RawCallTarget flags) (a::d::kws) NONE))
   shadow_sa=(vv,shadow_sb) /\
 lower_value compile_expr cenv (BaseT AddressT) a sa=(addr,s1) /\
 lower_value compile_expr cenv (expr_type d) d s1=(data,s2) /\
 emit_op MLOAD [data] s2=(len,s3) /\
 emit_op ADD [data;Lit 32w] s3=(ptr,s4) /\
 compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4=
   ((vo,go,ignored),s5) /\
 lower_word_args cenv (K (BaseT (UintT 256))) kws s4=(xs,s5) /\
 (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5)=(gas,s6) /\
 compile_raw_call_outbuf flags.rcf_max_outsize s6=((ov,op),s7) /\
 compile_raw_call_finish addr ptr len gas (case vo of NONE=>Lit 0w | SOME v=>v)
   (if flags.rcf_is_delegate then DelegateCall
    else if flags.rcf_is_static then StaticCall else RegularCall)
   flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7=(result,sb) /\
 gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
 gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
 gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
 MEM shadow_func shadow_ctx.ctx_functions /\
 fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
 fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
 (!H. dead_lo_ok H (DF H) lo cenv cx) /\
 (!x sz. cenv.ce_return_buf=SOME(PtrVar(Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc=SOME(PtrVar(Var x) sz) ==> not_fresh_at sa x) /\
 return_buf_frame dframe cenv sa s0 /\ alloca_history func s0 /\
 (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
 (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
 (!H. valid_horizon cx st0 H es.storage_trace ==>
   stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H) /\
   ghost_inv_at (DF H) lo dframe cenv cx es G0 tn0 s0) /\
 ~s0.vs_halted /\ s0.vs_current_bb=sa.cs_current_bb /\
 s0.vs_inst_idx=LENGTH sa.cs_current_insts /\
 (!av dv kvs. storage_trace_frame (k av dv kvs)) /\
 (!H exc ee gt r. expr_exit (INR exc) r /\ halt_exit H cx ee (INR exc) r ==>
   R H (INR exc) ee gt r) /\
 (!gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7.
   bind (eval_expr cx a) (read_result cx) (es with gas_obs:=gsA)=(INL av,esA) /\
   esA.gas_obs=[] /\
   bind (eval_expr cx d) (read_result cx) (esA with gas_obs:=gsD)=
      (INL(BytesV bs),esD) /\ esD.gas_obs=[] /\
   eval_exprs cx kws (esD with gas_obs:=gsK)=(INL kvs,esK) /\ esK.gas_obs=[] /\
   expr_sim_inv_mods mods cenv cx env esK /\ storage_trace_domain cx st0 esK.storage_trace /\
   vo=ext_call_kwarg EKValue flags.rcf_kws xs /\
   go=ext_call_kwarg EKGas flags.rcf_kws xs /\ ignored=NONE /\
   (!H. valid_horizon cx st0 H esK.storage_trace ==>
     expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
     expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
     expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
     typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
     stmt_state_rel H ctx func cenv cx esK t7 /\
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx esK (FST H) /\
     expr_val_rel cx (BaseT AddressT) av addr t7 /\
     (!x w. MEM x xs /\ eval_operand x tk=SOME w ==> eval_operand x t7=SOME w) /\
     eval_operand len t7=SOME(n2w(LENGTH bs)) /\
     eval_operand ptr t7=SOME(n2w(b+32)) /\ eval_operand gas t7=SOME gw /\
     b+32<dimword(:256) /\ LENGTH bs<dimword(:256) /\
     b+32+LENGTH bs<=t7.vs_alloca_next /\
     mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory=bs /\
     (!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==>
       mem_bytes_at (b+32) (LENGTH bs) mem=bs) /\
     EVERY (\x. op_taint tn7 x={})
       [addr;len;ptr;gas;(case vo of NONE=>Lit 0w | SOME v=>v)] /\
     EVERY (\x. op_prov G7 x=NONE) [addr;len] /\
     (LENGTH bs<>0 ==> ?base sz. op_prov G7 ptr=SOME(base,sz) /\
       base<=b+32 /\ b+32+LENGTH bs<=base+sz) /\
     eval_operand ov t7=SOME(n2w ob) /\
     eval_operand op t7=SOME(n2w(if flags.rcf_max_outsize=0 then ob else ob+32)) /\
     (flags.rcf_max_outsize=0 ==> ov=op) /\
     ob+(if flags.rcf_max_outsize=0 then 0
         else ((flags.rcf_max_outsize+31) DIV 32)*32+32)<dimword(:256) /\
     FLOOKUP t7.vs_allocas s6.cs_next_id=
       SOME(ob,if flags.rcf_max_outsize=0 then 0
               else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
     op_prov G7 ov=SOME(ob,if flags.rcf_max_outsize=0 then 0
                           else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
     op_prov G7 op=SOME(ob,if flags.rcf_max_outsize=0 then 0
                           else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
     op_taint tn7 ov={} /\ op_taint tn7 op={} /\
     (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
       regions_disjoint ob (if flags.rcf_max_outsize=0 then 0
                            else ((flags.rcf_max_outsize+31) DIV 32)*32+32) lb sz) /\
     (cenv.ce_is_ctor ==> !name tv v off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name)=SOME(ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE=>FEMPTY
         | SOME imms=>get_source_immutables cenv.ce_module imms) name=SOME(tv,v) ==>
       regions_disjoint off (type_memory_size tv) ob
         (if flags.rcf_max_outsize=0 then 0
          else ((flags.rcf_max_outsize+31) DIV 32)*32+32)) /\
     wb_frame cenv es esK sa s0 t7 /\ return_buf_frame dframe cenv sa t7 /\
     ~t7.vs_halted /\ t7.vs_current_bb=s7.cs_current_bb /\
     t7.vs_inst_idx=LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
     s0.vs_alloca_next<=t7.vs_alloca_next /\ lo<=t7.vs_alloca_next /\ allocas_from lo t7 /\
     ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7 /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
     EVERY (safe_operand s7)
       [addr;len;ptr;gas;(case vo of NONE=>Lit 0w | SOME v=>v);ov;op] /\
     (!x. MEM (Var x)
       [addr;len;ptr;gas;(case vo of NONE=>Lit 0w | SOME v=>v);ov;op] ==>
       not_fresh_at s7 x)) ==>
   gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (k av (BytesV bs) kvs) (esK,t7,G7,tn7) Q R) ==>
 gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   cenv.ce_modules cx st0
   (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (\dv.
       bind (eval_exprs cx kws) (k av dv)))) (es,s0,G0,tn0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `emit_op ADD [data;Lit 32w] s3 = (dp,s4)` >>
  `expr_type a = BaseT AddressT /\
   ?cap. expr_type d = BaseT (BytesT (Dynamic cap))` by
    (drule raw_call_pre_operands >> simp[] >> metis_tac[]) >>
  `raw_call_kws_ok flags kws /\ LENGTH kws = LENGTH flags.rcf_kws` by
    (drule raw_call_pre_flags >> simp[]) >>
  `EVERY (\kw. kw = EKValue \/ kw = EKGas) flags.rcf_kws /\
   EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by
    metis_tac[raw_call_kwargs_types] >>
  drule_all raw_call_code_spans >> strip_tac >>
  `vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
   go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ignored = NONE` by
    (drule_all exprSimRawCallTheory.raw_call_kwargs_word_args >>
     strip_tac >> gvs[]) >>
  irule gas_outcome_full_initial_domain >> conj_tac
  >- (match_mp_tac storage_trace_frame_bind_all >> conj_tac
      >- (match_mp_tac storage_trace_frame_bind_all >>
          simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> match_mp_tac storage_trace_frame_bind_all >> conj_tac
      >- (match_mp_tac storage_trace_frame_bind_all >>
          simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> match_mp_tac storage_trace_frame_bind_all >>
      simp[cj 6 evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  (* The successful cut of both forced values supplies the keyword IH and
     both child posts, without choosing a new endpoint at each horizon. *)
  irule (BETA_RULE (Q.INST [`k` |-> `\av dv. bind (eval_exprs cx kws) (kk av dv)`]
    raw_call_forced_args_full)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
  qexistsl_tac [`tops`,`shadow_sa`,`h2`,`h1`,`shadow_func`,`sa`,`s2`,`s1`,
                `dframe`,`data`,`addr`] >>
  simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[Q.INST_TYPE [`:'b` |-> `:value`] stmtSimPropsTheory.expr_exit_INR_type,
          exprSimDefsTheory.halt_exit_def]) >>
  conj_tac >- (rpt gen_tac >> irule storage_trace_frame_bind_all >>
               simp[cj 6 evaluate_storage_trace_frame]) >>
  qx_genl_tac [`gsA`,`av`,`esA`,`tA`,`GA`,`tnA`,`gsD`,`bs`,`esD`,`tD`,`GD`,`tnD`] >>
  strip_tac >>
  irule raw_call_forced_data_kwargs_full_from_action >>
  first_assum (irule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
  first_assum (irule_at (Pat `emit_op ADD _ _ = _`)) >>
  qpat_assum `lower_word_args cenv _ kws s4 = _` (irule_at Any) >>
  qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `expr_type d = BaseT (BytesT (Dynamic cap))` (irule_at Any) >>
  qexistsl_tac [`tA`,`s1`,`h5`,`h4`,`esA`,`bs`,`av`,`addr`] >>
  (reverse ((rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >- simp[])
   >- (rpt gen_tac >> strip_tac >>
       qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _` drule >> simp[])) >>
  qx_genl_tac [`b`,`x`,`l`,`p`,`base'`,`cap'`,`t4`,`G4`,`tn4`,`marksK`,`kvs`,`esK`,`tk`,`GK`,`tnK`] >>
  strip_tac >>
  qpat_assum `!tail. eval_exprs cx kws _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `esK with gas_obs := [] = esK` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
     expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
     expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _` drule >> simp[]) >>
  mp_tac (Q.INST [`gsK` |-> `gasSummary$gas_explicit marksK t4.vs_gas_readings`]
    bodyFullRawCallPreparedEntryTheory.raw_call_kwargs_prepared_entry) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  strip_tac >>
  irule raw_call_generated_prefix_full >> simp[] >>
  qexistsl_tac [`G7`,`n`,`t7`,`tn7`] >>
  (conj_tac >- (rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> simp[])) >>
  qpat_assum `!gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7. _` irule >>
  simp[] >>
  qexistsl_tac [`b`,`esA`,`esD`,`gsA`,`gsD`,
    `gasSummary$gas_explicit marksK t4.vs_gas_readings`,`gw`,`ob`,`t4`,`tA`,`tD`,`tk`] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `data = Var x` SUBST_ALL_TAC >>
  qpat_x_assum `len = Var l` SUBST_ALL_TAC >>
  qpat_x_assum `dp = Var p` SUBST_ALL_TAC >>
  qpat_x_assum `vo = ext_call_kwarg EKValue flags.rcf_kws xs` SUBST_ALL_TAC >>
  qpat_assum `expr_type d = BaseT (BytesT (Dynamic cap))` (fn type_eq =>
    qpat_x_assum `expr_store_bound cx (expr_type d) (BytesV bs) _ tD`
      (assume_tac o REWRITE_RULE [type_eq])) >>
  qpat_x_assum `EVERY (\arg. op_taint tn7 arg = {}) _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `EVERY (\arg. op_prov G7 arg = NONE) _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `EVERY (safe_operand s7) _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `!z. MEM (Var z) _ ==> not_fresh_at s7 z`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `LENGTH bs <> 0 ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  PURE_REWRITE_TAC[arithmeticTheory.ADD_ASSOC,
                   Q.SPEC `32` arithmeticTheory.MULT_COMM] >>
  `b + LENGTH bs + 32 = b + 32 + LENGTH bs` by decide_tac >>
  pop_assum (fn eq => PURE_REWRITE_TAC [eq]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
