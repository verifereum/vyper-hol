(* A single prepared execution for the raw_call arguments and buffers. *)
Theory bodyFullRawCallPrefix
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull bodyFullWordArgs bodyFullIfExpReach stateRelProj
  bodyFullRawCallPrefixOps bodyFullIntCallReturnFrame
  bodyFullRawCallHeader bodyFullRawCallGas bodyFullRawCallOutbuf bodyFullHashKeccakFixed
  bodyFullRawCallGeneratedPrefix bodyFullRawCallKwargsBytes bodyFullRawCallKwargsSource
  gasOutcomeFullCompose gasOutcomeFullGuarded exprSimRawCall
  exprSimSource wordArgsPtr gasShadowCompileStmtHelpers gasShadowCompileHelpers
  gasShadowState gasShadowCompileBuiltinSystem representationCleanPtr gasExemptCert
  vyperEvalExprPreservesScopesDom exprLoweringProps exprSimWordArgs fragExec list gasShadow vyperStorageTrace

Theorem raw_call_prefix_prepared_by_impl:
 !A DF lo dframe PG tops ctx shadow_ctx func shadow_func cenv env cx ty ann flags
  a d kws st0 sa sb shadow_sa shadow_sb vv addr data len ptr vo go ignored
  gas ov op result s1 s2 s3 s4 s5 s6 s7 xs es s0 G0 tn0 k Q R.
 body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
 body_exprs_full_ok cx (a::d::kws) /\
 body_const_cells_agree [(NONE,tops)] cx env es /\
 expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
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
 raw_call_initial_intro A cx st0 sa
   (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (\dv.
       bind (eval_exprs cx kws) (k av dv)))) (es,s0,G0,tn0) Q R /\
 (!h1 h2. raw_call_forced_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
   (tops,cenv,env,cx,st0) (ann,flags,a,d,kws)
   (sa,s1,s2,shadow_sa,h1,h2,addr,data) (es,s0,G0,tn0) ==>
   raw_call_forced_intro A (DF,lo,dframe,ctx,func) (cenv,env,cx,tops,st0)
     (a,d,kws) (sa,s1,s2,addr,data) (es,s0,G0,tn0)
     (\av dv. bind (eval_exprs cx kws) (k av dv)) Q R) /\
 (!h4 h5 esD t4 G4 tn4 av dv.
   raw_call_kw_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
     (tops,cenv,env,cx,st0) (s4,s5,h4,h5,kws,xs) (esD,t4,G4,tn4) ==>
   raw_call_kw_intro A (DF,lo,dframe,ctx,shadow_ctx,func,PG) (cenv,cx,st0)
     (s4,s5,kws,xs) (esD,t4,G4,tn4) (k av dv) Q R) /\
 raw_call_neutral_intro A (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   cx st0 s2 s4 (\s n t. n = 0 /\ raw_call_prep_landing s2 s4 s t) Q R /\
 raw_call_neutral_intro A (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   cx st0 s5 s6 (raw_call_gas_landing go s5 s6) Q R /\
 raw_call_neutral_intro A (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   cx st0 s6 s7 (\s n t. n = 0 /\ raw_call_prep_landing s6 s7 s t) Q R /\
 (!gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7.
   bind (eval_expr cx a) (read_result cx) (es with gas_obs:=gsA)=(INL av,esA) /\
   esA.gas_obs=[] /\
   bind (eval_expr cx d) (read_result cx) (esA with gas_obs:=gsD)=
      (INL(BytesV bs),esD) /\ esD.gas_obs=[] /\
   eval_exprs cx kws (esD with gas_obs:=gsK)=(INL kvs,esK) /\ esK.gas_obs=[] /\
   expr_sim_inv cenv cx env esK /\ storage_trace_domain cx st0 esK.storage_trace /\
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
   A s7 (k av (BytesV bs) kvs) (esK,t7,G7,tn7) Q R) ==>
 A sa
   (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (\dv.
       bind (eval_exprs cx kws) (k av dv)))) (es,s0,G0,tn0) Q R
Proof
  rpt gen_tac >> strip_tac >>
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
  rename1 `emit_op ADD [data;Lit 32w] s3 = (dp,s4)` >>
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
  `?h6. (case go of SOME g => (g,h5) | NONE => emit_op GAS [] h5) = (gas,h6) /\
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
  `expr_type a = BaseT AddressT /\
   ?cap. expr_type d = BaseT (BytesT (Dynamic cap))` by
    (drule raw_call_pre_operands >> simp[] >> metis_tac[]) >>
  `raw_call_kws_ok flags kws /\ LENGTH kws = LENGTH flags.rcf_kws` by
    (drule raw_call_pre_flags >> simp[]) >>
  `EVERY (\kw. kw = EKValue \/ kw = EKGas) flags.rcf_kws /\
   EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by
    metis_tac[raw_call_kwargs_types] >>
  `vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
   go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ignored = NONE` by
    (drule_all exprSimRawCallTheory.raw_call_kwargs_word_args >>
     strip_tac >> gvs[]) >>
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
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\ ci_mono s7 sb` by
    (rpt conj_tac
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_emit_op,pairTheory.SND]
     >- metis_tac[ci_mono_emit_op,pairTheory.SND]
     >- metis_tac[ci_mono_lower_word_args]
     >- (qpat_x_assum `(case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = (gas,s6)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >> strip_tac >>
         metis_tac[ci_mono_emit_op,pairTheory.SND,ci_mono_refl])
     >- metis_tac[ci_mono_compile_raw_call_outbuf,pairTheory.SND] >>
     metis_tac[ci_mono_compile_raw_call_finish,pairTheory.SND]) >>
  `?shadow_result.
   compile_raw_call_finish addr dp len gas (case vo of NONE=>Lit 0w | SOME v=>v)
     (if flags.rcf_is_delegate then DelegateCall
      else if flags.rcf_is_static then StaticCall else RegularCall)
     flags.rcf_max_outsize flags.rcf_revert_on_failure ov op h7=(shadow_result,shadow_sb)` by
    (qpat_x_assum `!gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7. _` kall_tac >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_expr_def,listTheory.MAP,optionTheory.OPTION_MAP_DEF] >>
     disch_then (strip_assume_tac o MATCH_MP compile_expr_raw_call) >>
     gvs[gas_shadow_expr_type]) >>
  `ci_mono shadow_sa h1 /\ ci_mono h1 h2 /\ ci_mono h2 h3 /\ ci_mono h3 h4 /\
   ci_mono h4 h5 /\ ci_mono h5 h6 /\ ci_mono h6 h7 /\ ci_mono h7 shadow_sb` by
    (rpt conj_tac
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_emit_op,pairTheory.SND]
     >- metis_tac[ci_mono_emit_op,pairTheory.SND]
     >- metis_tac[ci_mono_lower_word_args]
     >- (qpat_x_assum `(case go of NONE => emit_op GAS [] h5 | SOME g => (g,h5)) = (gas,h6)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >> strip_tac >>
         metis_tac[ci_mono_emit_op,pairTheory.SND,ci_mono_refl])
     >- metis_tac[ci_mono_compile_raw_call_outbuf,pairTheory.SND] >>
     metis_tac[ci_mono_compile_raw_call_finish,pairTheory.SND]) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\
   cs_extends s6 s7 /\ cs_extends s7 sb /\
   cs_extends shadow_sa h1 /\ cs_extends h1 h2 /\ cs_extends h2 h3 /\
   cs_extends h3 h4 /\ cs_extends h4 h5 /\ cs_extends h5 h6 /\
   cs_extends h6 h7 /\ cs_extends h7 shadow_sb` by
    (rpt conj_tac >> irule (cj 1 (iffLR ci_mono_def)) >> first_assum ACCEPT_TAC) >>
  `cs_extends s1 sb /\ cs_extends s2 sb /\ cs_extends s3 sb /\
   cs_extends s4 sb /\ cs_extends s5 sb /\ cs_extends s6 sb /\
   cs_extends h1 shadow_sb /\ cs_extends h2 shadow_sb /\ cs_extends h3 shadow_sb /\
   cs_extends h4 shadow_sb /\ cs_extends h5 shadow_sb /\ cs_extends h6 shadow_sb` by
    (rpt (qhdtm_x_assum `cs_extends` mp_tac) >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> rpt conj_tac >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `cs_extends sa s2 /\ cs_extends sa s3 /\ cs_extends sa s4 /\
   cs_extends sa s5 /\ cs_extends sa s6 /\ cs_extends sa s7 /\
   cs_extends shadow_sa h2 /\ cs_extends shadow_sa h3 /\ cs_extends shadow_sa h4 /\
   cs_extends shadow_sa h5 /\ cs_extends shadow_sa h6 /\ cs_extends shadow_sa h7` by
    (rpt (qhdtm_x_assum `cs_extends` mp_tac) >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> rpt conj_tac >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 s4 func /\
   fn_has_code s4 s5 func /\ fn_has_code s5 s6 func /\ fn_has_code s6 s7 func /\
   fn_has_code shadow_sa h1 shadow_func /\ fn_has_code h1 h2 shadow_func /\
   fn_has_code h2 h4 shadow_func /\ fn_has_code h4 h5 shadow_func /\
   fn_has_code h5 h6 shadow_func /\ fn_has_code h6 h7 shadow_func` by
    (rpt (qhdtm_x_assum `cs_extends` mp_tac) >>
     rpt (qhdtm_x_assum `fn_has_code` mp_tac) >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> rpt conj_tac >> irule fn_has_code_mid >>
     first_assum (irule_at (Pat `fn_has_code _ _ _`)) >>
     metis_tac[compileEnvTheory.cs_extends_refl,compileEnvTheory.cs_extends_trans]) >>
  qpat_assum `raw_call_initial_intro _ _ _ _ _ _ _ _`
    (match_mp_tac o REWRITE_RULE [raw_call_initial_intro_def]) >> conj_tac
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
  `raw_call_forced_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
     (tops,cenv,env,cx,st0) (ann,flags,a,d,kws)
     (sa,s1,s2,shadow_sa,h1,h2,addr,data) (es,s0,G0,tn0)` by
    (simp[raw_call_forced_ready_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h1 h2. raw_call_forced_ready _ _ _ _ _ ==> _` (drule_then assume_tac) >>
  qpat_assum `raw_call_forced_intro _ _ _ _ _ _ _ _ _`
    (match_mp_tac o BETA_RULE o REWRITE_RULE [raw_call_forced_intro_def]) >>
  qx_genl_tac [`gsA`,`av`,`esA`,`tA`,`GA`,`tnA`,`gsD`,`bs`,`esD`,`tD`,`GD`,`tnD`] >>
  strip_tac >>
  `well_typed_expr env a /\ well_typed_expr env d` by
    (qpat_assum `expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es`
       (mp_tac o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `body_const_cells_agree [(NONE,tops)] cx env esA` by
    (irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx a) (read_result cx) _ = (INL av,esA)` (irule_at Any) >>
     simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env esD` by
    (irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx d) (read_result cx) _ = (INL (BytesV bs),esD)` (irule_at Any) >>
     simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace)
     esD.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 esD.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon esD.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `ci_mono sa s1` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame dframe cenv s1 tA` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ ctx func cenv cx a es sa s1 s0 esA av addr tA`
       (assume_tac o MATCH_MP exprSimWordArgsTheory.expr_post_frame) >>
     simp[] >> metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  `post_value_type cenv d = expr_type d` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  `evaluate_type (get_tenv cx) (post_value_type cenv d) =
     SOME (BaseTV (BytesT (Dynamic cap))) /\
   ~is_word_type (post_value_type cenv d)` by
    (`expr_body_pre cenv cx env d esD` by
       (irule exprSimRawCallTheory.expr_body_pre_raw_call_arg >>
        first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     drule_at (Pat `expr_body_pre _ _ _ d _`) exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def,compileEnvTheory.is_word_type_def]) >>
  `stmt_state_rel (storage_trace_horizon esD.storage_trace) ctx func cenv cx esD tD /\
   expr_val_rel cx (post_value_type cenv d) (BytesV bs) data tD` by
    (qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_post_def,NoAsms]) >>
  `?b. eval_operand data tD = SOME (n2w b) /\
       b < dimword (:256) /\
       b+32+LENGTH bs < dimword (:256) /\
       mem_word_at b tD.vs_memory = n2w (LENGTH bs)` by
    (qpat_assum `expr_val_rel cx _ _ data tD` mp_tac >>
     qpat_assum `expr_store_bound cx _ _ data tD` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ esD tD`
       (mp_tac o MATCH_MP stmt_state_rel_alloca_room) >>
     qpat_assum `evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))` mp_tac >>
     qpat_assum `~is_word_type (post_value_type cenv d)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_rel_def,exprSimMemDefsTheory.expr_store_bound_def,
          exprLoweringPropsTheory.alloca_room_def] >>
     rpt strip_tac >> qexists_tac `w2n w` >>
     gvs[exprSimPropsTheory.val_store_size_def,valueEncodingDefsTheory.val_in_memory_def] >>
     qspec_then `LENGTH bs` assume_tac exprSimPropsTheory.le_word_size_mul >>
     decide_tac) >>
  `s1.cs_next_var <= s2.cs_next_var /\ sa.cs_next_var <= s2.cs_next_var` by
    (qpat_assum `ci_mono s1 s2` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `sa.cs_next_var <= s1.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `local_ptrs_reserved cenv s2` by metis_tac[local_ptrs_reserved_next_var] >>
  `!z. data = Var z ==> not_fresh_at s2 z` by
    (qpat_assum `lower_value compile_expr cenv (expr_type d) d s1 = _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  `?th. run_inst_seq (emitted_insts s2 s4) tD = OK th /\
     eval_operand len th = SOME (n2w (LENGTH bs)) /\
     eval_operand dp th = SOME (n2w (b+32)) /\
     (th with vs_vars := tD.vs_vars) = tD /\
     (!z. not_fresh_at s2 z ==> lookup_var z th = lookup_var z tD) /\
     (!z. len = Var z \/ dp = Var z ==> not_fresh_at s4 z) /\
     s4.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 s4 /\
     s4.cs_next_var = s2.cs_next_var + 2 /\ s4.cs_next_id = s2.cs_next_id + 2` by
    (irule exprSimHashTheory.hash_data_prefix_run >> simp[] >> metis_tac[]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `allocas_from lo tD /\ lo <= tD.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ esD GD tnD tD`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp tD` by simp[] >>
  drule_all raw_call_header_joint >>
  disch_then (qspecl_then [`PG`,`esD`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
  disch_then (qx_choose_then `header_end` strip_assume_tac) >>
  qpat_x_assum `header_end = _` SUBST_ALL_TAC >>
  qabbrev_tac `t4 = th with vs_inst_idx := LENGTH s4.cs_current_insts` >>
  qpat_assum `raw_call_neutral_intro _ _ _ _ s2 s4 _ _ _`
    (irule o BETA_RULE o REWRITE_RULE [raw_call_neutral_intro_def]) >>
  conj_tac >- (irule storage_trace_frame_bind_all >>
               simp[cj 6 evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G4`,`0`,`t4`,`tn4`] >> simp[NoAsms] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!D. gas_origin_ptr_path _ (tD,GD,tnD) [] (OK t4,G4,tn4)`
      (qspec_then `DF H` ACCEPT_TAC)) >>
  conj_tac >- (simp[raw_call_prep_landing_def,Abbr `t4`] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
     stmt_state_rel H ctx func cenv cx esD t4 /\
     storage_well_formed_on cx esD (FST H) /\
     ghost_inv_at (DF H) lo dframe cenv cx esD G4 tn4 t4` by
    (qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _` mp_tac >>
     qpat_assum `!H D d. stmt_state_rel _ _ _ _ _ _ tD /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> first_x_assum drule >>
     simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `return_buf_frame dframe cenv s2 tD` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv s1 tA` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[NoAsms] >> strip_tac >> simp[]) >>
  `return_buf_frame dframe cenv s4 t4` by
    (qpat_assum `!sa d. _ ==> return_buf_frame _ _ _ t4 /\ _`
       (qspecl_then [`s2`,`dframe`] mp_tac) >> simp[]) >>
  `(!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
       expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e))` by
    (rpt strip_tac
     >- (irule exprSimRawCallTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     `expr_type e = BaseT (UintT 256)` by
       (qpat_assum `EVERY (\e. expr_type e = _) kws`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `e` mp_tac) >> simp[]) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z)` by
    (qpat_assum `ci_mono s2 s3` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s3 s4` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     rpt strip_tac >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst u. frag_reachable ctx func t4 fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (tD,GD,tnD) [] (OK t4,G4,tn4)`
       (qspec_then `DF (storage_trace_horizon esD.storage_trace)` (fn path =>
        qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
        qpat_assum `!fn inst s. frag_reachable ctx func tD fn inst s ==> _`
          (ACCEPT_TAC o (fn nowrap =>
            MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
              (LIST_CONJ [path, phi, nowrap]))))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t4` by
    (qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==>
        stmt_state_rel H ctx func cenv cx esD t4 /\ _`
      (qspec_then `storage_trace_horizon esD.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `raw_call_kw_ready (DF,lo,dframe,ctx,shadow_ctx,func,shadow_func)
     (tops,cenv,env,cx,st0) (s4,s5,h4,h5,kws,xs) (esD,t4,G4,tn4)` by
    (rewrite_tac[raw_call_kw_ready_def] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  qpat_assum `!h4 h5 esD t4 G4 tn4 av dv. raw_call_kw_ready _ _ _ _ ==> _`
    (drule_then (qspecl_then [`av`,`BytesV bs`] assume_tac)) >>
  qpat_assum `raw_call_kw_intro _ _ _ _ _ _ _ _`
    (match_mp_tac o REWRITE_RULE [raw_call_kw_intro_def]) >>
  qx_genl_tac [`marksK`,`resK`,`esK`,`GK`,`tnK`,`tk`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace)
     esK.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 esK.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> raw_call_kw_post DF lo dframe ctx func cenv cx esD s4 s5 t4 _ _ kws xs H _ esK _ _ _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[raw_call_kw_post_def,NoAsms] >>
  strip_tac >> simp[] >>
  `esK with gas_obs := [] = esK` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_exprs cx kws _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `resK = INL _` SUBST_ALL_TAC >>
  rename1 `typed_args_post _ _ _ _ _ _ _ _ esK _ _ kvs tk` >>
  `expr_sim_inv cenv cx env esK /\ MAP FDOM esK.scopes = MAP FDOM esD.scopes` by
    (qpat_assum `eval_exprs cx kws _ = _`
       (mp_tac o SIMP_RULE (srw_ss()) []) >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` mp_tac >>
     qpat_assum `expr_sim_inv cenv cx env esD` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at (Pat `eval_exprs _ _ _ = _`) raw_call_kwargs_source_inv >>
     disch_then (qspecl_then [`cenv`,`env`,`ann`,`flags`,`a::d::kws`,`NONE`,`es`] mp_tac) >>
     simp[EVERY_MEM]) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
     typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
     stmt_state_rel H ctx func cenv cx esK tk /\
     storage_well_formed_on cx esK (FST H) /\
     ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk` by
    (qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==>
       raw_call_kw_post DF lo dframe ctx func cenv cx esD s4 s5 t4 _ _ kws xs H _ esK _ _ _` mp_tac >>
     simp[raw_call_kw_post_def,NoAsms] >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> first_x_assum drule >>
     simp[exprSimPrecompilesTheory.typed_args_post_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
     valid_horizon cx st0 H esD.storage_trace` by
    (qpat_assum `eval_exprs cx kws _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `storage_trace_frame (eval_exprs cx kws)` by simp[cj 6 evaluate_storage_trace_frame] >>
     drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     gvs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  `wb_frame cenv esD esK s4 t4 tk` by
    (qpat_assum `typed_args_post _ _ _ _ _ _ _ _ esK _ _ kvs tk`
       (mp_tac o REWRITE_RULE [exprSimPrecompilesTheory.typed_args_post_def]) >> simp[]) >>
  `return_buf_frame dframe cenv s5 tk` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv s4 t4` (irule_at Any) >>
     qpat_assum `ci_mono s4 s5` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `wb_frame cenv esD esK s4 t4 tk`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `t4.vs_alloca_next <= tk.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `s2.cs_next_var <= s4.cs_next_var /\ s2.cs_next_id <= s4.cs_next_id /\
   sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_id <= s4.cs_next_id` by
    (qpat_assum `ci_mono s2 s3` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s3 s4` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono sa s1` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s1 s2` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!name lb sz. local_region cenv esD.scopes t4 name lb sz <=>
                 local_region cenv esD.scopes tD name lb sz` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     qpat_assum `local_ptrs_reserved cenv s2`
       (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z t4 = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `eval_operand data t4 = SOME(n2w b)` by
    (qpat_assum `eval_operand data tD = _` mp_tac >>
     qpat_assum `data = Var _` mp_tac >>
     qpat_assum `!z. data = Var z ==> not_fresh_at s2 z` mp_tac >>
     qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z t4 = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `expr_val_at cenv cx (BaseT(BytesT(Dynamic cap))) s1 s2 esD (BytesV bs) data t4` by
    (qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     qpat_assum `post_value_type cenv d = _` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     qpat_assum `eval_operand data t4 = _` mp_tac >>
     qpat_assum `eval_operand data tD = _` mp_tac >>
     qpat_assum `t4.vs_allocas = tD.vs_allocas` mp_tac >>
     qpat_assum `!name lb sz. local_region _ _ t4 _ _ _ <=> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_at_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (BaseT(BytesT(Dynamic cap))) =
     SOME(BaseTV(BytesT(Dynamic cap)))` by
    (qpat_assum `evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))` mp_tac >>
     qpat_assum `post_value_type cenv d = _` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!mem. mem_agree_outside tnK.t_mem tk.vs_memory mem ==>
       mem_bytes_at (b+32) (LENGTH bs) mem = bs` by
    (gen_tac >> strip_tac >> drule_all raw_call_kwargs_bytes_frame >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM esA.scopes /\
   MAP FDOM esA.scopes = MAP FDOM esD.scopes` by
    (qpat_assum `bind (eval_expr cx a) (read_result cx) _ = _`
       (mp_tac o MATCH_MP (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom)) >>
     qpat_assum `bind (eval_expr cx d) (read_result cx) _ = _`
       (mp_tac o MATCH_MP (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 es.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  `wb_frame cenv es esA sa s0 tA /\ wb_frame cenv esA esD s1 tA tD` by
    (qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_post_def,loweringPostsTheory.wb_frame_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `sa.cs_next_id <= s1.cs_next_id` by
    (qpat_assum `ci_mono sa s1` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `wb_frame cenv es esD sa s0 tD /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GD tnD` by
    (qpat_assum `wb_frame cenv es esA sa s0 tA` mp_tac >>
     qpat_assum `wb_frame cenv esA esD s1 tA tD` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ es s0` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `MAP FDOM es.scopes = MAP FDOM esA.scopes` mp_tac >>
     qpat_assum `sa.cs_next_var <= s1.cs_next_var` mp_tac >>
     qpat_assum `sa.cs_next_id <= s1.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[wb_frame_trans,ghost_kept_at_wb_trans]) >>
  `wb_frame cenv es esD sa s0 t4 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4` by
    (conj_tac
     >- (qpat_assum `!sa es0 s0. _ ==> wb_frame _ _ _ _ _ t4` irule >> simp[]) >>
     qpat_assum `!sa es0 s0 G0 tn0. _ ==> ghost_kept_at _ _ _ _ _ _ _ G4 tn4` irule >> simp[]) >>
  `wb_frame cenv es esK sa s0 tk /\ ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK` by
    (qpat_assum `wb_frame cenv es esD sa s0 t4` mp_tac >>
     qpat_assum `wb_frame cenv esD esK s4 t4 tk` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ es s0` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `MAP FDOM es.scopes = MAP FDOM esA.scopes` mp_tac >>
     qpat_assum `MAP FDOM esA.scopes = MAP FDOM esD.scopes` mp_tac >>
     qpat_assum `sa.cs_next_var <= s4.cs_next_var` mp_tac >>
     qpat_assum `sa.cs_next_id <= s4.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[wb_frame_trans,ghost_kept_at_wb_trans]) >>
  `return_buf_frame dframe cenv sa tk` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es esK sa s0 tk`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `s0.vs_alloca_next <= tA.vs_alloca_next` mp_tac >>
     qpat_assum `tA.vs_alloca_next <= tD.vs_alloca_next` mp_tac >>
     qpat_assum `t4.vs_alloca_next <= tk.vs_alloca_next` mp_tac >>
     qpat_assum `t4.vs_alloca_next = tD.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!x. not_fresh_at s4 x ==>
     FLOOKUP GK x = FLOOKUP G4 x /\
     op_taint tnK (Var x) = op_taint tn4 (Var x)` by
    (qpat_assum `ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >> simp[]) >>
  `!x w. not_fresh_at s4 x /\ lookup_var x t4 = SOME w ==>
     lookup_var x tk = SOME w` by
    (qpat_assum `wb_frame cenv esD esK s4 t4 tk`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >> simp[]) >>
  `eval_operand len tk = SOME(n2w(LENGTH bs)) /\
   eval_operand dp tk = SOME(n2w(b+32)) /\
   op_taint tnK len = {} /\ op_taint tnK dp = {} /\
   op_prov GK len = NONE /\ op_prov GK dp = SOME(base',cap')` by
    (qpat_assum `!x w. not_fresh_at s4 x /\ _ ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at s4 x ==> _ /\ _` mp_tac >>
     qpat_assum `!z. len = Var z \/ dp = Var z ==> _` mp_tac >>
     qpat_assum `len = Var l` mp_tac >> qpat_assum `dp = Var p` mp_tac >>
     qpat_assum `eval_operand len t4 = _` mp_tac >>
     qpat_assum `eval_operand dp t4 = _` mp_tac >>
     qpat_assum `op_taint tn4 len = {}` mp_tac >>
     qpat_assum `op_taint tn4 dp = {}` mp_tac >>
     qpat_assum `op_prov G4 len = NONE` mp_tac >>
     qpat_assum `FLOOKUP G4 p = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >>
     gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_prov_def] >>
     metis_tac[]) >>
  `s1.cs_next_var <= s4.cs_next_var /\ s1.cs_next_id <= s4.cs_next_id` by
    (qpat_assum `ci_mono s1 s2` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s2 s3` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s3 s4` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `wb_frame cenv esA esD s1 tA t4 /\
   ghost_kept_at lo cenv esA s1 GA tnA tA G4 tn4` by
    (conj_tac
     >- (qpat_assum `!sa es0 s0. _ ==> wb_frame _ _ _ _ _ t4` irule >> simp[]) >>
     qpat_assum `!sa es0 s0 G0 tn0. _ ==> ghost_kept_at _ _ _ _ _ _ _ G4 tn4` irule >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon esD.storage_trace) ctx func cenv cx esA tA` by
    (qpat_assum `expr_post _ ctx func cenv cx a es sa s1 s0 esA av addr tA`
       (mp_tac o MATCH_MP exprSimWordArgsTheory.expr_post_state) >> simp[]) >>
  `wb_frame cenv esA esK s1 tA tk /\
   ghost_kept_at lo cenv esA s1 GA tnA tA GK tnK` by
    (qpat_assum `wb_frame cenv esA esD s1 tA t4` mp_tac >>
     qpat_assum `wb_frame cenv esD esK s4 t4 tk` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv esA s1 GA tnA tA G4 tn4` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ esA tA` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s1` mp_tac >>
     qpat_assum `MAP FDOM esA.scopes = MAP FDOM esD.scopes` mp_tac >>
     qpat_assum `s1.cs_next_var <= s4.cs_next_var` mp_tac >>
     qpat_assum `s1.cs_next_id <= s4.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[wb_frame_trans,ghost_kept_at_wb_trans]) >>
  `!z. addr = Var z ==> not_fresh_at s1 z` by
    (qpat_assum `lower_value compile_expr cenv (BaseT AddressT) a sa = _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  `post_value_type cenv a = BaseT AddressT` by
    (qpat_assum `expr_type a = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     simp[loweringPostsTheory.post_value_type_word,compileEnvTheory.is_word_type_def]) >>
  `expr_val_rel cx (BaseT AddressT) av addr tA /\
   op_taint tnA addr = {} /\ op_prov GA addr = NONE` by
    (qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     qpat_assum `ptr_val_ok cx (post_value_type cenv a) av addr GA tnA tA` mp_tac >>
     qpat_assum `post_value_type cenv a = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def,compileEnvTheory.is_word_type_def]) >>
  `expr_body_pre cenv cx env a es` by
    (irule exprSimRawCallTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `!l. addr <> Label l` by
    (qpat_assum `lower_value compile_expr cenv (BaseT AddressT) a sa = _` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env a es` mp_tac >>
     qpat_assum `expr_type a = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `is_word_type (expr_type a)` by simp[compileEnvTheory.is_word_type_def] >>
     drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `!w. eval_operand addr tA = SOME w ==> eval_operand addr tk = SOME w` by
    (qpat_assum `wb_frame cenv esA esK s1 tA tk`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `!z. addr = Var z ==> not_fresh_at s1 z` mp_tac >>
     qpat_assum `!l. addr <> Label l` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `addr` >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `expr_val_rel cx (BaseT AddressT) av addr tk` by
    (qpat_assum `expr_val_rel cx (BaseT AddressT) av addr tA` mp_tac >>
     qpat_assum `!w. eval_operand addr tA = SOME w ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_rel_def,compileEnvTheory.is_word_type_def] >>
     metis_tac[]) >>
  `op_taint tnK addr = {} /\ op_prov GK addr = NONE` by
    (qpat_assum `ghost_kept_at lo cenv esA s1 GA tnA tA GK tnK`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     qpat_assum `!z. addr = Var z ==> not_fresh_at s1 z` mp_tac >>
     qpat_assum `op_taint tnA addr = {}` mp_tac >>
     qpat_assum `op_prov GA addr = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `addr` >>
     simp[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!x. MEM x xs ==> ?w. eval_operand x tk = SOME w` by
    (qpat_assum `typed_args_post _ _ _ _ _ _ _ _ esK _ _ kvs tk`
       (mp_tac o REWRITE_RULE [exprSimPrecompilesTheory.typed_args_post_def]) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >> metis_tac[]) >>
  `!kw x. ext_call_kwarg kw flags.rcf_kws xs = SOME x ==>
       ?w. eval_operand x tk = SOME w /\ op_taint tnK x = {}` by
    (qpat_assum `!x. MEM x xs ==> ?w. eval_operand x tk = SOME w` mp_tac >>
     qpat_assum `EVERY (\x. op_taint tnK x = {}) xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     qid_spec_tac `xs` >> qspec_tac (`flags.rcf_kws`,`ks`) >>
     Induct_on `ks` >> Cases_on `xs` >> simp[vyperInterpreterTheory.ext_call_kwarg_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `(!g. go = SOME g ==> ?w. eval_operand g tk = SOME w /\ op_taint tnK g = {}) /\
   (!v. vo = SOME v ==> ?w. eval_operand v tk = SOME w /\ op_taint tnK v = {})` by
    (qpat_assum `!kw x. ext_call_kwarg _ _ _ = _ ==> _` mp_tac >>
     qpat_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_assum `vo = ext_call_kwarg _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `s4.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `ci_mono s4 s5` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `local_ptrs_reserved cenv s5` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s5 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s5 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `?t6 G6 tn6 gw n.
     raw_call_gas_landing go s5 s6 tk n t6 /\
     eval_operand gas t6 = SOME gw /\ op_taint tn6 gas = {} /\
     ~t6.vs_halted /\ t6.vs_current_bb = s6.cs_current_bb /\
     t6.vs_inst_idx = LENGTH s6.cs_current_insts /\ alloca_history func t6 /\
     t6.vs_memory = tk.vs_memory /\ t6.vs_allocas = tk.vs_allocas /\
     t6.vs_alloca_next = tk.vs_alloca_next /\ t6.vs_fmp = tk.vs_fmp /\
     tn6.t_mem = tnK.t_mem /\ tn6.t_stor = tnK.t_stor /\
     tn6.t_trans = tnK.t_trans /\ tn6.t_imm = tnK.t_imm /\
     (!x. not_fresh_at s5 x ==> lookup_var x t6 = lookup_var x tk /\
       FLOOKUP G6 x = FLOOKUP GK x /\ op_taint tn6 (Var x) = op_taint tnK (Var x)) /\
     (!H. valid_horizon cx st0 H esK.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (tk,GK,tnK) (REPLICATE n F) (OK t6,G6,tn6) /\
       ghost_inv_at (DF H) lo dframe cenv cx esK G6 tn6 t6 /\
       stmt_state_rel H ctx func cenv cx esK t6 /\
       storage_well_formed_on cx esK (FST H) /\
       ghost_kept_at lo cenv esK s5 GK tnK tk G6 tn6)` by
    (Cases_on `go`
     >- (mp_tac (Q.INST [`go` |-> `NONE`, `shadow_go` |-> `NONE`,
           `sa` |-> `s5`, `sb` |-> `s6`, `shadow_sa` |-> `h5`, `shadow_sb` |-> `h6`,
           `shadow_gas` |-> `gas`, `s` |-> `tk`, `G` |-> `GK`, `tn` |-> `tnK`,
           `es` |-> `esK`, `d` |-> `dframe`] raw_call_optional_gas_joint) >>
         (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
         qexistsl_tac [`t`,`G6`,`tn6`,`gw`,`1`] >>
         simp[raw_call_gas_landing_def] >>
         (conj_tac >- (qexists_tac `gw` >>
            qpat_assum `(case NONE of NONE => gas_prefix _ _ = _ /\ _ | SOME _ => _)` mp_tac >>
            simp[NoAsms] >> metis_tac[])) >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         `REPLICATE 1 F = [F]` by EVAL_TAC >> simp[] >> metis_tac[]) >>
     qpat_assum `(case SOME _ of NONE => _ | SOME _ => _) = (gas,s6)` mp_tac >>
     simp_tac std_ss [] >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) >>
     qpat_assum `!g. SOME _ = SOME g ==> _` (qspec_then `gas` mp_tac) >>
     simp_tac std_ss [] >> strip_tac >>
     qexistsl_tac [`tk`,`GK`,`tnK`,`w`,`0`] >>
     simp[raw_call_gas_landing_def,bodyPtrDefsTheory.ghost_kept_at_def,
          fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
     metis_tac[]) >>
  qpat_assum `raw_call_neutral_intro _ _ _ _ s5 s6 _ _ _`
    (irule o REWRITE_RULE [raw_call_neutral_intro_def]) >>
  simp[] >> qexistsl_tac [`G6`,`n`,`t6`,`tn6`] >> simp[] >>
  reverse conj_tac
  >- (qpat_assum `raw_call_gas_landing go s5 s6 tk n t6` mp_tac >>
      qpat_assum `go = ext_call_kwarg EKGas _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx esK t6 /\
   ghost_kept_at lo cenv esK s5 GK tnK tk G6 tn6 /\
   ghost_inv_at (DF (storage_trace_horizon esK.storage_trace)) lo dframe cenv cx esK G6 tn6 t6` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `local_ptrs_reserved cenv s6 /\ sa.cs_next_var <= s6.cs_next_var /\
   sa.cs_next_var <= s5.cs_next_var /\ sa.cs_next_id <= s5.cs_next_id` by
    (qpat_assum `ci_mono s5 s6` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s4 s5` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `sa.cs_next_var <= s4.cs_next_var` mp_tac >>
     qpat_assum `sa.cs_next_id <= s4.cs_next_id` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s5` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[local_ptrs_reserved_next_var,arithmeticTheory.LESS_EQ_TRANS]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `(if flags.rcf_max_outsize = 0 then 0 else
       ((flags.rcf_max_outsize+31) DIV 32)*32+32) < dimword (:256)` by
    (Cases_on `flags.rcf_max_outsize = 0` >- simp[] >>
     qpat_assum `flags.rcf_max_outsize <> 0` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env (Call ann (RawCallTarget flags) _ _) es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule exprSimRawCallTheory.raw_call_pre_flags >> strip_tac >>
     `type_alloc_ok cenv ann` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def] >>
     Cases_on `flags.rcf_revert_on_failure` >>
     gvs[vyperTypeSystemTheory.raw_call_return_type_def,allocLimitsTheory.type_alloc_ok_def,
         compileEnvTheory.is_word_type_def,compileEnvTheory.type_memory_bytes_def] >>
     `2 ** 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
     fs[] >> decide_tac) >>
  `?u. run_inst_seq (emitted_insts s6 s7) t6 = OK u` by
    (qpat_assum `compile_raw_call_outbuf flags.rcf_max_outsize s6 = _` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ esK t6` mp_tac >>
     qpat_assum `fn_inst_ids_distinct func` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s6` mp_tac >>
     qpat_assum `fn_has_code s6 s7 func` mp_tac >>
     qpat_assum `(if flags.rcf_max_outsize = 0 then 0 else _) < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `flags.rcf_max_outsize = 0` >> fs[]
     >- (drule_all raw_call_outbuf_zero_run >> metis_tac[]) >>
     `0 < flags.rcf_max_outsize` by decide_tac >>
     metis_tac[raw_call_outbuf_positive_run,arithmeticTheory.MULT_COMM]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s5 x` by
    (qpat_assum `sa.cs_next_var <= s5.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `wb_frame cenv es esK sa s0 t6` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`s5`, `tk`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` drule >> simp[]) >>
  `return_buf_frame dframe cenv sa t6` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `tk`, `sa`] >> simp[] >>
     rpt strip_tac >>
     `not_fresh_at s5 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` drule >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G6 tn6` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qexistsl_tac [`GK`, `tnK`] >> simp[] >> rpt strip_tac >>
     `not_fresh_at s5 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` drule >> simp[]) >>
  `allocas_from lo t6 /\ lo <= t6.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo dframe cenv cx esK G6 tn6 t6`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  `s0.vs_alloca_next <= t6.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= tA.vs_alloca_next` mp_tac >>
     qpat_assum `tA.vs_alloca_next <= tD.vs_alloca_next` mp_tac >>
     qpat_assum `t4.vs_alloca_next = tD.vs_alloca_next` mp_tac >>
     qpat_assum `t4.vs_alloca_next <= tk.vs_alloca_next` mp_tac >>
     qpat_assum `t6.vs_alloca_next = tk.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME(off,sz) /\
     aid < sa.cs_next_id ==> off+sz <= t6.vs_alloca_next` by
    (qpat_assum `wb_frame cenv es esK sa s0 t6`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ esK t6`
       (mp_tac o MATCH_MP (cj 2 stmt_state_rel_local_ptrs_alloca)) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]) >>
  `!name lb sz. local_region cenv es.scopes s0 name lb sz ==>
     lb+sz <= t6.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0` mp_tac >>
     qpat_assum `s0.vs_alloca_next <= t6.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[bodyMemoryDefsTheory.body_local_region_frontier,arithmeticTheory.LESS_EQ_TRANS]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t6 /\
    t6.vs_alloca_next + pending_alloca_size func t6 <= w2n t6.vs_initial_fmp` by
    (strip_tac >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx esK t6`
       (fn rel => conj_tac
          >- (match_mp_tac (MATCH_MP stmt_state_rel_allocas_below_fmp rel) >>
              first_assum ACCEPT_TAC)
          >> mp_tac (MATCH_MP stmt_state_rel_fmp_room rel)) >>
     qpat_assum `ctx_has_dalloca ctx` (fn has =>
       simp[NoAsms,fmp_room_def,has]) >> decide_tac) >>
  qabbrev_tac `t7 = u with vs_inst_idx := LENGTH s7.cs_current_insts` >>
  mp_tac (Q.INST [`sa` |-> `s6`, `sb` |-> `s7`, `sk` |-> `sa`,
    `es0` |-> `es`, `es` |-> `esK`, `s` |-> `t6`, `d` |-> `dframe`,
    `G` |-> `G6`, `tn` |-> `tn6`, `M` |-> `flags.rcf_max_outsize`,
    `n` |-> `if flags.rcf_max_outsize = 0 then 0 else
       ((flags.rcf_max_outsize+31) DIV 32)*32+32`] raw_call_outbuf_joint) >>
  (impl_tac >- (simp[Abbr `t7`] >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
    qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _` mp_tac >>
    qpat_assum `!name lb sz. local_region cenv es.scopes s0 name lb sz ==> _` mp_tac >>
    qpat_assum `t6.vs_alloca_next = tk.vs_alloca_next` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
  strip_tac >>
  `s5.cs_next_var <= s6.cs_next_var` by
    (qpat_assum `ci_mono s5 s6` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `!x. not_fresh_at s5 x ==>
     lookup_var x t7 = lookup_var x tk /\ FLOOKUP G7 x = FLOOKUP GK x /\
     op_taint tn7 (Var x) = op_taint tnK (Var x)` by
    (qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at s6 x ==> _ /\ _` mp_tac >>
     qpat_assum `s5.cs_next_var <= s6.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `!x. safe_operand s5 x ==> eval_operand x t7 = eval_operand x tk /\
      op_prov G7 x = op_prov GK x /\ op_taint tn7 x = op_taint tnK x` by
    (qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> Cases >>
     simp[exprSafeOperandTheory.safe_operand_def,venomStateTheory.eval_operand_def,
          ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def]) >>
  `safe_operand s5 addr /\ safe_operand s5 len /\ safe_operand s5 dp` by
    (qpat_assum `!z. addr = Var z ==> not_fresh_at s1 z` mp_tac >>
     qpat_assum `!l. addr <> Label l` mp_tac >>
     qpat_assum `!z. len = Var z \/ dp = Var z ==> not_fresh_at s4 z` mp_tac >>
     qpat_assum `len = Var l` mp_tac >> qpat_assum `dp = Var p` mp_tac >>
     qpat_assum `s1.cs_next_var <= s4.cs_next_var` mp_tac >>
     qpat_assum `s4.cs_next_var <= s5.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `EVERY (safe_operand s5) xs` by
    (`wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
      (qpat_assum `!e ee. MEM e kws /\ _ ==> _` mp_tac >>
       qpat_assum `expr_sim_inv cenv cx env esK` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[wb_args_shape_def] >> rpt strip_tac >>
       drule expr_body_pre_lower_value_word_shape >> metis_tac[]) >>
     qpat_assum `wb_args_shape cenv _ kws` mp_tac >>
     qpat_assum `lower_word_args cenv _ kws s4 = (xs,s5)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all lower_word_args_shape_ready >>
     simp[EVERY_MEM,exprSafeOperandTheory.safe_operand_def] >> metis_tac[]) >>
  `!kw x. ext_call_kwarg kw flags.rcf_kws xs = SOME x ==> safe_operand s5 x` by
    (qpat_assum `EVERY (safe_operand s5) xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `xs` >>
     qspec_tac (`flags.rcf_kws`,`ks`) >> Induct_on `ks` >> Cases_on `xs` >>
     simp[vyperInterpreterTheory.ext_call_kwarg_def] >> rpt strip_tac >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  `safe_operand s5 (case vo of NONE => Lit 0w | SOME v => v)` by
    (Cases_on `vo` >> simp[] >> metis_tac[]) >>
  `expr_val_rel cx (BaseT AddressT) av addr t7 /\
   eval_operand len t7 = SOME(n2w(LENGTH bs)) /\
   eval_operand dp t7 = SOME(n2w(b+32)) /\
   op_taint tn7 addr = {} /\ op_taint tn7 len = {} /\ op_taint tn7 dp = {} /\
   op_prov G7 addr = NONE /\ op_prov G7 len = NONE /\
   op_prov G7 dp = SOME(base',cap')` by
    (qpat_assum `!x. safe_operand s5 x ==> _ /\ _ /\ _` mp_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`safe_operand s5 addr`, `safe_operand s5 len`, `safe_operand s5 dp`,
        `expr_val_rel cx (BaseT AddressT) av addr tk`,
        `eval_operand len tk = _`, `eval_operand dp tk = _`,
        `op_taint tnK addr = {}`, `op_taint tnK len = {}`, `op_taint tnK dp = {}`,
        `op_prov GK addr = NONE`, `op_prov GK len = NONE`, `op_prov GK dp = _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_rel_def,compileEnvTheory.is_word_type_def]) >>
  `safe_operand s6 gas` by
    (qpat_assum `(case go of NONE => _ | SOME _ => _) = (gas,s6)` mp_tac >>
     qpat_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_assum `!kw x. ext_call_kwarg _ _ _ = _ ==> safe_operand s5 x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >>
     metis_tac[exprSafeOperandTheory.emit_op_safe_operand]) >>
  `eval_operand gas t7 = SOME gw /\ op_taint tn7 gas = {}` by
    (qpat_assum `!x. not_fresh_at s6 x ==> _ /\ _` mp_tac >>
     qpat_assum `safe_operand s6 gas` mp_tac >>
     qpat_assum `eval_operand gas t6 = SOME gw` mp_tac >>
     qpat_assum `op_taint tn6 gas = {}` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `gas` >>
     simp[exprSafeOperandTheory.safe_operand_def,venomStateTheory.eval_operand_def,
          ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `op_taint tn7 (case vo of NONE => Lit 0w | SOME v => v) = {}` by
    (qpat_assum `!x. safe_operand s5 x ==> _ /\ _ /\ _` mp_tac >>
     qpat_assum `safe_operand s5 (case vo of NONE => _ | SOME _ => _)` mp_tac >>
     qpat_assum `!v. vo = SOME v ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `vo` >>
     simp[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `b+32+LENGTH bs <= tD.vs_alloca_next` by
    (qpat_assum `expr_store_bound cx _ (BytesV bs) data tD`
       (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
     qpat_assum `evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))` mp_tac >>
     qpat_assum `eval_operand data tD = SOME(n2w b)` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     qpat_assum `post_value_type cenv d = _` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compileEnvTheory.is_word_type_def,exprSimPropsTheory.val_store_size_def] >>
     qspec_then `LENGTH bs` mp_tac exprSimPropsTheory.le_word_size_mul >> rpt strip_tac >> decide_tac) >>
  `b+32+LENGTH bs <= t6.vs_alloca_next` by
    (qpat_assum `b+32+LENGTH bs <= tD.vs_alloca_next` mp_tac >>
     qpat_assum `t4.vs_alloca_next = tD.vs_alloca_next` mp_tac >>
     qpat_assum `t4.vs_alloca_next <= tk.vs_alloca_next` mp_tac >>
     qpat_assum `t6.vs_alloca_next = tk.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory = bs /\
   (!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==>
       mem_bytes_at (b+32) (LENGTH bs) mem = bs)` by
    (qpat_assum `!mem. mem_agree_outside tnK.t_mem _ _ ==> _` mp_tac >>
     qpat_assum `t7.vs_memory = t6.vs_memory` mp_tac >>
     qpat_assum `t6.vs_memory = tk.vs_memory` mp_tac >>
     qpat_assum `tn6.t_mem = tnK.t_mem` mp_tac >>
     qpat_assum `!i. i IN tn7.t_mem <=> _` mp_tac >>
     qpat_assum `b+32+LENGTH bs <= t6.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory = bs` by
       metis_tac[bodyPtrDefsTheory.mem_agree_outside_def] >>
     simp[] >>
     `!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tnK.t_mem` by
       (drule representationCleanPtrTheory.robust_mem_bytes_at_clean >> simp[]) >>
     `mem_bytes_at (b+32) (LENGTH bs) t7.vs_memory =
      mem_bytes_at (b+32) (LENGTH bs) mem` by
       (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
        fs[bodyPtrDefsTheory.mem_agree_outside_def] >> rpt strip_tac >>
        first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx esK t7` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t7 /\ _`
       (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >> simp[]) >>
  drule_all raw_call_outbuf_separated >> strip_tac >>
  `s6.cs_next_var <= s7.cs_next_var /\ s5.cs_next_var <= s7.cs_next_var` by
    (qpat_assum `ci_mono s6 s7` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `s5.cs_next_var <= s6.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `safe_operand s7 ov /\ safe_operand s7 op` by
    (qpat_assum `!x. ov = Var x \/ op = Var x ==> not_fresh_at s7 x` mp_tac >>
     qpat_assum `op_prov G7 ov = SOME _` mp_tac >>
     qpat_assum `op_prov G7 op = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `ov` >> Cases_on `op` >>
     simp[exprSafeOperandTheory.safe_operand_def,ptrDisciplineTheory.op_prov_def]) >>
  `EVERY (safe_operand s7)
     [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op]` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`safe_operand s5 addr`, `safe_operand s5 len`, `safe_operand s5 dp`,
        `safe_operand s5 (case vo of NONE => _ | SOME _ => _)`,
        `safe_operand s6 gas`, `safe_operand s7 ov`, `safe_operand s7 op`,
        `s6.cs_next_var <= s7.cs_next_var`, `s5.cs_next_var <= s7.cs_next_var`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >>
     metis_tac[exprSafeOperandTheory.safe_operand_mono]) >>
  `!x. MEM (Var x) [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v);ov;op] ==>
      not_fresh_at s7 x` by
    (qpat_assum `EVERY (safe_operand s7) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM,exprSafeOperandTheory.safe_operand_def] >> metis_tac[]) >>
  `(flags.rcf_max_outsize = 0 ==> ov = op)` by
    (qpat_assum `compile_raw_call_outbuf flags.rcf_max_outsize s6 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> strip_tac >>
     gvs[builtinSystemTheory.compile_raw_call_outbuf_def,compileEnvTheory.comp_bind_def,
         compileEnvTheory.comp_return_def] >> pairarg_tac >> gvs[]) >>
  qpat_assum `raw_call_neutral_intro _ _ _ _ s6 s7 _ _ _`
    (irule o BETA_RULE o REWRITE_RULE [raw_call_neutral_intro_def]) >>
  simp[] >> qexistsl_tac [`G7`,`t7`,`tn7`] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!D explicit. gas_origin_ptr_path _ (t6,G6,tn6) [] (OK t7,G7,tn7)`
      (qspecl_then [`DF H`,`gas_explicit_sites ctx shadow_ctx`] ACCEPT_TAC)) >>
  conj_tac >- (rewrite_tac[raw_call_prep_landing_def] >> qexists_tac `u` >>
               simp[Abbr `t7`]) >>
  qpat_assum `!gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7. _` irule >>
  simp[] >>
  qexistsl_tac [`b`,`esA`,`esD`,`gsA`,`gsD`,
    `gasSummary$gas_explicit marksK t4.vs_gas_readings`,`gw`,`b'`,`t4`,`tA`,`tD`,`tk`] >>
  simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H esD.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> valid_horizon _ _ H esD.storage_trace` irule >> simp[]) >>
  `valid_horizon cx st0 H esA.storage_trace` by
    (qpat_assum `bind (eval_expr cx d) (read_result cx) _ = _` mp_tac >>
     qpat_assum `valid_horizon cx st0 H esD.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `storage_trace_frame (bind (eval_expr cx d) (read_result cx))` by
       simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_bind,storage_trace_frame_read_result] >>
     drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     gvs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind (eval_expr cx a) (read_result cx) _ = _` mp_tac >>
     qpat_assum `valid_horizon cx st0 H esA.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `storage_trace_frame (bind (eval_expr cx a) (read_result cx))` by
       simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_bind,storage_trace_frame_read_result] >>
     drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     gvs[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  qpat_assum `!H. valid_horizon cx st0 H esD.storage_trace ==>
      expr_post H ctx func cenv cx a _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `data = Var x` SUBST_ALL_TAC >>
  simp[] >>
  conj_tac >-
    (qpat_assum `expr_store_bound cx (post_value_type cenv d) (BytesV bs) _ tD` mp_tac >>
     qpat_assum `post_value_type cenv d = expr_type d` mp_tac >>
     qpat_assum `expr_type d = BaseT (BytesT (Dynamic cap))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `EVERY (safe_operand s5) xs` mp_tac >>
     qpat_assum `!x. safe_operand s5 x ==> eval_operand x t7 = eval_operand x tk /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `!mem. mem_agree_outside tnK.t_mem tk.vs_memory mem ==> _` mp_tac >>
     disch_then (qspec_then `tk.vs_memory` mp_tac) >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  conj_tac >-
    (qpat_assum `!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> _` mp_tac >> simp[]) >>
  qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _` mp_tac >> simp[]
QED

Theorem raw_call_prefix_prepared_full:
 !DF lo dframe PG tops ctx shadow_ctx func shadow_func cenv env cx ty ann flags
  a d kws st0 sa sb shadow_sa shadow_sb vv addr data len ptr vo go ignored
  gas ov op result s1 s2 s3 s4 s5 s6 s7 xs es s0 G0 tn0 k Q R.
 body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
 body_exprs_full_ok cx (a::d::kws) /\
 body_const_cells_agree [(NONE,tops)] cx env es /\
 expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
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
   expr_sim_inv cenv cx env esK /\ storage_trace_domain cx st0 esK.storage_trace /\
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
   gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (k av (BytesV bs) kvs) (esK,t7,G7,tn7) Q R) ==>
 gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (cx_tops cx) cx st0
   (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (\dv.
       bind (eval_exprs cx kws) (k av dv)))) (es,s0,G0,tn0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  irule (BETA_RULE (Q.ISPEC
    `\i:compile_state. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0` raw_call_prefix_prepared_by_impl)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  first_assum (irule_at (Pat `body_inv _ _ _ _`)) >>
  first_assum (irule_at (Pat `gas_shadow_function _ _`)) >>
  first_assum (irule_at (Pat `gas_shadow_context _ _`)) >>
  first_assum (irule_at (Pat `compile_expr (gas_shadow_env T _) _ _ _ = _`)) >>
  first_assum (irule_at (Pat `return_buf_frame _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_word_args _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ (BaseT AddressT) _ _ = _`)) >>
  qexistsl_tac [`st0`,`lo`,`PG`,`DF`] >>
  simp[raw_call_initial_intro_full,raw_call_neutral_intro_full] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  rpt gen_tac
  >~ [`raw_call_forced_ready _ _ _ _ _ ==> _`]
  >- (rpt strip_tac >> irule raw_call_forced_intro_full >>
      first_assum (irule_at (Pat `raw_call_forced_ready _ _ _ _ _`)) >>
      simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[cj 6 evaluate_storage_trace_frame])
  >~ [`raw_call_kw_ready _ _ _ _ ==> _`]
  >- (strip_tac >> irule raw_call_kw_ready_intro_full >>
      first_assum (irule_at (Pat `raw_call_kw_ready _ _ _ _`)) >> simp[]) >>
  qpat_assum `!gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7. _`
    (mp_tac o SPEC_ALL) >> simp[]
QED
