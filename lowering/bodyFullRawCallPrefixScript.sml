(* A single prepared execution for the raw_call arguments and buffers. *)
Theory bodyFullRawCallPrefix
Ancestors
  bodyFullPreds bodySimFull bodyFullWordArgs bodyInvNoDalloca
  bodyFullRawCallHeader bodyFullRawCallGas bodyFullRawCallOutbuf
  bodyFullRawCallGeneratedPrefix bodyFullRawCallKwargsBytes bodyFullRawCallKwargsSource
  gasOutcomeFullCompose gasOutcomeFullGuarded rawCallShapePtr exprSimRawCall
  exprSimSource wordArgsPtr gasShadowCompileStmtHelpers gasShadowCompileHelpers
  gasShadowState gasShadowCompileBuiltinSystem representationCleanPtr gasExemptCert
  vyperEvalExprPreservesScopesDom exprLoweringProps exprSimWordArgs fragExec list gasShadow vyperStorageTrace

Theorem raw_call_prefix_prepared_full:
 !DF lo dframe PG tops ctx shadow_ctx func shadow_func cenv env cx ty ann flags
  a d kws st0 sa sb shadow_sa shadow_sb vv addr data len ptr vo go ignored
  gas ov op result s1 s2 s3 s4 s5 s6 s7 xs es s0 G0 tn0 k Q R.
 body_inv tops ctx cenv cx /\
 body_exprs_full_ok cx (a::d::kws) /\
 expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
 compile_expr cenv ty (Call ann (RawCallTarget flags) (a::d::kws) NONE) sa=(vv,sb) /\
 compile_expr cenv ty
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
 (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
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
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `?h1. lower_value compile_expr cenv (BaseT AddressT) (gas_shadow_expr a)
       shadow_sa = (addr,h1) /\ gas_shadow_state s1 h1` by
    (mp_tac (Q.INST [`ty` |-> `BaseT AddressT`, `e` |-> `a`]
       gas_shadow_stmt_lower_value) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `?h2. lower_value compile_expr cenv (expr_type d) (gas_shadow_expr d)
       h1 = (data,h2) /\ gas_shadow_state s2 h2` by
    (mp_tac (Q.INST [`ty` |-> `expr_type d`, `e` |-> `d`]
       gas_shadow_stmt_lower_value) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`, `h1`] mp_tac) >>
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
     (compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws
       (MAP gas_shadow_expr kws))` by
    (irule (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwargs
              |> SIMP_RULE (srw_ss()) []) >>
     simp[cj 1 gasShadowCompileTheory.gas_shadow_compile_expr]) >>
  `?h5. compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws
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
    (drule_all rawCallShapePtrTheory.raw_call_kwargs_word_args >>
     strip_tac >> gvs[]) >>
  `!todo. gas_shadow_compiles
     (lower_word_args cenv (K (BaseT (UintT 256))) todo)
     (lower_word_args cenv (K (BaseT (UintT 256))) (MAP gas_shadow_expr todo))` by
    (POP_ASSUM_LIST (K all_tac) >>
     Induct >> simp[exprSimWordArgsTheory.lower_word_args_def,listTheory.MAP,
                    gas_shadow_compiles_return] >>
     gen_tac >> irule gas_shadow_compiles_bind >>
     simp[gas_shadow_stmt_lower_value] >>
     gen_tac >> irule gas_shadow_compiles_bind >>
     simp[gas_shadow_compiles_return]) >>
  `lower_word_args cenv (K (BaseT (UintT 256)))
     (MAP gas_shadow_expr kws) h4 = (xs,h5)` by
    (drule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)
       rawCallShapePtrTheory.raw_call_kwargs_word_args >>
     simp[] >> strip_tac >>
     qpat_x_assum `!todo. gas_shadow_compiles _ _`
       (mp_tac o Q.SPECL [`s4`,`h4`] o
        REWRITE_RULE [gas_shadow_compiles_def] o Q.SPEC `kws`) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `!todo x y ops. lower_word_args cenv (K (BaseT (UintT 256))) todo x = (ops,y) ==>
     ci_mono x y` by
    (POP_ASSUM_LIST (K all_tac) >> Induct >>
     simp[lower_word_args_nil,ci_mono_refl] >> rpt gen_tac >>
     rw[lower_word_args_cons] >>
     metis_tac[ci_mono_lower_value_compile_expr,ci_mono_trans,pairTheory.SND]) >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\ ci_mono s7 sb` by
    (rpt conj_tac
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
     >- metis_tac[ci_mono_emit_op,pairTheory.SND]
     >- metis_tac[ci_mono_emit_op,pairTheory.SND]
     >- metis_tac[]
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
     >- metis_tac[]
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
  irule gas_outcome_full_initial_domain >> conj_tac
  >- (match_mp_tac storage_trace_frame_bind_all >> conj_tac
      >- (match_mp_tac storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> match_mp_tac storage_trace_frame_bind_all >> conj_tac
      >- (match_mp_tac storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> match_mp_tac storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `expr_sim_inv cenv cx env es` by
    (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >> simp[]) >>
  `expr_body_pre cenv cx env a es` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `expr_sim_full (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT AddressT) a es` by
    (`body_expr_full_ok cx a` by
       (qpat_assum `body_exprs_full_ok _ _`
          (mp_tac o REWRITE_RULE [Once body_exprs_full_ok_def]) >>
        simp[NoAsms] >> metis_tac[]) >>
     drule (cj 1 (iffLR (CONJUNCT1 body_expr_full_ok_def))) >>
     metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ a _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`h1`,`addr`,
                          `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qabbrev_tac `P = (\e ei ca cb t0 Gi tni x H
      (res : value + vyperState$exception) ee G tn t.
    (?v. res = INL v /\ expr_post H ctx func cenv cx e ei ca cb t0 ee v x t /\
      expr_store_bound cx (post_value_type cenv e) v x t /\
      t.vs_current_bb = cb.cs_current_bb /\
      t.vs_inst_idx = LENGTH cb.cs_current_insts /\ alloca_history func t /\
      t0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
      ghost_kept_at lo cenv ei ca Gi tni t0 G tn) /\
    ~t.vs_halted /\ ee.gas_obs = [])` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[]) 
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> match_mp_tac storage_trace_frame_bind_all >> conj_tac
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame]) >>
  qexists_tac `P a es sa s1 s0 G0 tn0 addr` >> reverse conj_tac
  >- (BETA_TAC >> irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[Abbr `P`,NoAsms] >>
      qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
      qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >>
      first_x_assum irule >>
      gvs[stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  qx_genl_tac [`marksA`,`resA`,`esA`,`GA`,`tnA`,`tA`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esA.storage_trace)
     esA.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 esA.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H esA.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esA.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (P = _)`
    (fn th => simp[REWRITE_RULE [markerTheory.Abbrev_def] th,NoAsms]) >>
  strip_tac >> simp[] >>
  `esA with gas_obs := [] = esA` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `resA = INL _` SUBST_ALL_TAC >>
  rename1 `expr_store_bound cx (post_value_type cenv a) av addr tA` >>
  `expr_sim_inv cenv cx env esA` by
    (qpat_assum `bind (eval_expr cx a) (read_result cx) _ = _` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env a es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env d esA` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `body_expr_full_ok cx d` by
    (qpat_assum `body_exprs_full_ok _ _`
       (mp_tac o REWRITE_RULE [body_exprs_full_ok_def]) >>
     qpat_assum `bind (eval_expr cx a) (read_result cx) _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[vyperStateTheory.bind_def,AllCaseEqs()] >>
     metis_tac[]) >>
  `expr_sim_full (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type d) d esA` by
    (drule (cj 1 (iffLR (CONJUNCT1 body_expr_full_ok_def))) >> metis_tac[]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `ci_mono sa s1` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `return_buf_frame dframe cenv s1 tA` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[NoAsms] >> strip_tac >> simp[]) >>
  `!fn inst s. frag_reachable ctx func tA fn inst s ==> dalloca_no_wrap inst s` by
    (qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all contextRawReachableTheory.frag_reachable_members >> strip_tac >>
     fs[ptrDisciplineTheory.ctx_has_dalloca_def,EXISTS_MEM,
        unitMemInvTheory.dalloca_no_wrap_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H esA.storage_trace ==>
     stmt_state_rel H ctx func cenv cx esA tA /\
     storage_well_formed_on cx esA (FST H) /\
     ghost_inv_at (DF H) lo dframe cenv cx esA GA tnA tA` by
    (qpat_assum `!H. valid_horizon _ _ H esA.storage_trace ==> _` mp_tac >>
     simp[Abbr `P`,NoAsms] >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> first_x_assum drule >>
     simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx d) (read_result cx)) expr_res_ok esA` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ d _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`s1`,`s2`,`h1`,`h2`,`data`,
                          `tA`,`GA`,`tnA`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame]) >>
  qexists_tac `P d esA s1 s2 tA GA tnA data` >> reverse conj_tac
  >- (BETA_TAC >> irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx d) _) _ _ _`
        (irule_at Any) >>
      simp[Abbr `P`,NoAsms] >>
      qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
      qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >>
      first_x_assum irule >>
      gvs[stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  qx_genl_tac [`marksD`,`resD`,`esD`,`GD`,`tnD`,`tD`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace)
     esD.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 esD.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esD.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (P = _)`
    (fn th => simp[REWRITE_RULE [markerTheory.Abbrev_def] th,NoAsms]) >>
  strip_tac >> simp[] >>
  `esD with gas_obs := [] = esD` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `!tail. bind (eval_expr cx d) _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `resD = INL _` SUBST_ALL_TAC >>
  rename1 `expr_store_bound cx (post_value_type cenv d) dv data tD` >>
  `expr_sim_inv cenv cx env esD /\ expr_result_typed env d (Value dv)` by
    (qpat_assum `bind (eval_expr cx d) (read_result cx) _ = _` mp_tac >>
     qpat_assum `expr_body_pre cenv cx env d esA` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  `?bs. dv = BytesV bs` by
    (qpat_assum `expr_result_typed env d (Value dv)` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperValueTheory.evaluate_type_def,
          vyperTypeInvariantsTheory.value_result_typed_def,
          vyperTypingTheory.value_has_type_def] >>
     Cases_on `dv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `dv = BytesV bs` SUBST_ALL_TAC >>
  `post_value_type cenv d = expr_type d` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  `evaluate_type (get_tenv cx) (post_value_type cenv d) =
     SOME (BaseTV (BytesT (Dynamic cap))) /\
   ~is_word_type (post_value_type cenv d)` by
    (qpat_assum `expr_result_typed env d (Value (BytesV bs))` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     qpat_assum `post_value_type cenv d = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperValueTheory.evaluate_type_def,compileEnvTheory.is_word_type_def]) >>
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
     qpat_assum `stmt_state_rel _ _ _ _ _ esD tD` mp_tac >>
     qpat_assum `evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))` mp_tac >>
     qpat_assum `~is_word_type (post_value_type cenv d)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringPostsTheory.expr_val_rel_def,exprSimMemDefsTheory.expr_store_bound_def,
          exprLoweringPropsTheory.stmt_state_rel_def,exprLoweringPropsTheory.alloca_room_def] >>
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
  drule_all raw_call_header_joint >>
  disch_then (qspecl_then [`PG`,`esD`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `t4 = th with vs_inst_idx := LENGTH s4.cs_current_insts` >>
  irule (Q.INST [`n` |-> `0`, `s1` |-> `t4`, `G1` |-> `G4`,
                  `tn1` |-> `tn4`] raw_call_generated_prefix_full) >>
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G4`,`t4`,`tn4`] >> conj_tac
  >- (simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
     stmt_state_rel H ctx func cenv cx esD t4 /\
     storage_well_formed_on cx esD (FST H) /\
     ghost_inv_at (DF H) lo dframe cenv cx esD G4 tn4 t4` by
    (qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _` mp_tac >>
     qpat_assum `!H D d. stmt_state_rel _ _ _ _ _ _ tD /\ _ ==> _` mp_tac >>
     simp[Abbr `P`,NoAsms] >> POP_ASSUM_LIST (K all_tac) >>
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
     >- (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     `expr_type e = BaseT (UintT 256)` by
       (qpat_assum `EVERY (\e. expr_type e = _) kws`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `e` mp_tac) >> simp[]) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `body_exprs_full_ok cx kws` by
    (qpat_assum `body_exprs_full_ok cx (a::d::kws)`
       (mp_tac o REWRITE_RULE [body_exprs_full_ok_def]) >>
     qpat_assum `bind (eval_expr cx a) (read_result cx) _ = _` mp_tac >>
     qpat_assum `bind (eval_expr cx d) (read_result cx) _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperStateTheory.bind_def,AllCaseEqs()] >> metis_tac[]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z)` by
    (qpat_assum `ci_mono s2 s3` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s3 s4` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     rpt strip_tac >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
  mp_tac (Q.SPECL [`kws`,`DF`,`lo`,`dframe`,`ctx`,`shadow_ctx`,`PG`,`tops`,
     `func`,`shadow_func`,`cenv`,`env`,`cx`,`BaseT (UintT 256)`,
     `esD`,`st0`,`s4`,`s5`,`h4`,`h5`,`xs`,`t4`,`G4`,`tn4`]
     lower_word_args_sim_full) >>
  (impl_tac >- (simp[combinTheory.K_DEF] >> metis_tac[])) >> strip_tac >>
  qabbrev_tac `PK = (\H (rr : value list + vyperState$exception) mid G tn t.
    (?vs. rr = INL vs /\
      typed_args_post H ctx func cenv cx esD s4 t4 mid kws xs vs t /\
      t.vs_current_bb = s5.cs_current_bb /\
      t.vs_inst_idx = LENGTH s5.cs_current_insts /\
      alloca_history func t /\ t4.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx mid G tn t /\
      ghost_kept_at lo cenv esD s4 G4 tn4 t4 G tn /\
      EVERY (\x. op_taint tn x = {}) xs) /\ ~t.vs_halted /\ mid.gas_obs = [])` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_values >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[] >>
  qexists_tac `PK` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx kws) _ _ _` (irule_at Any) >>
      simp[Abbr `PK`,NoAsms] >>
      qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      Cases_on `res` >> gvs[exprSimWordArgsTheory.wb_args_exit_def] >>
      first_x_assum irule >>
      gvs[stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  qx_genl_tac [`marksK`,`resK`,`esK`,`GK`,`tnK`,`tk`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace)
     esK.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 esK.storage_trace`
       (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (PK = _)`
    (fn th => simp[REWRITE_RULE [markerTheory.Abbrev_def] th,NoAsms]) >>
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
    (qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _` mp_tac >>
     simp[Abbr `PK`,NoAsms] >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> first_x_assum drule >>
     simp[exprSimPrecompilesTheory.typed_args_post_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
     valid_horizon cx st0 H esD.storage_trace` by
    (qpat_assum `eval_exprs cx kws _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `storage_trace_frame (eval_exprs cx kws)` by simp[evaluate_storage_trace_frame] >>
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
  `stmt_state_rel (storage_trace_horizon esA.storage_trace) ctx func cenv cx esA tA` by
    (qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >> simp[]) >>
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
         qexistsl_tac [`t`,`G6`,`tn6`,`gw`,`1`] >> simp[] >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         `REPLICATE 1 F = [F]` by EVAL_TAC >> simp[] >> metis_tac[]) >>
     qpat_assum `(case SOME _ of NONE => _ | SOME _ => _) = (gas,s6)` mp_tac >>
     simp_tac std_ss [] >> disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) >>
     qpat_assum `!g. SOME _ = SOME g ==> _` (qspec_then `gas` mp_tac) >>
     simp_tac std_ss [] >> strip_tac >>
     qexistsl_tac [`tk`,`GK`,`tnK`,`w`,`0`] >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
     metis_tac[]) >>
  irule (Q.INST [`s1` |-> `t6`, `G1` |-> `G6`, `tn1` |-> `tn6`, `n` |-> `n`]
    raw_call_generated_prefix_full) >> simp[] >>
  qexistsl_tac [`G6`,`n`,`t6`,`tn6`] >>
  (conj_tac >- (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
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
     drule rawCallShapePtrTheory.raw_call_pre_flags >> strip_tac >>
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
  FAIL_TAC "outbuf frames"
QED
