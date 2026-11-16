(* Conditional composition of the actual prepared raw_call execution. *)
Theory bodyFullRawCallFinishCompose
Ancestors
  bodyFullPreds bodySimFull bodyInvNoDalloca
  bodyFullRawCallCall bodyFullRawCallZero bodyFullRawCallBytes
  bodyFullRawCallTuple bodyFullRawCallFailure
  gasOutcomeFullCompose gasOutcomeFullGuarded exprSimRawCall exprSimWordArgs vyperTypeSystem
  rawCallShapePtr rawCallCountedRun bodyMemRawCallFinish representationCleanPtr
  vyperEvalExprPreservesScopesDom exprSimSource vyperStorageFootprint
Libs
  monadsyntax

(* The three universally closed result-bridge antecedents are inserted here
   when the independently owned literal interfaces are available. *)
Theorem raw_call_finish_from_result_bridges:
 !DF lo dframe PG tops ctx shadow_ctx func shadow_func cenv env cx ty ann flags
  a d kws st0 sa sb shadow_sa shadow_sb vv addr data len ptr vo go ignored
  gas ov op result s1 s2 s3 s4 s5 s6 s7 xs es s0 G0 tn0.
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
 s0.vs_inst_idx=LENGTH sa.cs_current_insts ==>
 !gsA av esA gsD bs esD gsK kvs esK b ob gw tA tD t4 tk t7 G7 tn7.
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
   (cx_tops cx) cx st0
   (do type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
       target <- lift_option_type (dest_AddressV av) "raw_call target";
       data <- lift_option_type (dest_BytesV (BytesV bs)) "raw_call data";
       amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
       eval_raw_call cx flags target data amount
         (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)) od)
   (esK,t7,G7,tn7)
   (\H res ee G tn t. ?tv. res = INL tv /\
     vv_post H ctx func cenv cx (Call ann (RawCallTarget flags) (a::d::kws) NONE)
       es sa sb s0 ee tv vv t /\
     vv_store_bound cx (post_value_type cenv (Call ann (RawCallTarget flags) (a::d::kws) NONE))
       (lowered_value_type cenv (Call ann (RawCallTarget flags) (a::d::kws) NONE)) ee tv vv t /\
     t.vs_current_bb=sb.cs_current_bb /\ t.vs_inst_idx=LENGTH sb.cs_current_insts /\
     alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     s0.vs_alloca_next<=t.vs_alloca_next /\
     ghost_inv_at (DF H) lo dframe cenv cx ee G tn t /\
     ptr_vv_ok cx (post_value_type cenv (Call ann (RawCallTarget flags) (a::d::kws) NONE))
       tv vv ee G tn t /\
     (cenv.ce_is_ctor /\ vv_location vv=SOME LocCode ==>
       ?val. read_result cx tv ee=(INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx)
           (post_value_type cenv (Call ann (RawCallTarget flags) (a::d::kws) NONE))=SOME rt /\
           eval_operand (vv_operand vv) t=SOME w ==>
           w2n w+type_memory_size rt<=lo /\
           (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
             val_in_memory rt val (w2n w) mem)) /\
     (!t' op. vv=StackValue t' op /\
       ~is_word_type (post_value_type cenv (Call ann (RawCallTarget flags) (a::d::kws) NONE)) ==>
       ptr_buf_ok cenv (Call ann (RawCallTarget flags) (a::d::kws) NONE) op G t) /\
     (!t' p. vv=LocatedValue t' p /\ p.ptr_location=LocMemory ==>
       ptr_buf_ok cenv (Call ann (RawCallTarget flags) (a::d::kws) NONE) p.ptr_operand G t) /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
   (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
     (ctx_has_dalloca ctx ==> !s. r=Halt s ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `emit_op ADD [data;Lit 32w] s3 = (dp,s4)` >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace)
     esK.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_all raw_call_prefix_source_ready >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`,`bs`] SUBST1_TAC) >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- suspend "static_value_abort" >>
  `cx.txn.is_static ==> amount = 0` by fs[] >>
  `IS_SOME esK.outcomes /\ outcomes_accounts_typed esK.outcomes /\
   accounts_runtime_well_typed esK.accounts` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  drule_all raw_call_source_tail >>
  disch_then (qspecl_then [`target`,
    `forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)`,`bs`]
    strip_assume_tac) >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7` by
    (rpt conj_tac
     >- metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
                  exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND]
     >- metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
                  exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND]
     >- metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND]
     >- metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND]
     >- (`wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
           (simp[wb_args_shape_def] >> rpt strip_tac >>
            `expr_body_pre cenv cx env e esK /\ is_word_type (expr_type e)` by
              (conj_tac >- metis_tac[expr_body_pre_raw_call_arg, listTheory.MEM] >>
               drule raw_call_kwargs_types >> simp[listTheory.EVERY_MEM] >>
               metis_tac[compileEnvTheory.is_word_type_def]) >>
            drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
         drule_all lower_word_args_shape_ready >>
         simp[exprLoweringPropsTheory.ci_mono_def])
     >- (qpat_x_assum `(case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = (gas,s6)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >> strip_tac >>
         metis_tac[exprLoweringPropsTheory.ci_mono_emit_op,
                   exprLoweringPropsTheory.ci_mono_refl, pairTheory.SND]) >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_raw_call_outbuf, pairTheory.SND]) >>
  `ci_mono sa s7` by
    metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  `local_ptrs_reserved cenv s7` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  Cases_on `emit_op (if flags.rcf_is_static then STATICCALL else CALL)
    (if flags.rcf_is_static then [gas;addr;dp;len;op;Lit (n2w flags.rcf_max_outsize)]
     else [gas;addr;(case vo of NONE => Lit 0w | SOME v => v);dp;len;op;
           Lit (n2w flags.rcf_max_outsize)]) s7` >>
  rename1 `emit_op _ _ s7 = (ok,sc)` >>
  `flags.rcf_max_outsize <= ((flags.rcf_max_outsize+31) DIV 32)*32` by
    (POP_ASSUM_LIST (K all_tac) >>
     mp_tac (arithmeticTheory.DIVISION |> Q.SPEC `32` |> SIMP_RULE (srw_ss()) [] |>
       Q.SPEC `flags.rcf_max_outsize+31`) >> strip_tac >>
     `((flags.rcf_max_outsize+31) MOD 32) < 32` by simp[] >> decide_tac) >>
  `read_memory (w2n (n2w (b+32):bytes32))
     (w2n (n2w (LENGTH bs):bytes32)) t7 = bs` by
    simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
         memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
  `!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
     lb+sz <= (if flags.rcf_max_outsize=0 then ob else ob+32) \/
     (if flags.rcf_max_outsize=0 then ob else ob+32)+flags.rcf_max_outsize <= lb` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     Cases_on `flags.rcf_max_outsize=0` >> simp[] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name)=SOME(ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE=>FEMPTY
       | SOME imms=>get_source_immutables cenv.ce_module imms) name=SOME(tv,v) ==>
     off+type_memory_size tv <= (if flags.rcf_max_outsize=0 then ob else ob+32) \/
     (if flags.rcf_max_outsize=0 then ob else ob+32)+flags.rcf_max_outsize <= off` by
    (rpt strip_tac >>
     qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _` drule >>
     disch_then drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     Cases_on `flags.rcf_max_outsize=0` >> simp[] >> decide_tac) >>
  `?t u. run_inst_seq (emitted_insts s7 sc) t7 = OK u /\
    u = update_var (STRING #"%" (toString s7.cs_next_var))
      (bool_to_word outcome.co_success) t /\
    t = t7 with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion
      (if flags.rcf_max_outsize=0 then ob else ob+32)
      (TAKE flags.rcf_max_outsize outcome.co_returnData) t7).vs_memory /\
    t.vs_returndata = outcome.co_returnData` by
    (map_every (fn q => qpat_x_assum q mp_tac)
      [`emit_op _ _ s7 = (ok,sc)`,
       `stmt_state_rel _ ctx func cenv cx esK t7`,
       `local_ptrs_reserved cenv s7`,
       `eval_operand gas t7 = SOME gw`,
       `eval_operand addr t7 = SOME (w2w target)`,
       `eval_operand dp t7 = SOME _`, `eval_operand len t7 = SOME _`,
       `eval_operand op t7 = SOME _`,
       `eval_operand (case ext_call_kwarg EKValue _ _ of NONE => Lit 0w | SOME x => x) t7 = SOME _`,
       `vo = ext_call_kwarg EKValue _ _`,
       `amount < dimword (:256)`,
       `flags.rcf_is_static ==> amount = 0`,
       `cx.txn.is_static ==> amount = 0`,
       `take_call_outcome _ _ _ esK = _`,
       `read_memory _ _ t7 = bs`,
       `!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> lb+sz <= _ \/ _ <= lb`,
       `cenv.ce_is_ctor ==> !name tv v off. _ ==> off+type_memory_size tv <= _ \/ _ <= off`,
       `ob + (if _ then _ else _) < dimword (:256)`,
       `flags.rcf_max_outsize < dimword (:256)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     qpat_assum `read_memory _ _ t7 = bs` (fn th =>
       qpat_x_assum `take_call_outcome _ _ _ esK = _`
         (assume_tac o ONCE_REWRITE_RULE [GSYM th])) >>
     `(if flags.rcf_max_outsize=0 then ob else ob+32) < dimword (:256)` by
       (Cases_on `flags.rcf_max_outsize=0` >> fs[]) >>
     drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`) raw_call_oracle_emit_run_aged >>
     disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
     disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
     disch_then (qspecl_then
       [`n2w amount`,`n2w (if flags.rcf_max_outsize=0 then ob else ob+32)`,
        `gw`,`w2w target`] mp_tac) >>
     (impl_tac >-
       (`(if flags.rcf_max_outsize=0 then ob else ob+32) < dimword (:256)` by
          (Cases_on `flags.rcf_max_outsize=0` >> fs[]) >>
        `w2w (w2w target : bytes32) = target` by wordsLib.WORD_DECIDE_TAC >>
        Cases_on `flags.rcf_is_static` >> Cases_on `cx.txn.is_static` >>
        fs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> metis_tac[])) >>
     strip_tac >> qexistsl_tac [`t`,`u`] >>
     gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `ci_mono sc sb` by
    (map_every (fn q => qpat_x_assum q mp_tac)
      [`compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s7 = (result,sb)`,
       `emit_op _ _ s7 = (ok,sc)`, `~flags.rcf_is_delegate`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once builtinSystemTheory.compile_raw_call_finish_def,
          Once compileEnvTheory.comp_bind_def] >>
     Cases_on `flags.rcf_is_static` >> fs[] >>
     qmatch_goalsub_abbrev_tac `tail sc = (result,sb)` >> strip_tac >>
     `ci_mono sc (SND (tail sc))` by
       (unabbrev_all_tac >> POP_ASSUM_LIST (K all_tac) >>
        rpt (FIRST [
          CHANGED_TAC (simp[LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
            exprLoweringPropsTheory.ci_mono_emit_op,
            exprLoweringPropsTheory.ci_mono_emit_void,
            exprLoweringPropsTheory.ci_mono_emit_inst,
            exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
            exprLoweringPropsTheory.ci_mono_fresh_label,
            exprLoweringPropsTheory.ci_mono_new_block,
            exprLoweringPropsTheory.ci_mono_compile_select,
            exprLoweringPropsTheory.ci_mono_comp_return]),
          gen_tac,
          ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac,
          ho_match_mp_tac exprLoweringPropsTheory.ci_mono_ignore_bind >> conj_tac,
          IF_CASES_TAC])) >> gvs[]) >>
  `fn_has_code s7 sc func /\ fn_has_code sc sb func` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`emit_op _ _ s7 = (ok,sc)`, `ci_mono sc sb`, `ci_mono sa s7`,
        `fn_has_code sa sb func`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `ci_mono s7 sc` by
       metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND] >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_mid, fragExecTheory.fn_has_code_split,
               compileEnvTheory.cs_extends_trans]) >>
  (* Continue at the fixed actual endpoint, not a fresh semantic witness. *)
  `!j. b+32 <= j /\ j < b+32+LENGTH bs ==> j NOTIN tn7.t_mem` by
    (qpat_x_assum `!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     MATCH_ACCEPT_TAC robust_mem_bytes_at_clean) >>
  `(LENGTH bs <> 0 ==> ?p. dp=Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
   (flags.rcf_max_outsize <> 0 ==> ?p. op=Var p /\ ptr_covers G7 tn7 p t7 flags.rcf_max_outsize)` by
    (map_every (fn q => qpat_x_assum q mp_tac)
      [`LENGTH bs <> 0 ==> ?base sz. op_prov G7 dp = SOME (base,sz) /\ _`,
       `op_prov G7 op = SOME _`, `op_taint tn7 op = {}`,
       `EVERY (\x. op_taint tn7 x = {}) _`,
       `eval_operand dp t7 = SOME _`, `eval_operand op t7 = SOME _`,
       `LENGTH bs < dimword (:256)`, `b+32 < dimword (:256)`,
       `ob + (if _ then _ else _) < dimword (:256)`,
       `flags.rcf_max_outsize <= _` ] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac
     >- (Cases_on `dp` >>
         fs[ptrDisciplineTheory.op_prov_def, bodyPtrDefsTheory.ptr_covers_def,
            venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
            wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
     Cases_on `op` >>
     fs[ptrDisciplineTheory.op_prov_def, bodyPtrDefsTheory.ptr_covers_def,
            venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
        wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  `lo <= ob` by
    (qpat_x_assum `allocas_from lo t7` mp_tac >>
     qpat_x_assum `FLOOKUP t7.vs_allocas s6.cs_next_id = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[]) >>
  `local_ptrs_rel func cenv esK.scopes t7` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `(!x sz. cenv.ce_return_buf=SOME(PtrVar(Var x) sz) ==> not_fresh_at s7 x) /\
   (!x sz. cenv.ce_return_pc=SOME(PtrVar(Var x) sz) ==> not_fresh_at s7 x)` by
    (fs[exprLoweringPropsTheory.ci_mono_def, fragExecTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  qpat_abbrev_tac `inst = mk_inst s7.cs_next_id
    (if flags.rcf_is_static then STATICCALL else CALL)
    (if flags.rcf_is_static then [gas;addr;dp;len;op;Lit(n2w flags.rcf_max_outsize)]
     else [gas;addr;(case vo of NONE=>Lit 0w | SOME v=>v);dp;len;op;Lit(n2w flags.rcf_max_outsize)])
    [STRING #"%" (toString s7.cs_next_var)]` >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t7,G7,tn7) [] (OK(u with vs_inst_idx:=LENGTH sc.cs_current_insts),
        step_prov PG G7 inst u,step_taint inst t7 u tn7)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _` drule >> strip_tac >>
     drule_at (Pat `emit_op _ _ _ = _`) raw_call_actual_call_full >>
     disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     FAIL_TAC "actual full residual") >>
  POP_ASSUM_LIST (K all_tac) >> FAIL_TAC "actual ghost continuation"
QED

Resume raw_call_finish_from_result_bridges[static_value_abort]:
  FAIL_TAC "static bridge application"
QED

Finalise raw_call_finish_from_result_bridges
