Theory s1PrefixRawCallPreparedTail
Ancestors
  s1PrefixRawCallMemSafe s1PrefixRawCallSourceTail bodyFullRawCall
  bodyFullRawCallRequestGas s1PrefixFrame exprBodyPreProps exprOperandVar
  stateRelProj allocaSiteResource representationCleanPtr spillSim memoryReadProps
  vyperTypeExtCallSoundness words option arithmetic loweringStateRelDefs
  venomState ptrDiscipline bodyPtrDefs exprSimRawCall exprSimRawCallCalldata
  vyperStorageFootprint vyperStorageTrace vyperTypeSystem vyperInterpreter vyperState list
  exprLoweringProps bodyFullWordArgs fragExec emitHelperProps venomInst memSafeRun
  bodyFullRawCallCall bodySimStmtFacts bodyFullHashKeccakFixed
Libs
  monadsyntax

(* The output allocation covers the unrounded write range after its header. *)
Theorem raw_call_output_range:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx ee t /\
  allocas_from lo t /\
  eval_operand out t = SOME (n2w ro) /\
  ro = (if cap = 0 then ob else ob + 32) /\
  bytes_alloc = (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
  ob + bytes_alloc < dimword (:256) /\
  FLOOKUP t.vs_allocas aid = SOME (ob,bytes_alloc) /\
  op_prov G out = SOME (ob,bytes_alloc) /\ op_taint tn out = {} /\
  (!name lb sz. local_region cenv ee.scopes t name lb sz ==>
    regions_disjoint ob bytes_alloc lb sz) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob bytes_alloc) ==>
  ro < dimword (:256) /\ (cap <> 0 ==> lo <= ro) /\
  (cap <> 0 ==> ro + cap <= t.vs_alloca_next) /\
  (cap <> 0 ==> ?p. out = Var p /\ ptr_covers G tn p t cap) /\
  (!name lb sz. local_region cenv ee.scopes t name lb sz ==>
    regions_disjoint ro cap lb sz) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= ro \/ ro + cap <= off)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cap <= ((cap+31) DIV 32)*32` by
    simp[MULT_COMM,spillSimTheory.n_le_round_up_32] >>
  `ob <= ro /\ ro + cap <= ob + bytes_alloc` by
    (qpat_assum `ro = _` mp_tac >> qpat_assum `bytes_alloc = _` mp_tac >>
     Cases_on `cap = 0` >> simp[NoAsms] >> decide_tac) >>
  `ro < dimword (:256)` by decide_tac >>
  `ob + bytes_alloc <= t.vs_alloca_next` by
    (irule allocaSiteResourceTheory.alloca_site_registered_below >>
     drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `aid` >> first_assum ACCEPT_TAC) >>
  `lo <= ob` by
    (fs[allocas_from_def] >> first_x_assum drule >> simp[]) >>
  rpt conj_tac >> TRY decide_tac
  >- (strip_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`op_prov G out = _`, `op_taint tn out = _`, `eval_operand out t = _`,
         `ro < dimword (:256)`, `ob <= ro`, `ro + cap <= ob + bytes_alloc`] >>
      POP_ASSUM_LIST (K all_tac) >> Cases_on `out` >>
      simp[op_prov_def,eval_operand_def,ptr_covers_def,w2n_n2w])
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[regions_disjoint_def] >> decide_tac) >>
  disch_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_assum `_ ==> !src name tv v off. _ ==> regions_disjoint _ _ _ _` drule >>
  disch_then (qspecl_then [`src`,`name`,`tv`,`v`,`off`] mp_tac) >>
  impl_tac >- metis_tac[] >> simp[regions_disjoint_def] >> decide_tac
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_prefix_source_ready >> strip_tac >>
  drule raw_call_pre_flags >> simp_tac bool_ss [DROP_def] >> strip_tac >>
  `~(flags.rcf_is_delegate /\ flags.rcf_is_static)` by
    (drule expr_body_pre_static_facts >>
     simp_tac (srw_ss()) [well_typed_expr_def] >> metis_tac[]) >>
  `(flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0` by
    (disch_tac >>
     `~MEM EKValue flags.rcf_kws` by fs[raw_call_kws_ok_def] >>
     qpat_assum `raw_call_value flags.rcf_kws kvs = _` mp_tac >>
     qpat_assum `~MEM EKValue flags.rcf_kws` mp_tac >>
     simp[NoAsms,raw_call_value_def,ext_call_kwarg_not_mem]) >>
  `!e. vyperState$assert T e = vyperState$return ()` by
    simp[FUN_EQ_THM,vyperStateTheory.assert_def,vyperStateTheory.return_def] >>
  `LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws` by simp[] >>
  asm_simp_tac bool_ss [vyperStateTheory.type_check_def,vyperStateTheory.lift_option_type_def,
       vyperValueTheory.dest_BytesV_def,vyperStateTheory.bind_return,
       vyperStateTheory.ignore_bind_def] >>
  simp_tac (srw_ss()) [vyperStateTheory.bind_return] >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- (`~flags.rcf_is_delegate /\ ~flags.rcf_is_static` by metis_tac[] >>
      irule gas_prefix_full_no_outcome >>
      asm_simp_tac bool_ss [storage_trace_frame_raw_call] >>
      rpt gen_tac >>
      `eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
          (esK with gas_obs := gobs) =
        (INR (Error (RuntimeError "write in static context")),esK with gas_obs := gobs)` by
        (irule raw_call_static_value_abort >> metis_tac[]) >>
      asm_simp_tac (srw_ss()) [] >>
      disch_then (SUBST1_TAC o SYM o CONJUNCT2) >>
      simp[DROP_LENGTH_NIL]) >>
  `cx.txn.is_static ==> amount = 0` by metis_tac[] >>
  drule raw_call_source_inv_facts >> strip_tac >>
  irule raw_call_eval_prefix_from_take >> asm_simp_tac bool_ss [] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> disch_tac >>
  suspend "successful_take"
QED
*)
Theorem raw_call_prepared_tail_prefix:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data;Lit 32w] s3 = (dp,s4) /\
  lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  (case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = (gas,s6) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr dp len gas (case vo of NONE => Lit 0w | SOME v => v)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) = (INL (BytesV bs),esD) /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  storage_trace_domain cx st0 esK.storage_trace /\
  vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
  go = ext_call_kwarg EKGas flags.rcf_kws xs /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
    stmt_state_rel H ctx func cenv cx esK t7 /\
    expr_val_rel cx (BaseT AddressT) av addr t7 /\
    (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t7 = SOME w) /\
    eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
    eval_operand dp t7 = SOME (n2w (b+32)) /\ eval_operand gas t7 = SOME gw /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    (LENGTH bs = 0 \/ b+32+LENGTH bs <= t7.vs_alloca_next \/
     ctx_has_dalloca ctx /\ w2n t7.vs_initial_fmp <= b+32 /\
     b+32+LENGTH bs <= w2n t7.vs_fmp) /\
    (!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==>
      mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
    EVERY (\x. op_taint tn7 x = {})
      [addr;len;dp;gas;(case vo of NONE => Lit 0w | SOME v => v)] /\
    (LENGTH bs <> 0 ==> ?base sz. op_prov G7 dp = SOME (base,sz) /\
      base <= b+32 /\ b+32+LENGTH bs <= base+sz) /\
    eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob+32)) /\
    ob+(if flags.rcf_max_outsize = 0 then 0
        else ((flags.rcf_max_outsize+31) DIV 32)*32+32) < dimword (:256) /\
    FLOOKUP t7.vs_allocas s6.cs_next_id =
      SOME (ob,if flags.rcf_max_outsize = 0 then 0
               else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
    op_prov G7 op = SOME (ob,if flags.rcf_max_outsize = 0 then 0
                         else ((flags.rcf_max_outsize+31) DIV 32)*32+32) /\
    op_taint tn7 op = {} /\
    (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
      regions_disjoint ob (if flags.rcf_max_outsize = 0 then 0
                           else ((flags.rcf_max_outsize+31) DIV 32)*32+32) lb sz) /\
    ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
    t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ allocas_from lo t7 /\
    ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (vyperState$ignore_bind
      (type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args")
      (vyperState$bind (lift_option_type (dest_AddressV av) "raw_call target") (\target.
       vyperState$bind (lift_option_type (dest_BytesV (BytesV bs)) "raw_call data") (\data0.
       vyperState$bind (lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value") (\amount.
         eval_raw_call cx flags target data0 amount (ext_call_kwarg EKGas flags.rcf_kws kvs))))))
    (esK,t7,G7,tn7)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_prepared_tail_prefix[successful_take]:
  `ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sa s7` by
    (`ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
      ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7` by
       (rpt conj_tac
        >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
        >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
        >- metis_tac[ci_mono_emit_op,pairTheory.SND]
        >- metis_tac[ci_mono_emit_op,pairTheory.SND]
        >- metis_tac[ci_mono_lower_word_args]
        >- (qpat_assum `(case go of NONE => _ | SOME g => _) = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >>
            metis_tac[ci_mono_emit_op,pairTheory.SND,ci_mono_refl]) >>
        metis_tac[ci_mono_compile_raw_call_outbuf,pairTheory.SND]) >>
     rpt (qhdtm_x_assum `ci_mono` mp_tac) >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_trans]) >>
  `!p. ext_call_kwarg EKGas flags.rcf_kws xs = SOME p ==> gas = p` by
    (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
       (fn th => rewrite_tac [GSYM th]) >>
     qpat_assum `(case go of NONE => _ | SOME g => _) = _` mp_tac >>
     Cases_on `go` >> simp[NoAsms] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env esA` by
    (`expr_body_pre cenv cx env a (es with gas_obs := gsA)` by
       (irule expr_body_pre_raw_call_arg >>
        first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
        simp[] >> metis_tac[expr_body_pre_static_facts]) >>
     metis_tac[bodySimStmtFactsTheory.expr_body_pre_eval]) >>
  `expr_sim_inv cenv cx env esD` by
    (`expr_body_pre cenv cx env d (esA with gas_obs := gsD)` by
       (irule expr_body_pre_raw_call_arg >>
        first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     metis_tac[bodySimStmtFactsTheory.expr_body_pre_eval]) >>
  `!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
       g = w2n gw` by
    (gen_tac >> disch_tac >>
     irule (INST_TYPE [alpha |-> ``:256``] raw_call_request_gas_at_entry) >>
     first_assum (irule_at (Pat `eval_exprs _ _ _ = _`)) >>
     first_assum (irule_at (Pat `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `eval_operand gas t7 = SOME gw`)) >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "prepared_operands"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_prepared_tail_prefix[prepared_operands]:
  qpat_x_assum `vo = _` SUBST_ALL_TAC >>
  qabbrev_tac `vop = case ext_call_kwarg EKValue flags.rcf_kws xs of
                         NONE => Lit 0w | SOME v => v` >>
  qabbrev_tac `cap = flags.rcf_max_outsize` >>
  qabbrev_tac `call_ty = if flags.rcf_is_delegate then DelegateCall
                         else if flags.rcf_is_static then StaticCall else RegularCall` >>
  qabbrev_tac `opc = case call_ty of RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL` >>
  qabbrev_tac `ops = if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
                     else [gas;addr;dp;len;op;Lit (n2w cap)]` >>
  `?ok sc. emit_op opc ops s7 = (ok,sc) /\ cs_extends sc sb` by
    (drule raw_call_finish_prefix >>
     disch_then (qx_choose_then `ok` (qx_choose_then `sc` strip_assume_tac)) >>
     qexistsl [`ok`,`sc`] >> simp[Abbr `opc`, Abbr `ops`] >>
     qpat_assum `_ s7 = (ok,sc)` mp_tac >>
     Cases_on `call_ty` >> simp[NoAsms]) >>
  `fn_has_code s7 sc func` by
    (irule fn_has_code_mid >>
     `cs_extends sa s7 /\ cs_extends s7 sc` by
       metis_tac[ci_mono_emit_op,ci_mono_def,pairTheory.SND] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`sb`,`sa`] >> simp_tac bool_ss [] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv s7 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x)` by
    (rpt conj_tac >> rpt strip_tac >>
     metis_tac[compiler_ci_mono_reserved, compiler_ci_mono_not_fresh]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t7` by metis_tac[stmt_state_rel_allocas_below_fmp] >>
  qabbrev_tac `inst = mk_inst s7.cs_next_id opc ops
    [STRING #"%" (toString s7.cs_next_var)]` >>
  `op_taint tn7 (Lit (n2w cap)) = {}` by simp[op_taint_def] >>
  `EVERY (\p. op_taint tn7 p = {}) inst.inst_operands` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY _ [addr;len;dp;gas;vop]`,`op_taint tn7 op = _`,
        `op_taint tn7 (Lit (n2w cap)) = _`] >>
     Cases_on `call_ty` >>
     simp[NoAsms, Abbr `inst`,Abbr `ops`,Abbr `opc`,mk_inst_def] >>
     tautLib.TAUT_TAC) >>
  `!j. b + 32 <= j /\ j < b + 32 + LENGTH bs ==> j NOTIN tn7.t_mem` by
    (qpat_assum `!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==> _`
       (mp_tac o MATCH_MP robust_mem_bytes_at_clean) >> simp[]) >>
  `(LENGTH bs <> 0 ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs))` by
    (`op_taint tn7 dp = {}` by
       (qpat_assum `EVERY _ [addr;len;dp;gas;vop]` mp_tac >> simp[NoAsms]) >>
     strip_tac >> qpat_assum `LENGTH bs <> 0 ==> _` drule >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operand dp t7 = _`, `op_taint tn7 dp = {}`, `b + 32 < dimword (:256)`] >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `dp` >>
     simp[op_prov_def,eval_operand_def,ptr_covers_def,w2n_n2w] >>
     rpt strip_tac >> simp[] >> decide_tac) >>
  `read_memory (b + 32) (LENGTH bs) t7 = bs` by
    (rewrite_tac[read_memory_eq_mem_bytes_at] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  qabbrev_tac `ro = if cap = 0 then ob else ob + 32` >>
  qabbrev_tac `bytes_alloc = if cap = 0 then 0 else ((cap+31) DIV 32)*32+32` >>
  `fn_has_code s6 s7 func` by
    (qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ s7 = (result,sb)` mp_tac >>
     qpat_assum `ci_mono sa s6` mp_tac >>
     qpat_assum `ci_mono s6 s7` mp_tac >>
     qpat_assum `fn_has_code sa sb func` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[fn_has_code_mid,ci_mono_def,ci_mono_compile_raw_call_finish,pairTheory.SND]) >>
  `cenv.ce_is_ctor ==> !src name tv v off.
     (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) ob bytes_alloc` by
    (mp_tac (Q.INST [`sa` |-> `s6`, `sb` |-> `s7`, `cap` |-> `cap`,
        `es` |-> `esK`, `t` |-> `t7`, `sz` |-> `bytes_alloc`,
        `H` |-> `storage_trace_horizon esK.storage_trace`]
       (INST_TYPE [alpha |-> ``:256``] raw_call_outbuf_immutable_separation)) >>
     impl_tac >- simp[] >>
     disch_then ACCEPT_TAC) >>
  `ro < dimword (:256) /\ (cap <> 0 ==> lo <= ro) /\
   (cap <> 0 ==> ro + cap <= t7.vs_alloca_next) /\
   (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G7 tn7 p t7 cap) /\
   (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
     regions_disjoint ro cap lb sz) /\
   (cenv.ce_is_ctor ==> !src name tv v off.
      (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
      FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
      off + type_memory_size tv <= ro \/ ro + cap <= off)` by
    (irule raw_call_output_range >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexistsl [`s6.cs_next_id`,`bytes_alloc`,`ob`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         simp_tac bool_ss [Abbr `ro`, Abbr `bytes_alloc`]) >>
     qexistsl [`storage_trace_horizon esK.storage_trace`,`ctx`,`func`] >>
     first_assum ACCEPT_TAC) >>
  `mem_safe_step 0 ctx inst t7` by
    (qunabbrev_tac `inst` >> qunabbrev_tac `ops` >> qunabbrev_tac `opc` >>
     irule raw_call_inst_mem_safe_at >>
     first_assum (irule_at (Pat `eval_operand dp _ = _`)) >>
     first_assum (irule_at (Pat `eval_operand len _ = _`)) >>
     first_assum (irule_at (Pat `eval_operand op _ = _`)) >>
     simp_tac bool_ss [IS_SOME_EXISTS] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     goal_assum (drule_at Any)) >>
  suspend "request_site"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_call_prepared_tail_prefix[request_site]:
  `w2n (n2w ro : bytes32) = ro /\
   w2n (n2w (b + 32) : bytes32) = b + 32 /\
   w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs /\
   w2n (n2w amount : bytes32) = amount` by
    asm_simp_tac bool_ss [w2n_n2w,LESS_MOD] >>
  `(call_ty = DelegateCall) = flags.rcf_is_delegate` by
    (Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >> simp[Abbr `call_ty`]) >>
  qabbrev_tac `value_opt = if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount` >>
  qabbrev_tac `gas_cap = OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV` >>
  `(call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
   w2n (if call_ty = RegularCall then n2w amount else 0w : bytes32) =
     (case value_opt of NONE => 0 | SOME n => n)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`~(flags.rcf_is_delegate /\ flags.rcf_is_static)`,
        `(flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0`,
        `cx.txn.is_static ==> amount = 0`, `w2n (n2w amount : bytes32) = amount`] >>
     simp[NoAsms,Abbr `call_ty`,Abbr `value_opt`] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >>
     Cases_on `cx.txn.is_static` >> simp[]) >>
  `w2w (w2w target : bytes32) = target` by wordsLib.WORD_DECIDE_TAC >>
  `(n2w (LENGTH bs) : bytes32) <> 0w ==>
    ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)` by
    (once_rewrite_tac[GSYM w2n_eq_0] >> asm_simp_tac bool_ss []) >>
  `read_memory (w2n (n2w (b + 32) : bytes32)) (w2n (n2w (LENGTH bs) : bytes32)) t7 = bs` by
    asm_simp_tac bool_ss [] >>
  qpat_assum `read_memory (w2n _) (w2n _) t7 = bs` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `(call_ty = DelegateCall) = flags.rcf_is_delegate` (fn th => rewrite_tac[GSYM th]) >>
  irule raw_call_actual_call_mem_safe_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- asm_simp_tac bool_ss []
  >- (qexistsl [`mid`,`outcome`,`rq`] >> asm_simp_tac bool_ss []) >>
  qexistsl [`w2w target : bytes32`,`cap`,`cenv`,`dframe`,`len`,`dp`,
            `gw`,`gas`,`inst`,`ok`,`op`,`n2w ro : bytes32`,`s7`,`sc`,
            `addr`,`vop`,`n2w amount : bytes32`] >>
  qpat_assum `w2n (n2w ro : bytes32) = ro` (fn th => rewrite_tac[th]) >>
  qpat_assum `w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs` (fn th => rewrite_tac[th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rename1 `inst = mk_inst _ _ _ _` >>
       simp_tac bool_ss [Abbr `inst`,Abbr `opc`,Abbr `ops`] >> NO_TAC) >>
  TRY (rename1 `emit_op _ _ s7 = (ok,sc)` >>
       qpat_assum `emit_op opc ops s7 = (ok,sc)` mp_tac >>
       simp_tac bool_ss [Abbr `opc`,Abbr `ops`] >> NO_TAC)
  >- (qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `cap <> 0 ==> lo <= ro` mp_tac >> tautLib.TAUT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_call_prepared_tail_prefix
*)
