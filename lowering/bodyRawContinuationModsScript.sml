(* Assemble the linked continuation at the actual fetched CALL endpoint. *)
Theory bodyRawContinuationMods
Ancestors
  bodyRawFetchedEntryMods bodyRawEarlyAbortMods bodyRawOracleSourceMods
  bodyRawNormalLandingMods bodyRawLandingFrameMods bodyRawLandedBufferMods
  bodyRawMandatoryRevertMods bodyRawZeroResultMods bodyRawBufferedResultMods
  gasOutcomeFullPostMods stateRelProj vyperStorageFootprint
  bodyFullPostsMods bodyFullPredsMods exprSimRawCall exprLoweringProps exprOperandVar
  bodyPtrDefs fragGasOriginPtr loweringPosts loweringStateRelDefs
  vyperTypeSystem vyperCallOutcome vyperState venomInst venomState words list arithmetic

val raw_cap = ``flags.rcf_max_outsize``;
val raw_size = ``if ^raw_cap = 0 then 0 else 32 * ((^raw_cap + 31) DIV 32) + 32``;
val raw_value = ``case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME p => p``;
val raw_gas = ``ext_call_kwarg EKGas flags.rcf_kws (kvs : value list)``;
val raw_kind = ``if flags.rcf_is_delegate then DelegateCall
  else if flags.rcf_is_static then StaticCall else RegularCall``;
val raw_inputs = ``[addr;len;dp;gas;^raw_value]``;
val raw_operands = ``[addr;len;dp;gas;^raw_value;ov;op]``;

val raw_normal = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + vyperState$exception) ee G tn t. ?tv. res = INL tv /\
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo dframe cenv cx ee G tn t /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
       ~is_bytestring_type (post_value_type cenv e) ==>
       vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
             eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  (!t' p. vv = StackValue t' p /\ ~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e p G t) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==> ptr_buf_ok cenv e p.ptr_operand G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val raw_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Theorem raw_call_continuation_full_mods:
  !mods DF lo dframe ctx shadow_ctx PG func cenv cx env e es flags
    st0 sa sb vv s0 G0 tn0 s6 sout s7 addr dp len gas xs kvs ov op result
    target bs amount gw ib ob esK t7 G7 tn7.
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\ expr_type e = raw_call_return_type flags /\
  type_alloc_ok cenv (expr_type e) /\ ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\ (flags.rcf_is_static ==> amount = 0) /\
  amount < dimword (:256) /\ ^raw_cap < dimword (:256) /\
  expr_sim_inv_mods mods cenv cx env esK /\ esK.gas_obs = [] /\
  storage_trace_domain cx st0 esK.storage_trace /\
  fn_has_code sa sb func /\ fn_has_code s6 sout func /\ fn_inst_ids_distinct func /\
  ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\ ci_mono sa s7 /\
  compile_raw_call_outbuf ^raw_cap s6 = ((ov,op),sout) /\
  compile_raw_call_finish addr dp len gas ^raw_value ^raw_kind ^raw_cap flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  vv = (if ^raw_cap = 0 then StackValue (raw_call_return_type flags) result
        else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
     stmt_state_rel H ctx func cenv cx esK t7 /\ immutable_frame_mods func cenv cx esK t7 /\
     storage_well_formed_on cx esK (FST H) /\ ghost_inv_at_mods (DF H) lo dframe cenv cx esK G7 tn7 t7) /\
  return_buf_frame dframe cenv sa t7 /\ wb_frame cenv es esK sa s0 t7 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
  ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
  t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
  s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next /\ allocas_from lo t7 /\
  eval_operand addr t7 = SOME (w2w target) /\ eval_operand ^raw_value t7 = SOME (n2w amount) /\
  eval_operand gas t7 = SOME gw /\ (!g. OPTION_BIND ^raw_gas dest_NumV = SOME g ==> g = w2n gw) /\
  eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
  ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\ w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
  read_memory ib (LENGTH bs) t7 = bs /\ (!j. ib <= j /\ j < ib + LENGTH bs ==> j NOTIN tn7.t_mem) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
  eval_operand ov t7 = SOME (n2w ob) /\ eval_operand op t7 = SOME (n2w (if ^raw_cap = 0 then ob else ob + 32)) /\
  (^raw_cap = 0 ==> ov = op) /\ ob + ^raw_size < dimword (:256) /\
  FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,^raw_size) /\
  op_prov G7 ov = SOME (ob,^raw_size) /\ op_prov G7 op = SOME (ob,^raw_size) /\
  op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> regions_disjoint ob ^raw_size lb sz) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob ^raw_size) /\
  EVERY (\x. op_taint tn7 x = {}) ^raw_inputs /\ EVERY (safe_operand s7) ^raw_operands /\
  (!x. MEM (Var x) ^raw_operands ==> not_fresh_at s7 x) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_raw_call cx flags target bs amount ^raw_gas) (esK,t7,G7,tn7) ^raw_normal ^raw_exit
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon esK.storage_trace` >>
  `valid_horizon cx st0 H0 esK.storage_trace` by
    simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> stmt_state_rel H _ _ _ _ esK t7 /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  qabbrev_tac `cap = ^raw_cap` >> qabbrev_tac `vop = ^raw_value` >>
  qabbrev_tac `ct = ^raw_kind` >> qabbrev_tac `gkw = ^raw_gas` >>
  drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)
    (INST_TYPE [alpha |-> ``:word8``] raw_call_fetched_entry_mods) >>
  disch_then (drule_at (Pat `fn_has_code sa sb func`)) >>
  disch_then (drule_at (Pat `FLOOKUP t7.vs_allocas s6.cs_next_id = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand addr t7 = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand gas t7 = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand dp t7 = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand len t7 = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand vop t7 = SOME _`)) >>
  disch_then (drule_at (Pat `op_prov G7 op = SOME _`)) >>
  disch_then (drule_at (Pat `allocas_from lo t7`)) >>
  disch_then (drule_at (Pat `local_ptrs_reserved cenv sa`)) >>
  disch_then (qspec_then `tn7` mp_tac) >>
  disch_then (qspec_then `esK` mp_tac) >>
  disch_then (qspec_then `cx` mp_tac) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (qspec_then `w2w (target:160 word)` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `ok` (qx_choose_then `sc` (qx_choose_then `inst`
    (qx_choose_then `bb` (map_every assume_tac o CONJUNCTS))))) >>
  `t7.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) stmt_state_rel_state_rel >>
     simp[NoAsms,call_ctx_rel_def]) >>
  `esK.outcomes = SOME t7.vs_outcomes` by
    (drule stmt_state_rel_state_rel >> simp[NoAsms,state_rel_def]) >>
  qabbrev_tac `ro = if cap = 0 then ob else ob + 32` >>
  `w2n (n2w cap : bytes32) = cap /\ w2n (n2w ib : bytes32) = ib /\
   w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs /\
   w2n (n2w amount : bytes32) = amount` by simp[w2n_n2w] >>
  `cap <> 0 ==> ?p. op = Var p /\ ptr_covers G7 tn7 p t7 cap` by
    (disch_tac >> first_x_assum (drule_then strip_assume_tac) >> metis_tac[]) >>
  Cases_on `t7.vs_outcomes = [] \/ (cx.txn.is_static /\ amount <> 0)`
  >- (qunabbrev_tac `cap` >> irule raw_call_early_abort_outcome_mods >>
      `!H. valid_horizon cx st0 H esK.storage_trace ==> stmt_state_rel H ctx func cenv cx esK t7` by
        (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
      asm_rewrite_tac[] >>
      qexistsl [`addr`,`bb`,`ct`,`len`,`dp`,`gas`,`gw`,`s7.cs_next_id`,`inst`,
                `n2w ib`,`n2w (LENGTH bs)`,`op`,`STRING #"%" (toString s7.cs_next_var)`,
                `n2w ro`,`vop`] >>
      asm_simp_tac bool_ss [Abbr `ct`, GSYM w2n_eq_0] >>
      qpat_x_assum `get_instruction bb t7.vs_inst_idx = SOME inst` mp_tac >>
      asm_rewrite_tac[]) >>
  `(cx.txn.is_static ==> amount = 0) /\ esK.outcomes <> SOME []` by
    (qpat_x_assum `~(t7.vs_outcomes = [] \/ _)` mp_tac >>
     Cases_on `cx.txn.is_static` >> simp[]) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==> storage_well_formed_on cx esK (FST H)` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
         (drule_then strip_assume_tac)) >>
  drule_at (Pat `expr_sim_inv_mods mods cenv cx env esK`) raw_call_oracle_source_mods >>
  disch_then (drule_at (Pat `~(flags.rcf_is_delegate /\ flags.rcf_is_static)`)) >>
  disch_then (drule_at (Pat `cx.txn.is_static ==> amount = 0`)) >>
  disch_then (qspecl_then [`target`,`st0`,`gkw`,`bs`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `rq` (qx_choose_then `outcome` (qx_choose_then `es1`
    (qx_choose_then `es2` (map_every assume_tac o CONJUNCTS))))) >>
  suspend "normal_landing"
QED

Resume raw_call_continuation_full_mods[normal_landing]:
  `cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) ro cap` by
    (rpt strip_tac >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_mods_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `bare_globals_layout _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [exprSimHypsDefsTheory.bare_globals_layout_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!src id off. FLOOKUP _ _ = SOME (ImmutableLoc off) ==> _`
       (drule_then strip_assume_tac) >>
     drule_all_then strip_assume_tac vyperTypeInvariantsTheory.env_consistent_bare_global_find_NONE >>
     `ALOOKUP cenv.ce_modules cenv.ce_module = SOME ts` by
       (qpat_assum `!src. ALOOKUP cenv.ce_modules src = _` (qspec_then `cenv.ce_module` mp_tac) >> simp[]) >>
     qpat_assum `cenv.ce_is_ctor ==> !src tops name tv v off. _ ==> regions_disjoint _ _ ro cap`
       (drule_then (drule_all_then ACCEPT_TAC))) >>
  qabbrev_tac `value_opt = if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount` >>
  `w2n (if ct = RegularCall then n2w amount : bytes32 else 0w) =
      (case value_opt of NONE => 0 | SOME n => n)` by
    (Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >>
     Cases_on `cx.txn.is_static` >> fs[Abbr `ct`,Abbr `value_opt`]) >>
  `(ct = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt` by
    (Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >>
     fs[Abbr `ct`,Abbr `value_opt`]) >>
  `(ct = DelegateCall) = flags.rcf_is_delegate` by
    (Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >> simp[Abbr `ct`]) >>
  `w2w (w2w (target : 160 word) : bytes32) = target` by
    simp[w2w_w2w, WORD_ALL_BITS, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  `es2 = SND (adopt_call_outcome rq outcome es1)` by simp[] >>
  FAIL_TAC "normal call conversions"
QED
