(* Assemble the linked continuation at the actual fetched CALL endpoint. *)
Theory bodyRawContinuationMods
Ancestors
  bodyRawFetchedEntryMods bodyRawEarlyAbortMods bodyRawOracleSourceMods
  bodyRawNormalLandingMods bodyRawLandingFrameMods bodyRawLandedBufferMods
  bodyRawMandatoryRevertMods bodyRawZeroResultMods bodyRawBufferedResultMods
  gasOutcomeFullPostMods stateRelProj vyperStorageFootprint
  bodyFullPostsMods bodyFullPredsMods exprSimRawCall exprLoweringProps exprOperandVar
  bodyPtrDefs fragGasOriginPtr loweringPosts loweringStateRelDefs ptrDiscipline
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
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`w2n (n2w amount : bytes32) = amount`,
        `flags.rcf_is_delegate ==> amount = 0`, `flags.rcf_is_static ==> amount = 0`,
        `cx.txn.is_static ==> amount = 0`] >>
     Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >>
     Cases_on `cx.txn.is_static` >> simp[Abbr `ct`,Abbr `value_opt`]) >>
  `(ct = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt` by
    (qpat_assum `~(flags.rcf_is_delegate /\ flags.rcf_is_static)` mp_tac >>
     Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >>
     simp[Abbr `ct`,Abbr `value_opt`]) >>
  `(ct = DelegateCall) = flags.rcf_is_delegate` by
    (Cases_on `flags.rcf_is_delegate` >> Cases_on `flags.rcf_is_static` >> simp[Abbr `ct`]) >>
  `w2w (w2w (target : 160 word) : bytes32) = target` by
    simp[w2w_w2w, WORD_ALL_BITS, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  `es2 = SND (adopt_call_outcome rq outcome es1)` by simp[] >>
  `sc.cs_current_bb = t7.vs_current_bb` by simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t7)` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
    ?u. run_inst_seq (emitted_insts s7 sc) t7 = OK u /\ step_inst_base inst t7 = OK u /\
      let q = u with vs_inst_idx := LENGTH sc.cs_current_insts in
      let Gq = step_prov PG G7 inst u in
      let tnq = step_taint inst t7 u tn7 in
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t7,G7,tn7) [] (OK q,Gq,tnq) /\
        stmt_state_rel H ctx func cenv cx es2 q /\
        ~q.vs_halted /\ q.vs_current_bb = sc.cs_current_bb /\
        q.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func q /\
        q.vs_returndata = outcome.co_returnData /\
        q.vs_memory = (write_memory_with_expansion ro (TAKE cap outcome.co_returnData) t7).vs_memory /\
        q.vs_allocas = t7.vs_allocas /\ q.vs_alloca_next = t7.vs_alloca_next /\
        q.vs_fmp = t7.vs_fmp /\ q.vs_initial_fmp = t7.vs_initial_fmp /\
        q.vs_immutables = t7.vs_immutables /\ q.vs_data_section = t7.vs_data_section /\
        (!p. safe_operand s7 p ==> eval_operand p q = eval_operand p t7) /\
        eval_operand ok q = SOME (bool_to_word outcome.co_success) /\
        op_taint tnq ok = {} /\ op_prov Gq ok = NONE /\
        tnq.t_mem = tn7.t_mem DIFF {j | ro <= j /\ j < ro + LENGTH (TAKE cap outcome.co_returnData)} /\
        stor_taint_ok_at (DF H) tnq q /\
        (!x. ~MEM x inst.inst_outputs ==>
             FLOOKUP Gq x = FLOOKUP G7 x /\ op_taint tnq (Var x) = op_taint tn7 (Var x) /\
             lookup_var x q = lookup_var x t7)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> stmt_state_rel H _ _ _ _ esK t7 /\ _`
       (drule_at (Pat `valid_horizon cx st0 H esK.storage_trace`)) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `stor_taint_ok_at (DF H) tn7 t7` by
       (qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms,bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     irule raw_call_normal_landing_mods >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists `bb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`n2w ib`,`w2w target`,`n2w (LENGTH bs)`,`ct`,`len`,`dp`,`es1`,`esK`,
       `gw`,`OPTION_BIND gkw dest_NumV`,`gas`,`op`,`rq`,`n2w ro`,`target`,`addr`,
       `vop`,`n2w amount`,`value_opt`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?u. run_inst_seq _ _ = OK u /\ _`
    (drule_then (qx_choose_then `u` mp_tac)) >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  qabbrev_tac `Gq = step_prov PG G7 inst u` >>
  qabbrev_tac `tnq = step_taint inst t7 u tn7` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t7,G7,tn7) [] (OK q,Gq,tnq) /\
     stmt_state_rel H ctx func cenv cx es2 q /\ stor_taint_ok_at (DF H) tnq q` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ?u. run_inst_seq _ _ = OK u /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `u'` (mp_tac o REWRITE_RULE [LET_THM])) >>
     CONV_TAC (DEPTH_CONV BETA_CONV) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `u' = u` by
       (qpat_assum `run_inst_seq _ _ = OK u'` mp_tac >>
        qpat_assum `run_inst_seq _ _ = OK u` (fn th => simp[NoAsms,th])) >>
     pop_assum SUBST_ALL_TAC >>
     simp[NoAsms,Abbr `q`,Abbr `Gq`,Abbr `tnq`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "landed_resources"
QED

Resume raw_call_continuation_full_mods[landed_resources]:
  `(case ct of RegularCall => emit_op CALL [gas;addr;vop;dp;len;op;Lit (n2w cap)]
    | StaticCall => emit_op STATICCALL [gas;addr;dp;len;op;Lit (n2w cap)]
    | DelegateCall => emit_op DELEGATECALL [gas;addr;dp;len;op;Lit (n2w cap)]) s7 = (ok,sc)` by
    (qpat_assum `emit_op _ _ s7 = (ok,sc)` mp_tac >> Cases_on `ct` >> simp[NoAsms]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp q /\
     q.vs_alloca_next + pending_alloca_size func q <= w2n q.vs_initial_fmp)` by
    (disch_tac >> conj_tac
     >- (qpat_assum `stmt_state_rel H0 ctx func cenv cx es2 q`
           (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
         simp[]) >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx es2 q`
       (mp_tac o MATCH_MP stmt_state_rel_fmp_room) >>
     qpat_assum `ctx_has_dalloca ctx` (fn th => simp[NoAsms,fmp_room_def,th]) >>
     strip_tac >> decide_tac) >>
  `allocas_from lo q /\ lo <= q.vs_alloca_next /\ s0.vs_alloca_next <= q.vs_alloca_next` by
    (qpat_assum `allocas_from lo t7` mp_tac >>
     qpat_assum `lo <= t7.vs_alloca_next` mp_tac >>
     qpat_assum `s0.vs_alloca_next <= t7.vs_alloca_next` mp_tac >>
     qpat_assum `q.vs_allocas = t7.vs_allocas` (fn allocs =>
       qpat_assum `q.vs_alloca_next = t7.vs_alloca_next`
         (fn next => simp[NoAsms,allocas_from_def,allocs,next]))) >>
  `eval_operand ok q = SOME (if outcome.co_success then 1w else 0w)` by
    (`!b. bool_to_word b = (if b then 1w else 0w)` by
       (Cases >> simp[venomExecSemanticsTheory.bool_to_word_def]) >>
     qpat_assum `eval_operand ok q = SOME _` mp_tac >>
     pop_assum (fn th => simp[NoAsms,th])) >>
  qabbrev_tac `status = STRING #"%" (toString s7.cs_next_var)` >>
  `~not_fresh_at s7 status` by
    (simp[Abbr `status`,not_fresh_at_def] >> qexists `s7.cs_next_var` >> simp[]) >>
  `inst.inst_outputs = [status]` by
    (qpat_assum `inst = mk_inst _ _ _ _` (fn th => simp[NoAsms,th,mk_inst_def])) >>
  `!x. x <> status ==> lookup_var x q = lookup_var x t7 /\
      FLOOKUP Gq x = FLOOKUP G7 x /\ op_taint tnq (Var x) = op_taint tn7 (Var x)` by
    (rpt strip_tac >> qpat_assum `!x. ~MEM x inst.inst_outputs ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `FLOOKUP Gq status = NONE /\ op_taint tnq (Var status) = {}` by
    (qpat_assum `op_prov Gq ok = NONE` mp_tac >>
     qpat_assum `op_taint tnq ok = {}` mp_tac >>
     qpat_assum `ok = Var status` (fn th => simp[NoAsms,th,op_prov_def])) >>
  qabbrev_tac `capacity = if cap = 0 then 0 else 32 * ((cap + 31) DIV 32) + 32` >>
  `ob <= ro /\ ro + LENGTH (TAKE cap outcome.co_returnData) <= ob + capacity` by
    (`cap <= 32 * ((cap + 31) DIV 32)` by simp[NoAsms,spillSimTheory.n_le_round_up_32] >>
     `LENGTH (TAKE cap outcome.co_returnData) <= cap` by
       (simp[NoAsms,LENGTH_TAKE_EQ] >> IF_CASES_TAC >> decide_tac) >>
     qpat_assum `LENGTH (TAKE _ _) <= cap` mp_tac >>
     qpat_assum `cap <= 32 * _` mp_tac >>
     simp[NoAsms,Abbr `capacity`,Abbr `ro`] >> IF_CASES_TAC >> decide_tac) >>
  `(cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint ob capacity off (type_memory_size tv))` by
    (rpt strip_tac >>
     qpat_assum `cenv.ce_is_ctor ==> !src tops name tv v off. _ ==> regions_disjoint _ _ ob capacity`
       (drule_then (drule_all_then mp_tac)) >>
     simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `!H. valid_horizon cx st0 H esK.storage_trace /\ stor_taint_ok_at (DF H) tnq q ==>
       ghost_inv_at_mods (DF H) lo dframe cenv cx es2 Gq tnq q /\
       immutable_frame_mods func cenv cx es2 q /\ wb_frame cenv es es2 sa s0 q /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tnq` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> stmt_state_rel H _ _ _ _ esK t7 /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     irule raw_call_landing_frames_mods >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`G7`,`cap`,`capacity`,`ctx`,`esK`,`ob`,`outcome.co_returnData`,
               `n2w ro`,`s6`,`s7`,`status`,`t7`,`tn7`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `w2n (n2w ro : bytes32) = ro` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace /\ stor_taint_ok_at _ _ _ ==> _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `es2 with gas_obs := [] = es2` by
    (qpat_assum `es2.gas_obs = []` (fn th => simp[NoAsms,GSYM th])) >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  qmatch_asmsub_abbrev_tac `eval_raw_call cx flags target bs amount gkw esK = (res,es2)` >>
  `!tail. eval_raw_call cx flags target bs amount gkw (esK with gas_obs := tail) =
      (res,es2 with gas_obs := tail)` by
    (qpat_assum `!gs. eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `eval_raw_call cx flags target bs amount gkw esK = (res,es2)`
       (fn th => simp[NoAsms,th])) >>
  Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success`
  >- suspend "mandatory_failure" >>
  `flags.rcf_revert_on_failure ==> outcome.co_success` by
    (qpat_assum `~(flags.rcf_revert_on_failure /\ ~outcome.co_success)` mp_tac >>
     tautLib.TAUT_TAC) >>
  Cases_on `cap = 0`
  >- suspend "zero_capacity" >>
  suspend "positive_capacity"
QED

Resume raw_call_continuation_full_mods[mandatory_failure]:
  `flags.rcf_revert_on_failure /\ ~outcome.co_success` by first_assum ACCEPT_TAC >>
  pop_assum strip_assume_tac >>
  `compile_raw_call_finish addr dp len gas vop ct cap T ov op s7 = (result,sb)` by
    (qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ flags.rcf_revert_on_failure _ _ _ = _` mp_tac >>
     qpat_assum `flags.rcf_revert_on_failure` (fn th => simp[NoAsms,th])) >>
  `eval_operand ok q = SOME 0w` by
    (qpat_assum `eval_operand ok q = SOME (if _ then _ else _)` mp_tac >>
     qpat_assum `~outcome.co_success` (fn th => simp[NoAsms,th])) >>
  `res = INR (Error (RevertData outcome.co_returnData))` by
    (qpat_assum `flags.rcf_revert_on_failure /\ ~outcome.co_success` (fn th => simp[NoAsms,Abbr `res`,th])) >>
  drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ T _ _ _ = _`)
    (INST_TYPE [alpha |-> ``:eval_result``] raw_call_mandatory_revert_path_mods) >>
  disch_then (drule_at (Pat `(case ct of _ => _ | _ => _ | _ => _) s7 = (ok,sc)`)) >>
  disch_then (drule_at (Pat `eval_operand ok q = SOME 0w`)) >>
  disch_then (drule_at (Pat `op_taint tnq ok = {}`)) >>
  disch_then (drule_at (Pat `op_prov Gq ok = NONE`)) >>
  disch_then (drule_at (Pat `fn_has_code sc sb func`)) >>
  disch_then (drule_at (Pat `allocas_from lo q`)) >>
  disch_then (drule_at (Pat `q.vs_returndata = outcome.co_returnData`)) >>
  disch_then (qspecl_then [`(res : eval_result + vyperState$exception)`,`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `ur` (qx_choose_then `Gr` (qx_choose_then `tnr`
    (map_every assume_tac o CONJUNCTS)))) >>
  irule gas_outcome_full_mods_exit_revert >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gr`,`es2`,`res`,`tnr`,`ur`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- simp[NoAsms,fragExecTheory.exit_result_def] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (once_rewrite_tac[GSYM APPEND_NIL] >> irule gas_origin_ptr_path_append >>
      qexistsl [`Gq`,`q`,`(OK q,Gq,tnq)`,`tnq`] >> simp[NoAsms] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!D. gas_origin_ptr_path _ (q,Gq,tnq) [] _` (qspec_then `DF H` ACCEPT_TAC)) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `es2 with gas_obs := [] = es2` (fn th => rewrite_tac[th]) >>
  qpat_assum `res = INR (Error (RevertData _))`
    (fn th => simp[NoAsms,th,exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]) >>
  first_assum ACCEPT_TAC
QED

Resume raw_call_continuation_full_mods[zero_capacity]:
  `flags.rcf_max_outsize = 0` by
    (qpat_assum `cap = 0` (fn th => mp_tac th >> simp[NoAsms,Abbr `cap`])) >>
  `compile_raw_call_finish addr dp len gas vop ct 0 flags.rcf_revert_on_failure ov op s7 = (result,sb)` by
    (qpat_assum `compile_raw_call_finish _ _ _ _ _ _ cap _ _ _ _ = _` mp_tac >>
     qpat_assum `cap = 0` (fn th => simp[NoAsms,th])) >>
  `(case ct of RegularCall => emit_op CALL [gas;addr;vop;dp;len;op;Lit 0w]
    | StaticCall => emit_op STATICCALL [gas;addr;dp;len;op;Lit 0w]
    | DelegateCall => emit_op DELEGATECALL [gas;addr;dp;len;op;Lit 0w]) s7 = (ok,sc)` by
    (qpat_assum `(case ct of _ => _ | _ => _ | _ => _) s7 = (ok,sc)` mp_tac >>
     qpat_assum `cap = 0` (fn th => simp[NoAsms,th])) >>
  `vv = StackValue (raw_call_return_type flags) result` by
    (qpat_assum `vv = if cap = 0 then _ else _` mp_tac >>
     qpat_assum `cap = 0` (fn th => simp[NoAsms,th])) >>
  `res = INL (Value (if flags.rcf_revert_on_failure then NoneV else BoolV outcome.co_success))` by
    (qpat_assum `flags.rcf_max_outsize = 0` (fn th => simp[NoAsms,Abbr `res`,th]) >>
     qpat_assum `flags.rcf_revert_on_failure ==> outcome.co_success` mp_tac >> tautLib.TAUT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp q /\ _` mp_tac >> tautLib.TAUT_TAC) >>
  drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ 0 _ _ _ _ = _`)
    (INST_TYPE [alpha |-> ``:vyperState$exception``, beta |-> ``:256``] raw_zero_result_path_mods) >>
  disch_then (drule_at (Pat `(case ct of _ => _ | _ => _ | _ => _) s7 = (ok,sc)`)) >>
  disch_then (drule_at (Pat `eval_operand ok q = SOME (if _ then _ else _)`)) >>
  disch_then (drule_at (Pat `op_taint tnq ok = {}`)) >>
  disch_then (drule_at (Pat `op_prov Gq ok = NONE`)) >>
  disch_then (drule_at (Pat `fn_has_code sc sb func`)) >>
  disch_then (drule_at (Pat `allocas_from lo q`)) >>
  disch_then (drule_at (Pat `wb_frame cenv es es2 sa s0 q`)) >>
  disch_then (drule_at (Pat `ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tnq`)) >>
  disch_then (drule_at (Pat `expr_has_effect e`)) >>
  disch_then (fn th => mp_tac (Q.SPECL [`res`,`dframe`,`cx`,`ctx`] th)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (fn th =>
    map_every (fn c => if is_forall (concl c) andalso
                          is_imp (snd (strip_forall (concl c)))
                       then mk_asm "zero_post" c else assume_tac c) (CONJUNCTS th))) >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gq`,`es2`,`res`,`t`,`tnq`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (once_rewrite_tac[GSYM APPEND_NIL] >> irule gas_origin_ptr_path_append >>
      qexistsl [`Gq`,`q`,`(OK q,Gq,tnq)`,`tnq`] >> simp[NoAsms] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!D explicit PG. gas_origin_ptr_path _ (q,Gq,tnq) [] _`
        (qspecl_then [`DF H`,`explicit`,`PG`] ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> valid_horizon _ _ H esK.storage_trace /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace /\ stor_taint_ok_at _ _ _ ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "zero_post" (qspecl_then [`H`,`DF (H : (bool # 256 word # type_value) list # num list)`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `tv` (map_every assume_tac o CONJUNCTS)) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `es2 with gas_obs := [] = es2` (pure_rewrite_tac o single) >>
  qpat_assum `vv = StackValue _ _` (fn th => simp[NoAsms,th,contextTheory.vv_location_def]) >>
  qexists `tv` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `!v. tv = Value v /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Resume raw_call_continuation_full_mods[positive_capacity]:
  `0 < cap` by (qpat_assum `cap <> 0` mp_tac >> decide_tac) >>
  `capacity = 32 * ((cap + 31) DIV 32) + 32 /\ ro = ob + 32` by
    (qpat_assum `cap <> 0` (fn th => simp[NoAsms,Abbr `capacity`,Abbr `ro`,th])) >>
  pop_assum strip_assume_tac >>
  `vv = LocatedValue (expr_type e) (mk_ptr result LocMemory)` by
    (qpat_assum `vv = if cap = 0 then _ else _` mp_tac >>
     qpat_assum `expr_type e = raw_call_return_type flags` (fn th => rewrite_tac[th]) >>
     qpat_assum `cap <> 0` (fn th => simp[NoAsms,th])) >>
  `cs_extends sc sb` by
    (drule exprSimRawCallCalldataTheory.raw_call_finish_prefix >>
     disch_then strip_assume_tac >>
     qpat_assum `(case ct of _ => _ | _ => _ | _ => _) s7 = (ok,sc)` (fn th =>
       qpat_x_assum `(case ct of _ => _ | _ => _ | _ => _) s7 = _` mp_tac >>
       simp[NoAsms,th]) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `?x. ov = Var x` by
    (qpat_assum `op_prov G7 ov = SOME _` mp_tac >> Cases_on `ov` >> simp[NoAsms,op_prov_def]) >>
  pop_assum strip_assume_tac >>
  `safe_operand s7 ov /\ safe_operand s7 op` by
    (qpat_assum `EVERY (safe_operand s7) _` mp_tac >> simp[NoAsms]) >>
  pop_assum strip_assume_tac >>
  `safe_operand sc ok` by
    (qpat_assum `ok = Var status` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,exprSafeOperandTheory.safe_operand_def,Abbr `status`,not_fresh_at_def] >>
     qpat_assum `sc.cs_next_var = s7.cs_next_var + 1` (fn th => simp[NoAsms,th])) >>
  `not_fresh_at s7 x` by
    (qpat_assum `safe_operand s7 ov` mp_tac >>
     qpat_assum `ov = Var x` (fn th => simp[NoAsms,th,exprSafeOperandTheory.safe_operand_def])) >>
  `x <> status` by
    (qpat_assum `!x. not_fresh_at s7 x ==> x <> status` irule >> first_assum ACCEPT_TAC) >>
  `lookup_var x q = SOME (n2w ob) /\ FLOOKUP Gq x = SOME (ob,capacity) /\ op_taint tnq (Var x) = {}` by
    (qpat_assum `!x. x <> status ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
     qpat_assum `eval_operand ov t7 = SOME _` mp_tac >>
     qpat_assum `op_prov G7 ov = SOME _` mp_tac >>
     qpat_assum `op_taint tn7 ov = {}` mp_tac >>
     qpat_assum `ov = Var x` (fn th => simp[NoAsms,th,op_prov_def,venomStateTheory.eval_operand_def]) >>
     strip_tac >> strip_tac >> strip_tac >>
     asm_rewrite_tac[]) >>
  pop_assum strip_assume_tac >>
  suspend "positive_packet"
QED

Resume raw_call_continuation_full_mods[positive_packet]:
  `expr_type e = (if flags.rcf_revert_on_failure then BaseT (BytesT (Dynamic cap))
     else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic cap))])` by
    (qpat_assum `expr_type e = raw_call_return_type flags` (fn th => rewrite_tac[th]) >>
     qpat_assum `cap <> 0` mp_tac >>
     simp[NoAsms,vyperTypeSystemTheory.raw_call_return_type_def,Abbr `cap`]) >>
  `32 + (32 * ((cap + 31) DIV 32) + 32) < dimword (:256)` by
    (qpat_assum `type_alloc_ok cenv (expr_type e)` mp_tac >>
     qpat_assum `expr_type e = if flags.rcf_revert_on_failure then _ else _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `flags.rcf_revert_on_failure` >>
     simp[allocLimitsTheory.type_alloc_ok_def,compileEnvTheory.is_word_type_def,compileEnvTheory.type_memory_bytes_def] >>
     simp[NoAsms,wordsTheory.dimword_def] >> decide_tac) >>
  `~flags.rcf_revert_on_failure ==> evaluate_type (get_tenv cx) (expr_type e) =
     SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))])` by
    (qpat_assum `expr_type e = if flags.rcf_revert_on_failure then _ else _` (fn th => rewrite_tac[th]) >>
     qpat_assum `cap < dimword (:256)` (fn th => mp_tac th >>
       mp_tac (MATCH_MP vyperTypeExtCallSoundnessTheory.raw_call_bytes_slot_size_bound th)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[vyperValueTheory.evaluate_type_def]) >>
  `ob < dimword (:256) /\ ob + 32 < dimword (:256)` by
    (qpat_assum `ob + capacity < dimword (:256)` mp_tac >>
     qpat_assum `capacity = 32 * _ + 32` (fn th => rewrite_tac[th]) >> decide_tac) >>
  pop_assum strip_assume_tac >>
  `w2n (n2w ob : bytes32) = ob` by
    (qpat_assum `ob < dimword (:256)` (fn th => simp[NoAsms,w2n_n2w,th])) >>
  `ptr_covers Gq tnq x q capacity` by
    (simp[NoAsms,ptr_covers_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`n2w ob`,`ob`,`capacity`] >>
     qpat_assum `w2n (n2w ob : bytes32) = ob` (fn th => simp[NoAsms,th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `wb_frame cenv es es2 sa s0 q` mp_tac >>
     simp[NoAsms,wb_frame_def,locals_kept_def] >> strip_tac >> first_assum (ACCEPT_TAC o SYM)) >>
  `ghost_kept_at lo cenv esK s7 G7 tn7 t7 Gq tnq` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qexistsl [`G7`,`tn7`] >> simp[NoAsms,wordArgsPtrTheory.ghost_kept_at_refl] >> conj_tac
     >- (qx_gen_tac `y` >> disch_tac >>
         `y <> status` by (qpat_assum `!x. not_fresh_at s7 x ==> x <> status` irule >> first_assum ACCEPT_TAC) >>
         qpat_assum `!x. x <> status ==> _` (drule_at (Pat `y <> status`)) >>
         disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `tnq.t_mem = tn7.t_mem DIFF _` (fn th => simp[NoAsms,th,pred_setTheory.SUBSET_DIFF])) >>
  suspend "positive_buffer"
QED

Resume raw_call_continuation_full_mods[positive_buffer]:
  `local_ptrs_reserved cenv s6` by
    (irule exprOperandVarTheory.compiler_ci_mono_reserved >> qexists `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `compile_raw_call_outbuf cap s6 = _`)
    (Q.INST [`scopes` |-> `es2.scopes`] exprSimRawCallTheory.raw_call_outbuf_allocation_site) >>
  disch_then (fn th => mp_tac (Q.SPECL [`func`,`es2`,`cenv`] th)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `site` (qx_choose_then `var0` (map_every assume_tac o CONJUNCTS))) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= s6.cs_next_id /\
   s6.cs_next_id < s7.cs_next_id /\ s7.cs_next_id < sc.cs_next_id` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ci_mono sa s6`,`ci_mono sa s7`,`ci_mono sout s7`,`ci_mono s7 sc`,
        `s6.cs_next_id < sout.cs_next_id`,`sc.cs_next_id = s7.cs_next_id + 1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ci_mono_def] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `emit_op opc ops s7 = (ok,sc)` >>
  mp_tac (Q.INST [`rev` |-> `flags.rcf_revert_on_failure`, `success` |-> `outcome.co_success`,
    `call_ty` |-> `ct`, `val_op` |-> `vop`] raw_call_landed_buffer_packet_mods) >>
  qpat_assum `capacity = 32 * _ + 32` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `ro = ob + 32` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `w2n (n2w ro : bytes32) = ro` (pure_rewrite_tac o single) >>
  qpat_assum `w2n (n2w ob : bytes32) = ob` (pure_rewrite_tac o single) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qpat_assum `flags.rcf_revert_on_failure ==> outcome.co_success` mp_tac >> tautLib.TAUT_TAC)
     >- (qpat_assum `ro = ob + 32` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)
     >- (qpat_assum `capacity = 32 * _ + 32` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)
     >- (qpat_assum `q.vs_allocas = t7.vs_allocas` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
     qpat_assum `q.vs_returndata = outcome.co_returnData` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC)) >>
  disch_then assume_tac >> suspend "positive_finish"
QED

Resume raw_call_continuation_full_mods[positive_finish]:
  `32 + ((cap + 31) DIV 32) * 32 = capacity /\
   64 + ((cap + 31) DIV 32) * 32 = 32 + capacity` by
    (qpat_assum `capacity = 32 * _ + 32` (pure_rewrite_tac o single) >>
     pure_once_rewrite_tac[MULT_COMM] >> decide_tac) >>
  `LENGTH q.vs_returndata < dimword (:256)` by
    (qpat_assum `q.vs_returndata = outcome.co_returnData` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `v = if flags.rcf_revert_on_failure then BytesV (TAKE cap q.vs_returndata)
      else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE cap q.vs_returndata)])` >>
  `res = INL (Value v)` by
    (qpat_assum `flags.rcf_revert_on_failure ==> outcome.co_success` mp_tac >>
     qpat_assum `cap <> 0` mp_tac >>
     qpat_assum `q.vs_returndata = outcome.co_returnData` (fn th =>
       simp[NoAsms,Abbr `res`,Abbr `v`,Abbr `cap`,th]) >> tautLib.TAUT_TAC) >>
  mp_tac (Q.INST [`to_op` |-> `addr`, `dl` |-> `len`, `gas_op` |-> `gas`, `val_op` |-> `vop`,
    `call_ty` |-> `ct`, `n` |-> `cap`, `rev` |-> `flags.rcf_revert_on_failure`,
    `success` |-> `outcome.co_success`, `sa` |-> `s7`, `s` |-> `q`, `G` |-> `Gq`,
    `tn` |-> `tnq`, `es0` |-> `es`, `es` |-> `es2`, `sf` |-> `sa`, `dep` |-> `dframe`]
    raw_buffered_result_path_mods) >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `Abbrev (v = _)` (pure_rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qpat_assum `flags.rcf_revert_on_failure ==> outcome.co_success` mp_tac >> tautLib.TAUT_TAC) >>
     qpat_assum `32 + _ = capacity` (pure_rewrite_tac o single) >>
     qpat_assum `64 + _ = 32 + capacity` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf` (fn th =>
    map_every (fn c => if is_forall (concl c) andalso
                          is_imp (snd (strip_forall (concl c)))
                       then mk_asm "buffered_post" c else assume_tac c) (CONJUNCTS th))))) >>
  suspend "positive_post"
QED

Resume raw_call_continuation_full_mods[positive_post]:
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`es2`,`res`,`t`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (once_rewrite_tac[GSYM APPEND_NIL] >> irule gas_origin_ptr_path_append >>
      qexistsl [`Gq`,`q`,`(OK q,Gq,tnq)`,`tnq`] >> simp[NoAsms] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (q,Gq,tnq) [] _`
        (qspecl_then [`DF H`,`explicit`] ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> valid_horizon _ _ H esK.storage_trace /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace /\ stor_taint_ok_at _ _ _ ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "buffered_post" (qspecl_then [`H`,`DF (H : (bool # 256 word # type_value) list # num list)`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `es2 with gas_obs := [] = es2` (pure_rewrite_tac o single) >>
  `!p. (mk_ptr p LocMemory).ptr_location = LocMemory /\ (mk_ptr p LocMemory).ptr_operand = p` by
    simp[NoAsms,contextTheory.mk_ptr_def] >>
  pop_assum (fn ptr => qpat_assum `vv = LocatedValue _ _`
    (fn th => simp[NoAsms,th,ptr,contextTheory.vv_location_def])) >>
  qexists `Value v` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `vv_own cenv cx _ sa sb es2 (Value v) _ t`
    (fn th => simp[NoAsms,th])
QED

Finalise raw_call_continuation_full_mods
