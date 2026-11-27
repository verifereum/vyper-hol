(* Join the reached byte-input prefix with an independently supplied finish. *)
Theory bodyRawBytesRequestMods
Ancestors
  bodyRawBytesRequestCutsMods bodyRawBytesForcedReadsMods
  bodyRawBytesHeaderEntryMods bodyRawBytesKeywordsMods bodyRawRequestGasOutbufMods
  bodyRawBytesReadOutcomesMods bodyRawBytesReachedFramesMods
  bodyRawBytesTailInputsMods bodyRawBytesOutbufSavedMods bodyRawRequestInputsMods
  bodyECRecoverForcedTailMods bodyForcedStorageFrameMods
  bodyRawCalldataRequestMods
  gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods bodyExtRequestOptionalGasMods
  exprSimFullBundleProps exprBodyPreProps exprSimSliceCompose stmtSimForRounds
  bodyFullPostsMods bodyFullPredsMods vyperStorageTrace vyperStorageFootprint
  exprSimRawCall exprOperandVar exprWordOperand exprSimSource exprSimWordArgs
  loweringPosts bodyPtrDefs bodyMemoryDefs loweringShapeDefs exprSafeOperand vyperTypeSystem
  compileEnv vyperTypeEvalCaseProofs
  haltExitProj stmtSimProps exprLoweringProps fragExec
  vyperInterpreter vyperState vyperValue gasShadow gasContext gasStorage
Libs monadsyntax

val raw_e = ``Call ann (RawCallTarget flags) args dflt``;
val raw_M = ``flags.rcf_max_outsize``;
val raw_n = ``if ^raw_M = 0 then 0 else 32 * ((^raw_M + 31) DIV 32) + 32``;
val raw_v = ``case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME p => p``;
val raw_g = ``ext_call_kwarg EKGas flags.rcf_kws (kvs:value list)``;
val raw_ct = ``if flags.rcf_is_delegate then DelegateCall
               else if flags.rcf_is_static then StaticCall else RegularCall``;
val raw_R = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : eval_result + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;
val gas_out_separated = ``\b n t.
  (!name base sz. local_region cenv esK.scopes t name base sz ==> regions_disjoint b n base sz) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint b n off (type_memory_size tv))``;
val gas_old_regs = ``\sa s (G : string |-> num # num) tn t J tf.
  !x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP J x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)``;
val raw_Q = ``\(H : (bool # 256 word # type_value) list # num list) (res:eval_result + exception) ee G tn t. ?tv. res = INL tv /\
  vv_post_mods H ctx func cenv cx ^raw_e es sa sb s0 ee tv vv t /\
  vv_store_bound cx (post_value_type cenv ^raw_e) (lowered_value_type cenv ^raw_e) ee tv vv t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo dframe cenv cx ee G tn t /\
  ptr_vv_ok cx (post_value_type cenv ^raw_e) tv vv ee G tn t /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^raw_e) /\ ~is_bytestring_type (post_value_type cenv ^raw_e) ==>
       vv_own cenv cx (post_value_type cenv ^raw_e) sa sb ee tv vv t /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^raw_e) = SOME rt /\
             eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)) /\
  (!t' p. vv = StackValue t' p /\ ~is_word_type (post_value_type cenv ^raw_e) ==> ptr_buf_ok cenv ^raw_e p G t) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==> ptr_buf_ok cenv ^raw_e p.ptr_operand G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val raw_bytes_Q = subst [``args : expr list`` |-> ``a::d::kws : expr list``,
                         ``dflt : expr option`` |-> ``NONE : expr option``] raw_Q;

val raw_finish = ``
  !st0 sa sb vv s0 G0 tn0 s6 sout s7 addr dp len gas xs kvs ov op result
    target bs amount gw ib ob esK t7 G7 tn7.
  expr_has_effect ^raw_e /\ post_value_type cenv ^raw_e = expr_type ^raw_e /\
  lowered_value_type cenv ^raw_e = expr_type ^raw_e /\ expr_type ^raw_e = raw_call_return_type flags /\
  type_alloc_ok cenv (expr_type ^raw_e) /\ ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\ (flags.rcf_is_static ==> amount = 0) /\
  amount < dimword (:256) /\ ^raw_M < dimword (:256) /\
  expr_sim_inv_mods mods cenv cx env esK /\ esK.gas_obs = [] /\
  storage_trace_domain cx st0 esK.storage_trace /\
  fn_has_code sa sb func /\ fn_has_code s6 sout func /\ fn_inst_ids_distinct func /\
  ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\ ci_mono sa s7 /\
  compile_raw_call_outbuf ^raw_M s6 = ((ov,op),sout) /\
  compile_raw_call_finish addr dp len gas ^raw_v ^raw_ct ^raw_M flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  vv = (if ^raw_M = 0 then StackValue (raw_call_return_type flags) result
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
  eval_operand addr t7 = SOME (w2w target) /\ eval_operand ^raw_v t7 = SOME (n2w amount) /\
  eval_operand gas t7 = SOME gw /\ (!g. OPTION_BIND ^raw_g dest_NumV = SOME g ==> g = w2n gw) /\
  eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
  ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\ w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
  read_memory ib (LENGTH bs) t7 = bs /\ (!j. ib <= j /\ j < ib + LENGTH bs ==> j NOTIN tn7.t_mem) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
  eval_operand ov t7 = SOME (n2w ob) /\ eval_operand op t7 = SOME (n2w (if ^raw_M = 0 then ob else ob + 32)) /\
  (^raw_M = 0 ==> ov = op) /\ ob + ^raw_n < dimword (:256) /\ FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,^raw_n) /\
  op_prov G7 ov = SOME (ob,^raw_n) /\ op_prov G7 op = SOME (ob,^raw_n) /\
  op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> regions_disjoint ob ^raw_n lb sz) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob ^raw_n) /\
  EVERY (\x. op_taint tn7 x = {}) [addr;len;dp;gas;^raw_v] /\
  EVERY (safe_operand s7) [addr;len;dp;gas;^raw_v;ov;op] /\
  (!x. MEM (Var x) [addr;len;dp;gas;^raw_v;ov;op] ==> not_fresh_at s7 x)
  ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_raw_call cx flags target bs amount ^raw_g) (esK,t7,G7,tn7) ^raw_Q ^raw_R``;

val read_post = ``\e es sa sb s0 op G0 tn0 (H : (bool # 256 word # type_value) list # num list) v ee G tn t.
  (expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo dframe cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;
val PA = ``^read_post a es sa s1 s0 addr G0 tn0``;
val PD = ``\(av:value) esA GA tnA tA. ^read_post d esA s1 s2 tA data GA tnA``;
val raw_next = ``\av dv kvs. do
    type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
    target <- lift_option_type (dest_AddressV av) "raw_call target";
    bs <- lift_option_type (dest_BytesV dv) "raw_call data";
    amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
    eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
  od``;
val raw_suffix = ``\av dv. bind (eval_exprs cx kws) (^raw_next av dv)``;

Triviality raw_next_frame:
  !av dv kvs. storage_trace_frame (^raw_next av dv kvs)
Proof
  BETA_TAC >> simp[storage_trace_frame_bind_all,ignore_bind_def,storage_trace_frame_checks,
                   storage_trace_frame_lifts,storage_trace_frame_raw_call]
QED

val read_R = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : value + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Triviality raw_read_exit_wrap:
  gas_outcome_full_mods (DF,lo,E,ctx,func,PG) ms cx st0 action (ee,t,G,tn) Q ^read_R ==>
  gas_outcome_full_mods (DF,lo,E,ctx,func,PG) ms cx st0 action (ee,t,G,tn) Q
    (\H res est gt r. ?ex. res = INR ex /\ ^raw_R H (INR ex) est gt r)
Proof
  strip_tac >> irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at Any) >> BETA_TAC >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[] >>
  rpt strip_tac >> metis_tac[expr_exit_INR_type,halt_exit_INR_type]
QED

Theorem raw_call_vv_from_parts_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env ^raw_e es /\ body_exprs_full_ok_mods mods exps cx args /\
  ^raw_finish ==>
  expr_vv_sim_full_mods (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^raw_e es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then strip_assume_tac (BETA_RULE raw_bytes_request_cuts_mods) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  qpat_x_assum `dflt = NONE` SUBST_ALL_TAC >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `tail` >>
      Cases_on `eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) NONE)
                  (es with gas_obs := tail)` >>
      `storage_trace_frame (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) NONE))` by
        simp[NoAsms,evaluate_storage_trace_frame] >>
      `~storage_trace_domain cx st0 (es with gas_obs := tail).storage_trace` by simp[] >>
      drule_all_then (simp o single) storage_trace_frame_preserves_bad_domain) >>
  qpat_assum `eval_expr _ (Call _ _ _ _) = _` (fn th =>
    rule_assum_tac (ONCE_REWRITE_RULE [th]) >> pure_once_rewrite_tac[th]) >>
  ho_match_mp_tac (BETA_RULE (Q.INST [`P1` |-> `^PA`, `P2` |-> `^PD`]
      raw_bytes_forced_reads_mods)) >>
  conj_tac
  >- (irule (BETA_RULE raw_read_exit_wrap) >>
      irule (BETA_RULE raw_bytes_address_outcome_mods) >>
      qpat_assum `gas_admissible (bind (bind (eval_expr cx a) _) _) _ es` (irule_at Any) >>
      qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
      qpat_assum `expr_sim_full_code _ (sa,s1,shadow_sa,h1)` (irule_at Any) >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qexists_tac `exps` >> rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       (qx_gen_tac `H` >> disch_tac >>
        qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _ /\ _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)))
  >> conj_tac
  >- (rpt gen_tac >> irule storage_trace_frame_bind_all >> reverse conj_tac
      >- simp[evaluate_storage_trace_frame] >>
      rpt gen_tac >> BETA_TAC >> irule (BETA_RULE raw_next_frame))
  >> conj_tac
  >- suspend "data_read"
  >> suspend "after_reads"
QED

Resume raw_call_vv_from_parts_mods[data_read]:
  qx_genl_tac [`marks`,`av`,`esA`,`GA`,`tnA`,`tA`] >> strip_tac >>
  drule_all_then strip_assume_tac (BETA_RULE raw_bytes_data_reached_mods) >>
  irule (BETA_RULE raw_read_exit_wrap) >>
  irule (BETA_RULE raw_bytes_data_outcome_mods) >>
  qpat_assum `expr_sim_full_code _ (s1,s2,h1,h2)` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`^raw_suffix`,`s0`,`marks`,`kws`,`exps`,`es`,`env`,`cap`,`av`,`a`] >>
  BETA_TAC >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]) >>
  qpat_assum `expr_type d = BaseT (BytesT _)` (pure_rewrite_tac o single o GSYM) >>
  first_assum ACCEPT_TAC
QED

Resume raw_call_vv_from_parts_mods[after_reads]:
  qx_genl_tac [`marksA`,`av`,`esA`,`GA`,`tnA`,`tA`,`marksD`,`dv`,`esD`,`GD`,`tnD`,`tD`] >>
  strip_tac >>
  drule_all_then strip_assume_tac (BETA_RULE raw_bytes_data_reached_mods) >>
  `expr_body_pre_mods mods cenv cx env a es` by
    (irule request_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
     simp[] >> qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es`
       (ACCEPT_TAC o MATCH_MP expr_body_pre_mods_inv)) >>
  `safe_operand s1 addr` by
    (irule lower_value_word_safe_operand >>
     qpat_assum `lower_value compile_expr cenv (BaseT AddressT) a sa = _` (irule_at Any) >>
     qpat_assum `expr_body_pre_mods _ _ _ _ a es`
       (fn th => assume_tac (MATCH_MP expr_body_pre_mods_well_typed th) >>
                 assume_tac (MATCH_MP expr_body_pre_mods_inv th)) >>
     qexists_tac `env` >> simp[is_word_type_def,well_formed_type_def] >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ es` (strip_assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
     drule env_consistent_type_defs_get_tenv >> simp[] >>
     metis_tac[env_consistent_var_type_evaluates]) >>
  qpat_assum `!H. valid_horizon cx st0 H esA.storage_trace ==> (expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _) /\ _`
    (strip_assume_tac o CONV_RULE
      (BINDER_CONV (REWR_CONV IMP_CONJ_THM) THENC FORALL_AND_CONV)) >>
  qpat_assum `!H. valid_horizon cx st0 H esD.storage_trace ==> _ /\ _`
    (strip_assume_tac o CONV_RULE
      (BINDER_CONV (REWR_CONV IMP_CONJ_THM) THENC FORALL_AND_CONV)) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _ /\ _`
    (strip_assume_tac o CONV_RULE
      (BINDER_CONV (REWR_CONV IMP_CONJ_THM) THENC FORALL_AND_CONV)) >>
  drule_all_then strip_assume_tac (BETA_RULE raw_bytes_reached_data_frames_mods) >>
  qpat_x_assum `dv = BytesV _` SUBST_ALL_TAC >>
  `ci_mono sa s2` by (irule ci_mono_trans >> qexists_tac `s1` >> simp[]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var` by
    (qpat_assum `ci_mono sa s2` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     qpat_assum `ci_mono s1 s2` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >> simp[]) >>
  `!x. data = Var x ==> not_fresh_at s2 x` by
    (qpat_assum `lower_value compile_expr cenv _ d s1 = _`
       (mp_then Any (drule_then ACCEPT_TAC) compile_lower_value_var)) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule bodyFullIfExpReachTheory.body_inv_no_phi_mods >> disch_then (drule_then ACCEPT_TAC)) >>
  `!fn inst u. frag_reachable ctx func tD fn inst u ==> dalloca_fmp_headroom inst u` by
    (`valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
       (qpat_assum `storage_trace_domain cx st0 esD.storage_trace`
          (ACCEPT_TAC o REWRITE_RULE[storage_trace_domain_def])) >>
     qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> !fn inst u. _`
       (drule_then ACCEPT_TAC)) >>
  drule_all_then
    (qspecl_then [`shadow_ctx`, `PG`]
       (qx_choose_then `b` $ qx_choose_then `t4` $ qx_choose_then `G4` $
        qx_choose_then `tn4` $ map_every assume_tac o CONJUNCTS))
    (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`] raw_bytes_header_entry_mods) >>
  drule_all_then strip_assume_tac raw_bytes_header_saved_entry_mods >>
  qpat_x_assum `dp = Var _` SUBST_ALL_TAC >>
  `esA with gas_obs := [] = esA /\ esD with gas_obs := [] = esD` by
    simp[evaluation_state_component_equality] >>
  `gas_admissible (bind (bind (eval_expr cx d) (read_result cx)) (^raw_suffix av))
     expr_vv_res_ok esA` by
    (BETA_TAC >> qpat_assum `gas_admissible (bind (bind (eval_expr cx a) _) _) _ es`
       (mp_then (Pos hd) (drule_then mp_tac) gas_admissible_bind_tail) >> BETA_TAC >> simp[]) >>
  `gas_admissible (^raw_suffix av (BytesV bs)) expr_vv_res_ok esD` by
    (BETA_TAC >> qpat_assum `gas_admissible (bind (bind (eval_expr cx d) _) _) _ esA`
       (mp_then (Pos hd) (drule_then mp_tac) gas_admissible_bind_tail) >> BETA_TAC >> simp[]) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`G4`, `t4`, `tn4`] >>
  conj_tac
  >- (gen_tac >> first_assum (qspec_then `DF H` ACCEPT_TAC)) >>
  suspend "before_keywords"
QED

Resume raw_call_vv_from_parts_mods[before_keywords]:
  `ci_mono s4 s5` by (qpat_assum `lower_word_args cenv _ kws s4 = _`
       (mp_then Any ACCEPT_TAC bodyFullWordArgsTheory.ci_mono_lower_word_args)) >>
  `s4.cs_next_var >= sa.cs_next_var` by
    (qpat_assum `ci_mono sa s4` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ esD` (assume_tac o BETA_RULE) >>
  `!vs. storage_trace_frame (^raw_next av (BytesV bs) vs)` by
    (BETA_TAC >> simp[storage_trace_frame_ignore_bind,storage_trace_frame_checks,
       storage_trace_frame_bind_all,storage_trace_frame_lifts,storage_trace_frame_raw_call]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  irule (BETA_RULE raw_bytes_keywords_mods) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (s4,s5,_,_)` (irule_at Any) >>
  qpat_assum `lower_word_args cenv _ kws s4 = _` (irule_at Any) >>
  qpat_assum `expr_val_at _ _ _ s1 s2 esD (BytesV bs) data t4` (irule_at Any) >>
  qpat_assum `expr_val_rel cx (BaseT AddressT) av addr t4` (irule_at Any) >>
  qpat_assum `EVERY (safe_operand s4) [addr; len; Var p]` (irule_at Any) >>
  qpat_assum `op_prov G4 (Var p) = SOME _` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4` (irule_at Any) >>
  BETA_TAC >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`dframe`, `b`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_tac >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`reads`,`kvs`,`esK`,`GK`,`tnK`,`tk`] >> strip_tac >>
  suspend "after_keywords"
QED

Resume raw_call_vv_from_parts_mods[after_keywords]:
  `value_has_type (BaseTV AddressT) av` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ a es`
       (mp_then Any mp_tac bodyBopBytestringBindModsTheory.bop_bytestring_operand_source_mods) >>
     disch_then (qspecl_then [`av`,`st0`,`gas_explicit marksA s0.vs_gas_readings`,`esA`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperValueTheory.evaluate_type_def]) >>
  `type_alloc_ok cenv (raw_call_return_type flags)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es`
       (strip_assume_tac o REWRITE_RULE[exprSimHypsDefsTheory.expr_body_pre_mods_def]) >>
     qpat_assum `alloc_limits_expr cenv (Call _ _ _ _)`
       (mp_then Any mp_tac exprSimHypsTheory.alloc_limits_expr_type_alloc_ok) >>
     simp[vyperASTTheory.expr_type_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace) esK.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 esK.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE[storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then (qspec_then `bs` strip_assume_tac)
    (BETA_RULE raw_bytes_reached_tail_inputs_mods) >>
  qpat_assum `expr_sim_full_code _ (s4,s5,h4,h5)`
    (strip_assume_tac o MATCH_MP expr_sim_full_code_fields) >>
  `s4.cs_next_var <= s5.cs_next_var /\ sa.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `ci_mono s4 s5` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     qpat_assum `ci_mono sa s4` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >> decide_tac) >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s4` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  drule_all_then (qspec_then `sa` strip_assume_tac) raw_bytes_outbuf_old_bounds_mods >>
  qpat_assum `!st0 sa sb vv s0 G0 tn0 s6 sout s7 addr dp len gas xs kvs ov op result target bs amount gw ib ob esK t7 G7 tn7. _ ==> _`
    (fn rawth =>
      let
        val req =
          BETA_RULE
            (Q.INST [`go` |-> `ext_call_kwarg EKGas flags.rcf_kws xs`,
                     `source_gas` |-> `ext_call_kwarg EKGas flags.rcf_kws kvs`,
                     `s` |-> `tk`, `G` |-> `GK`, `tn` |-> `tnK`, `ee` |-> `esK`,
                     `ce` |-> `cenv`, `M` |-> `flags.rcf_max_outsize`, `n` |-> `^raw_n`,
                     `s5` |-> `s5`, `s6` |-> `s6`, `sout` |-> `s7`,
                     `h5` |-> `h5`, `h6` |-> `h6`,
                     `ctx` |-> `ctx`, `shctx` |-> `shadow_ctx`, `func` |-> `func`,
                     `shfunc` |-> `shadow_func`, `cx` |-> `cx`, `st0` |-> `st0`,
                     `sa` |-> `sa`, `s0` |-> `s0`, `es` |-> `es`,
                     `G0` |-> `G0`, `tn0` |-> `tn0`, `d` |-> `dframe`,
                     `lo` |-> `lo`, `DF` |-> `DF`,
                     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                     `PG` |-> `PG`, `ov` |-> `ov`, `op` |-> `op`, `gas` |-> `gas`]
              (BETA_RULE raw_request_gas_outbuf_mods))
      in
        assume_tac rawth >>
        SUBGOAL_THEN (lhand (concl req))
          (fn prem =>
            (qx_choose_then `gw`
             (qx_choose_then `t`
              (qx_choose_then `J`
               (qx_choose_then `tf`
                (qx_choose_then `ob`
                 (map_every assume_tac o CONJUNCTS)))))
             (MP req prem)))
      end)
  >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
      >- (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
            (fn th => rewrite_tac [GSYM th]) >>
          qpat_x_assum
            `(case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = _` mp_tac >>
          Cases_on `go` >> simp[])
      >- (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
            (fn th => rewrite_tac [GSYM th]) >>
          qpat_x_assum
            `(case go of NONE => emit_op GAS [] h5 | SOME g => (g,h5)) = _` mp_tac >>
          Cases_on `go` >> simp[])
      >- (qpat_assum
            `!H. valid_horizon _ _ H esK.storage_trace ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            (drule_then strip_assume_tac) >>
          qpat_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`
            (strip_assume_tac o REWRITE_RULE [exprSimPrecompilesTheory.typed_args_post_def]) >>
          (simp[]))
      >- (qpat_assum
            `!H. valid_horizon _ _ H esK.storage_trace ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          simp[NoAsms,exprSimPrecompilesTheory.typed_args_post_def] >>
          metis_tac[])
      >- (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
            (fn th => rewrite_tac [GSYM th]) >>
          first_assum ACCEPT_TAC)
      >- (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
            (fn th => rewrite_tac [GSYM th]) >>
          first_assum ACCEPT_TAC)
      )
  >> `!g. go = SOME g ==> safe_operand s5 g` by
    (gen_tac >> disch_tac >>
     `MEM g xs` by
       (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
          (fn eq => qpat_assum `go = SOME g` (assume_tac o REWRITE_RULE[eq])) >>
        drule_then ACCEPT_TAC raw_call_kwarg_mem) >>
     qpat_assum `EVERY (\op. (!l. op <> Label l) /\ _) xs`
       (mp_tac o REWRITE_RULE[listTheory.EVERY_MEM]) >>
     disch_then (qspec_then `g` mp_tac) >>
     simp[safe_operand_def])
  >> `EVERY (safe_operand s5) [addr;len;Var p;(case vo of NONE => Lit 0w | SOME v => v)] /\
      EVERY (\op. op_taint tnK op = {}) [addr;len;Var p;(case vo of NONE => Lit 0w | SOME v => v)]` by
    (qpat_assum `EVERY (safe_operand s5) [addr;len;Var p]`
       (strip_assume_tac o REWRITE_RULE[listTheory.EVERY_DEF]) >>
     qpat_assum `EVERY (\op. op_taint tnK op = {}) [addr;len;Var p]`
       (strip_assume_tac o BETA_RULE o REWRITE_RULE[listTheory.EVERY_DEF]) >>
     simp[])
  >> drule_all_then strip_assume_tac (Q.INST [`sout` |-> `s7`, `tout` |-> `t`, `M` |-> `^raw_M`,
         `n` |-> `^raw_n`, `ob` |-> `ob`, `value_op` |-> `case vo of NONE => Lit 0w | SOME v => v`]
       raw_bytes_outbuf_saved_input_mods)
  >> `!x. MEM (Var x) [addr;len;Var p;gas;
          case vo of NONE => Lit 0w | SOME v => v;ov;op] ==> not_fresh_at s7 x` by
       qpat_assum `!x. MEM (Var x) _ ==> not_fresh_at s7 x` ACCEPT_TAC
  >> irule ext_request_generated_prefix_mods
  >> conj_tac
  >- (qpat_assum `!vs. storage_trace_frame _`
        (qspec_then `kvs` ACCEPT_TAC))
  >> conj_tac >- first_assum ACCEPT_TAC
  >> qexistsl_tac [`J`,`if IS_NONE go then 1 else 0`,`t`,`tf`]
  >> conj_tac
  >- (`REPLICATE 1 F = [F]` by EVAL_TAC >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (tk,GK,tnK) _ (OK t,J,tf) /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
        (fn eq => qpat_assum `gas_origin_ptr_path _ (tk,GK,tnK) _ (OK t,J,tf)`
                    (mp_tac o REWRITE_RULE[GSYM eq])) >>
      Cases_on `IS_NONE go` >> simp[])
  >> `gas_outcome_full_mods
        (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
        (eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs))
        (esK with gas_obs := [],t,J,tf) ^raw_bytes_Q ^raw_R` by
      (qpat_assum `!st0 sa sb vv s0 G0 tn0 s6 sout s7 addr dp len gas xs kvs ov op result target bs amount gw ib ob esK t7 G7 tn7. _ ==> _`
        (fn rule =>
          let
            fun arg v = case fst (dest_var v) of
                "sout" => ``s7 : compile_state``
              | "ib" => ``b + 32 : num``
              | "dp" => ``Var p : operand``
              | "esK" => ``esK with gas_obs := []``
              | "t7" => ``t : venom_state``
              | "G7" => ``J : (string |-> num # num)``
              | "tn7" => ``tf : taint``
              | _ => v
            val instance = SPECL (map arg (fst (strip_forall (concl rule)))) rule
          in
            qpat_assum `vo = ext_call_kwarg EKValue flags.rcf_kws xs`
              (fn eq => mp_tac (PURE_REWRITE_RULE [GSYM eq,evaluation_state_accfupds] instance))
          end) >>
       (impl_tac >-
         (rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
          >- simp[NoAsms,expr_has_effect_thm]
          >- simp[NoAsms,post_value_type_def]
          >- simp[NoAsms,exprLoweringTheory.lowered_value_type_def]
          >- simp[vyperASTTheory.expr_type_def]
          >- simp[vyperASTTheory.expr_type_def]
          >- (drule_then strip_assume_tac raw_call_pre_operands_flags_mods >> first_assum ACCEPT_TAC)
          >- (drule_then strip_assume_tac raw_call_pre_operands_flags_mods >> first_assum ACCEPT_TAC)
          >- (pure_rewrite_tac[bodyWriteSubscriptSourceModsTheory.write_subscript_source_gas_obs_mods] >>
              first_assum ACCEPT_TAC)
          >- simp[NoAsms,combinTheory.K_THM]
          >- (irule ci_mono_trans >> qexists_tac `s5` >>
              conj_tac >- (irule ci_mono_trans >> qexists_tac `s4` >> simp[]) >> simp[])
          >- simp[ci_mono_refl]
          >- (irule ci_mono_trans >> qexists_tac `s6` >>
              conj_tac >- (irule ci_mono_trans >> qexists_tac `s5` >>
                           conj_tac >- (irule ci_mono_trans >> qexists_tac `s4` >> simp[]) >> simp[]) >> simp[])
          >- simp[]
          >- (gen_tac >> disch_tac >>
              `valid_horizon cx st0 H esD.storage_trace` by
                (qpat_assum `!tail. eval_exprs cx kws _ = _` (qspec_then `[]` mp_tac) >>
                 simp[NoAsms] >>
                 disch_then (mp_then (Pat `f st = (res,st')`) mp_tac valid_horizon_frame) >>
                 simp[cj 6 evaluate_storage_trace_frame]) >>
              `valid_horizon cx st0 H es.storage_trace` by
                (qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> valid_horizon _ _ H es.storage_trace`
                   (drule_then ACCEPT_TAC)) >>
              qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ es s0`
                (drule_then ACCEPT_TAC))
          >- (gen_tac >> disch_tac >>
              qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
                (drule_then strip_assume_tac) >>
              conj_tac >- simp[stmt_state_rel_start_gas_obs] >>
              conj_tac >- (qpat_assum `immutable_frame_mods _ _ _ esK t` mp_tac >>
                pure_rewrite_tac[immutable_frame_mods_def,bodyInvSplitTheory.immutables_rel_mods_def,
                  bodyInvSplitTheory.immutable_alloca_sep_mods_def,immutable_alloca_sep_def,
                  loweringStateRelDefsTheory.immutables_rel_def,evaluation_state_accfupds] >>
                disch_then ACCEPT_TAC) >>
              conj_tac >- (`storage_well_formed_on cx (esK with gas_obs := []) (FST H) <=>
                            storage_well_formed_on cx esK (FST H)` suffices_by simp[] >>
                           irule storage_well_formed_on_backends >> simp[]) >>
              qpat_assum `ghost_inv_at_mods (DF H) lo dframe cenv cx esK J tf t` mp_tac >>
              pure_rewrite_tac[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def,evaluation_state_accfupds] >>
              disch_then ACCEPT_TAC)
          >- (pure_rewrite_tac[exprSimWordArgsTheory.wb_frame_gas_obs] >> first_assum ACCEPT_TAC)
          >- simp[]
          >- simp[]
          >> qpat_assum `cenv.ce_is_ctor ==> !src tops name tv v off. _ ==> regions_disjoint ob _ off _`
               mp_tac >>
             simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM])) >>
       disch_then ACCEPT_TAC)
  >> qpat_assum `_ = eval_raw_call cx flags target bs amount _`
       (fn eq => pure_once_rewrite_tac[eq])
  >> irule bodyRawCalldataRequestModsTheory.calldata_outcome_reset
  >> qpat_assum `gas_outcome_full_mods _ _ _ _ _ (esK with gas_obs := [],t,J,tf) _ _`
       ACCEPT_TAC

QED
Finalise raw_call_vv_from_parts_mods
