(* Join the reached byte-input prefix with an independently supplied finish. *)
Theory bodyRawBytesRequestMods
Ancestors
  bodyRawBytesRequestCutsMods bodyRawBytesForcedReadsMods
  bodyRawBytesHeaderEntryMods bodyRawBytesKeywordsMods bodyRawRequestGasOutbufMods
  bodyECRecoverForcedTailMods bodyForcedStorageFrameMods
  gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods bodyExtRequestOptionalGasMods
  exprSimFullBundleProps exprBodyPreProps exprSimSliceCompose stmtSimForRounds
  bodyFullPostsMods bodyFullPredsMods vyperStorageTrace vyperStorageFootprint
  exprSimRawCall exprOperandVar exprSimWordArgs loweringPosts bodyPtrDefs bodyMemoryDefs
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
  drule_then assume_tac slice_gas_admissible_expr_head >>
  qpat_assum `expr_sim_full_code _ (sa,s1,shadow_sa,h1)`
    (strip_assume_tac o MATCH_MP expr_sim_full_code_fields) >>
  `expr_body_pre_mods mods cenv cx env a es` by
    (irule bodyRawRequestInputsModsTheory.request_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
     simp[] >> drule expr_body_pre_mods_inv >> simp[]) >>
  `body_expr_full_ok_mods mods exps cx a` by
    fs[body_exprs_full_ok_mods_def] >>
  `expr_sim_full_mods (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT AddressT) a es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ a`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     first_x_assum (irule o cj 1 o UNDISCH_ALL o SPEC_ALL) >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`h1`,`addr`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE[expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  ho_match_mp_tac raw_bytes_forced_reads_mods >>
  FAIL_TAC "inspect the two-read composition"
QED
