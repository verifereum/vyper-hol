(* Join the linked calldata word and copy prefixes at the raw-call entry. *)
Theory bodyRawCalldataRequestMods
Ancestors
  bodyRawCalldataCutsMods bodyRawWordValueVVMods bodyRawCalldataOutbufEntryMods
  bodyRawRequestGasOutbufMods bodyCalldataCopyHeadroomMods bodyCalldataCopyFrameMods
  bodyExtRequestOptionalGasMods gasOutcomeFullPostMods gasExemptCertMods
  bodyRawRequestInputsMods bodyFullPostsMods bodyFullPredsMods exprSimFullBundleProps
  bodyFullIfExpReach rawCallCalldataDalloca dallocaCalldata rawCallOutbufCompile
  exprBodyPreProps exprSafeOperand exprSimPrecompiles exprSimRawCall exprLoweringProps
  vyperCallFrame vyperStorageTrace vyperStorageFootprint vyperTypeSystem
  loweringPosts loweringStateRelDefs gasOutcomeFull gasStorage ptrDiscipline
  fragGasOriginPtr gasShadow fragExec builtinSystem exprLowering compileEnv
  vyperAST vyperInterpreter vyperValue vyperState alist finite_map words list arithmetic
Libs monadsyntax

val calldata_expr = ``Call ann (RawCallCalldataTarget flags) args dflt``;
val calldata_tail = ``\vs. do
  type_check (LENGTH vs = 1 + LENGTH flags.rcf_kws) "raw_call calldata args";
  target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
  amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 1 vs)) "raw_call value";
  eval_raw_call cx flags target cx.txn.calldata amount
    (ext_call_kwarg EKGas flags.rcf_kws (DROP 1 vs))
  od``;

val rc_cap = ``flags.rcf_max_outsize``;
val rc_size = ``if ^rc_cap = 0 then 0 else 32 * ((^rc_cap + 31) DIV 32) + 32``;
val rc_value = ``case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME p => p``;
val rc_gas = ``ext_call_kwarg EKGas flags.rcf_kws (kvs : value list)``;
val rc_kind = ``if flags.rcf_is_delegate then DelegateCall
  else if flags.rcf_is_static then StaticCall else RegularCall``;
val rc_inputs = ``[addr;len;dp;gas;^rc_value]``;
val rc_operands = ``[addr;len;dp;gas;^rc_value;ov;op]``;

val rc_normal = ``\(H : (bool # 256 word # type_value) list # num list) (res : eval_result + vyperState$exception) ee G tn t. ?tv. res = INL tv /\
  vv_post_mods H ctx func cenv cx ^calldata_expr es sa sb s0 ee tv vv t /\
  vv_store_bound cx (post_value_type cenv ^calldata_expr) (lowered_value_type cenv ^calldata_expr) ee tv vv t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo dframe cenv cx ee G tn t /\
  ptr_vv_ok cx (post_value_type cenv ^calldata_expr) tv vv ee G tn t /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^calldata_expr) /\
       ~is_bytestring_type (post_value_type cenv ^calldata_expr) ==>
       vv_own cenv cx (post_value_type cenv ^calldata_expr) sa sb ee tv vv t /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^calldata_expr) = SOME rt /\
             eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  (!t' p. vv = StackValue t' p /\ ~is_word_type (post_value_type cenv ^calldata_expr) ==> ptr_buf_ok cenv ^calldata_expr p G t) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==> ptr_buf_ok cenv ^calldata_expr p.ptr_operand G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val rc_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + vyperState$exception) ee (gt : (string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val calldata_finish_rule = ``
  !st0 sa sb vv s0 G0 tn0 s6 sout s7 addr dp len gas xs kvs ov op result
     target bs amount gw ib ob esK t7 G7 tn7.
  expr_has_effect ^calldata_expr /\ post_value_type cenv ^calldata_expr = expr_type ^calldata_expr /\
  lowered_value_type cenv ^calldata_expr = expr_type ^calldata_expr /\
  expr_type ^calldata_expr = raw_call_return_type flags /\
  type_alloc_ok cenv (expr_type ^calldata_expr) /\ ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\ (flags.rcf_is_static ==> amount = 0) /\
  amount < dimword (:256) /\ ^rc_cap < dimword (:256) /\
  expr_sim_inv_mods mods cenv cx env esK /\ esK.gas_obs = [] /\
  storage_trace_domain cx st0 esK.storage_trace /\
  fn_has_code sa sb func /\ fn_has_code s6 sout func /\ fn_inst_ids_distinct func /\
  ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\ ci_mono sa s7 /\
  compile_raw_call_outbuf ^rc_cap s6 = ((ov,op),sout) /\
  compile_raw_call_finish addr dp len gas ^rc_value ^rc_kind ^rc_cap flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  vv = (if ^rc_cap = 0 then StackValue (raw_call_return_type flags) result
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
  eval_operand addr t7 = SOME (w2w target) /\ eval_operand ^rc_value t7 = SOME (n2w amount) /\
  eval_operand gas t7 = SOME gw /\ (!g. OPTION_BIND ^rc_gas dest_NumV = SOME g ==> g = w2n gw) /\
  eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
  ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\ w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
  read_memory ib (LENGTH bs) t7 = bs /\ (!j. ib <= j /\ j < ib + LENGTH bs ==> j NOTIN tn7.t_mem) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
  eval_operand ov t7 = SOME (n2w ob) /\ eval_operand op t7 = SOME (n2w (if ^rc_cap = 0 then ob else ob + 32)) /\
  (^rc_cap = 0 ==> ov = op) /\ ob + ^rc_size < dimword (:256) /\
  FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,^rc_size) /\
  op_prov G7 ov = SOME (ob,^rc_size) /\ op_prov G7 op = SOME (ob,^rc_size) /\
  op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> regions_disjoint ob ^rc_size lb sz) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob ^rc_size) /\
  EVERY (\x. op_taint tn7 x = {}) ^rc_inputs /\ EVERY (safe_operand s7) ^rc_operands /\
  (!x. MEM (Var x) ^rc_operands ==> not_fresh_at s7 x) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_raw_call cx flags target bs amount ^rc_gas) (esK,t7,G7,tn7) ^rc_normal ^rc_exit``;

Triviality calldata_tail_frame:
  !vs. storage_trace_frame ((^calldata_tail) vs)
Proof
  gen_tac >> BETA_TAC >> irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts,storage_trace_frame_raw_call]
QED

Triviality calldata_tail_value:
  (^calldata_tail) vs st = (INL pv,st') ==> ?v. pv = Value v
Proof
  BETA_TAC >> simp[ignore_bind_def,bind_def,type_check_def,assert_def,lift_option_type_def] >>
  Cases_on `LENGTH vs = 1 + LENGTH flags.rcf_kws` >> simp[raise_def,return_def] >>
  Cases_on `dest_AddressV (HD vs)` >> simp[raise_def,return_def] >>
  Cases_on `raw_call_value flags.rcf_kws (DROP 1 vs)` >> simp[raise_def,return_def] >>
  MATCH_ACCEPT_TAC eval_raw_call_success_value
QED

Theorem raw_calldata_vv_from_parts_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env ^calldata_expr es /\ body_exprs_full_ok_mods mods exps cx args /\
  ^calldata_finish_rule ==>
  expr_vv_sim_full_mods (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^calldata_expr es
Proof
  strip_tac >> rw[expr_vv_sim_full_mods_def] >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "prefix" >>
  irule gas_outcome_full_mods_bad_nil >> simp[] >>
  qmatch_goalsub_abbrev_tac `SND (action _)` >>
  `storage_trace_frame action` by simp[Abbr `action`,evaluate_storage_trace_frame] >>
  drule_all_then mp_tac gas_bad_storage_at_initial >>
  disch_then (qspecl_then [`s0`,`[]`] mp_tac o REWRITE_RULE [gas_bad_storage_at_def]) >> simp[]
QED

Resume raw_calldata_vv_from_parts_mods[prefix]:
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then strip_assume_tac raw_calldata_request_cuts_mods >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  qpat_x_assum `dflt = _` SUBST_ALL_TAC >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  qpat_x_assum `gas_admissible (eval_expr _ _) _ _`
    (assume_tac o PURE_REWRITE_RULE [raw_calldata_source_bind]) >>
  pure_rewrite_tac[raw_calldata_source_bind] >>
  irule request_word_value_vv_prefix_mods >> BETA_TAC >>
  suspend "word_premises"
QED

Resume raw_calldata_vv_from_parts_mods[word_premises]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE calldata_tail_value)) >>
  conj_tac >- MATCH_ACCEPT_TAC (BETA_RULE calldata_tail_frame) >>
  simp[] >>
  conj_tac
  >- (fs[EVERY_MEM,is_word_type_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qexistsl_tac [`expr_type`,`dframe`,`env`,`exps`,`mods`,`sa`,`s2`,`shadow_func`,
                `shadow_sa`,`h2`,`src`,`tops`,`addr::xs`] >>
  simp[gasShadowTheory.gas_shadow_expr_type] >>
  conj_tac >- (rpt strip_tac >> irule request_operand_pre_mods >>
    qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  reverse conj_tac >- (drule expr_body_pre_mods_inv >> disch_tac >>
    conj_tac >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _` (drule_then strip_assume_tac) >> simp[]) >>
    pure_rewrite_tac[GSYM MAP] >> conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "reached_words"
QED

Resume raw_calldata_vv_from_parts_mods[reached_words]:
  qx_genl_tac [`reads`,`vs`,`ee`,`GK`,`tnK`,`tk`] >> strip_tac >>
  qpat_assum `expr_sim_full_code _ (sa,s2,shadow_sa,h2)`
    (strip_assume_tac o MATCH_MP expr_sim_full_code_fields) >>
  rpt (qpat_x_assum `(\a b c d e. _) _ _ _ _ _` (strip_assume_tac o BETA_RULE)) >>
  rpt (qpat_x_assum `(\a b c d e f. _) _ _ _ _ _ _` (strip_assume_tac o BETA_RULE)) >>
  `type_alloc_ok cenv (raw_call_return_type flags)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` mp_tac >>
     simp[NoAsms,exprSimHypsDefsTheory.expr_body_pre_mods_def,
          allocLimitsTheory.alloc_limits_expr_def,expr_type_def]) >>
  `EVERY (safe_operand s2) (addr::xs)` by
    (qpat_assum `EVERY (\op. (!l. op <> Label l) /\ _) _` mp_tac >>
     simp[NoAsms,EVERY_MEM,safe_operand_def] >> metis_tac[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >> simp[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx` by
    (`a::kws <> []` by simp[] >>
     drule_all_then strip_assume_tac compile_expr_raw_call_calldata_dalloca >>
     fs[ctx_has_dalloca_def,EXISTS_MEM] >> metis_tac[]) >>
  qabbrev_tac `M = flags.rcf_max_outsize` >>
  qabbrev_tac `payload = if M = 0 then 0 else 32 * ((M+31) DIV 32) + 32` >>
  mp_tac (Q.INST [`M` |-> `M`, `payload` |-> `payload`, `d` |-> `dframe`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `P` |-> `\tout Gout tnout ob gw. !name lb sz. local_region cenv ee.scopes tout name lb sz ==>
                             regions_disjoint ob payload lb sz`]
    raw_calldata_outbuf_from_words_mods) >>
  BETA_TAC >>
  (impl_tac >- suspend "outbuf_premises") >>
  strip_tac >> suspend "copy_entry"
QED

Resume raw_calldata_vv_from_parts_mods[outbuf_premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[Abbr `M`,Abbr `payload`] >> NO_TAC) >>
  TRY (qmatch_goalsub_rename_tac `LIST_REL _ (a::kws) vs` >>
       simp[] >> NO_TAC) >>
  FAIL_TAC "common run"
QED

Resume raw_calldata_vv_from_parts_mods[copy_entry]:
  FAIL_TAC "copy entry"
QED

Finalise raw_calldata_vv_from_parts_mods
