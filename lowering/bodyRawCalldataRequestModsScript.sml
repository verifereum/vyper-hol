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

(* Entry observations are overwritten by replay, including exempt replay. *)
Theorem calldata_outcome_reset:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es with gas_obs := [],s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R
Proof
  `!gs. (es with gas_obs := []) with gas_obs := gs = es with gas_obs := gs` by
    simp[NoAsms,vyperStateTheory.evaluation_state_component_equality] >>
  pop_assum (fn eq => pure_rewrite_tac[gasOutcomeFullModsTheory.gas_outcome_full_mods_def,
                    gas_bad_storage_at_def,evaluation_state_accfupds,eq]) >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      conj_tac >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  reverse conj_tac >- (qexists_tac `H` >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule gas_exempt_cert_start_gas_obs_mods >>
  disch_then (qspec_then `es.gas_obs` mp_tac) >>
  simp[NoAsms,vyperStateTheory.evaluation_state_component_equality]
QED

(* Fix the copy-frame rule at selected endpoints before checking its premises. *)
fun apply_copy_frame h =
  let
    val rule = SPEC_ALL (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
                calldata_copy_finish_frame_mods))
    val address_read =
      List.find (can (match_term ``eval_operand _ _ = SOME (w2w target)``))
        (strip_conj (lhand (concl rule))) |> valOf
    val anchors = ``
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
      stmt_state_rel H0 ctx func cenv cx es s0 /\
      stmt_state_rel H ctx func cenv cx ee s /\
      ghost_inv_at_mods D lo d cenv cx ee G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      local_ptrs_reserved cenv sm /\
      FLOOKUP s.vs_allocas s6.cs_next_id = SOME (ob,sz) /\
      sz = (if cap = 0 then 0 else 32 * ((cap + 31) DIV 32) + 32) /\
      EVERY (\p. op_taint tn p = {}) [addr;value;gas;ov;op] /\
      ^address_read /\
      eval_operand value s = SOME (n2w amount) /\ eval_operand gas s = SOME gw /\
      eval_operand dp t = SOME s.vs_fmp /\ eval_operand len t = SOME (n2w (LENGTH cx.txn.calldata))``
    fun pick facts [] =
          let val instance = INST_TY_TERM (match_term anchors (list_mk_conj (rev facts))) rule
          in SUBGOAL_THEN (lhand (concl instance)) (assume_tac o MP instance) end
      | pick facts (pat::pats) = qpat_assum pat (fn th => pick (concl th::facts) pats)
  in
    pick [] [
      `gas_origin_ptr_path (DF ^h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
                          (tout,Gout,tnout) [] (OK t7,G7,tn7)`,
      `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0`,
      `stmt_state_rel ^h ctx func cenv cx ee tout`,
      `ghost_inv_at_mods (DF ^h) lo dframe cenv cx ee Gout tnout tout`,
      `ghost_kept_at lo cenv es sa G0 tn0 s0 Gout tnout`,
      `local_ptrs_reserved cenv s4`,
      `FLOOKUP tout.vs_allocas s3.cs_next_id = SOME (ob,payload)`,
      `payload = if M = 0 then 0 else 32 * ((M+31) DIV 32) + 32`,
      `EVERY (\p. op_taint tnout p = {}) [addr;value;gas;ov;op]`,
      `eval_operand addr tout = SOME (w2w target)`,
      `eval_operand value tout = SOME (n2w amount)`, `eval_operand gas tout = SOME gw`,
      `eval_operand dp t7 = SOME tout.vs_fmp`,
      `eval_operand len t7 = SOME (n2w (LENGTH cx.txn.calldata))`]
  end

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
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- simp[Abbr `M`]
  >- simp[Abbr `payload`]
  >- simp[]
  >- simp[] >>
  `sa.cs_next_var <= s3.cs_next_var` by
    (qpat_assum `ci_mono sa s2` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono s2 s3` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `wb_frame cenv es ee sa s0 tk` by fs[typed_args_post_def] >>
  `sa.cs_next_var <= s2.cs_next_var` by fs[ci_mono_def] >>
  `return_buf_frame dframe cenv s2 tk` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >> fs[wb_frame_def]) >>
  `local_ptrs_reserved cenv s2` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  rpt (qpat_x_assum `(\a b c d e f g. _) _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee tk /\ immutable_frame_mods func cenv cx ee tk /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo dframe cenv cx ee GK tnK tk` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[typed_args_post_def]) >>
  `!x. go = SOME (Var x) ==> not_fresh_at s2 x` by
    (rpt strip_tac >> qpat_assum `!p. go = SOME p ==> _` (drule_then strip_assume_tac) >>
     fs[safe_operand_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[GSYM storage_trace_domain_def] >>
  `local_ptrs_rel func cenv es.scopes s0 /\ alloca_inv s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off + sz <= tk.vs_alloca_next` by
    (rpt strip_tac >> fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     `off + sz <= s0.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `!name base sz. local_region cenv es.scopes s0 name base sz ==>
      base + sz <= tk.vs_alloca_next` by
    (rpt strip_tac >> rename1 `local_region cenv es.scopes s0 name lb sz` >>
     `lb + sz <= s0.vs_alloca_next` by
       metis_tac[exprSimConvertFromBytesTheory.dynamic_local_region_bound] >>
     decide_tac) >>
  `payload = (if M = 0 then 0 else ((M+31) DIV 32)*32+32)` by
    simp[Abbr `payload`,MULT_COMM] >>
  (let
     val rule = Q.INST [`source_gas` |-> `ext_call_kwarg EKGas flags.rcf_kws (DROP 1 vs)`,
       `n` |-> `payload`, `s5` |-> `s2`, `s6` |-> `s3`, `sout` |-> `s4`,
       `h5` |-> `h2`, `h6` |-> `h3`, `shctx` |-> `shadow_ctx`, `shfunc` |-> `shadow_func`,
       `ce` |-> `cenv`, `d` |-> `dframe`, `s` |-> `tk`, `G` |-> `GK`, `tn` |-> `tnK`]
       (BETA_RULE raw_request_gas_outbuf_mods)
   in SUBGOAL_THEN (lhand (concl rule)) (strip_assume_tac o MP rule) end)
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rename1 `eval_operand gas tout = SOME gw` >>
  rename1 `FLOOKUP tout.vs_allocas s3.cs_next_id = SOME (ob,payload)` >>
  rename1 `op_prov Gout ov = SOME (ob,payload)` >>
  rename1 `op_taint tnout gas = {}` >>
  `!p. safe_operand s2 p ==> eval_operand p tout = eval_operand p tk /\
       op_prov Gout p = op_prov GK p /\ op_taint tnout p = op_taint tnK p` by
    (Cases >> simp[safe_operand_def,venomStateTheory.eval_operand_def,op_prov_def,op_taint_def] >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x tout = _ /\ _`
       (drule_then strip_assume_tac) >> fs[op_taint_def]) >>
  `return_buf_frame dframe cenv sa tout` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_assum `wb_frame cenv es ee sa s0 tout` (mp_tac o REWRITE_RULE [wb_frame_def]) >>
     simp[NoAsms]) >>
  qexistsl_tac [`tout`,`Gout`,`tnout`,`ob`,`gw`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  Cases_on `go` >- simp[NoAsms] >>
  simp[NoAsms] >> rename1 `eval_operand gasop tk = SOME gw` >>
  `safe_operand s2 gasop` by
    (qpat_assum `!p. go = SOME p ==> safe_operand s2 p /\ _`
       (qspec_then `gasop` mp_tac) >> simp[]) >>
  `gasop = gas` by
    (qpat_assum `(case SOME gasop of NONE => emit_op GAS [] s2 | SOME r => (r,s2)) = (gas,s3)` mp_tac >>
     simp[NoAsms]) >>
  qpat_assum `!p. safe_operand s2 p ==> eval_operand p tout = _ /\ _`
    (qspec_then `gasop` drule) >> disch_then strip_assume_tac >>
  qpat_x_assum `gasop = gas` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `eval_operand gasop tout = eval_operand gasop tk`
    (fn th => once_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC
QED

Resume raw_calldata_vv_from_parts_mods[copy_entry]:
  `allocas_below_fmp tout /\ w2n tout.vs_initial_fmp <= w2n tout.vs_fmp` by
    (qpat_assum `ctx_has_dalloca ctx ==> _ /\ _` (drule_then ACCEPT_TAC)) >>
  rpt (qpat_x_assum `(\a b c d e f g. _) _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE)) >>
  drule_all calldata_copy_from_headroom >>
  disch_then (qspecl_then [`tnout`,`PG`,`Gout`] strip_assume_tac) >>
  rename1 `eval_operand dp t7 = SOME tout.vs_fmp` >>
  rename1 `op_taint tn7 len = {}` >>
  rename1 `op_prov G7 len = NONE` >>
  qabbrev_tac `value = case vo of NONE => Lit 0w | SOME q => q` >>
  `sa.cs_next_var <= s4.cs_next_var` by
    (`ci_mono sa s4` by metis_tac[ci_mono_trans] >>
     qpat_assum `ci_mono sa s4` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[NoAsms]) >>
  `!x. MEM (Var x) [addr;value;gas;ov;op] ==> not_fresh_at s4 x` by
    (rpt strip_tac >>
     qpat_assum `EVERY (safe_operand s4) [addr;value;gas;ov;op]`
       (mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `Var x` drule) >> simp[NoAsms,safe_operand_def]) >>
  `EVERY (\p. op_taint tnout p = {}) [addr;value;gas;ov;op]` by
    simp[Abbr `value`] >>
  `local_ptrs_reserved cenv s4` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s4 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `s0.vs_alloca_next <= tout.vs_alloca_next` by decide_tac >>
  `t7.vs_memory = (write_memory_with_expansion (w2n tout.vs_fmp) cx.txn.calldata tout).vs_memory` by
    (qpat_assum `tout.vs_call_ctx.cc_calldata = cx.txn.calldata`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  `cx.txn.calldata <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH cx.txn.calldata)` by
    (qpat_assum `tout.vs_call_ctx.cc_calldata = cx.txn.calldata`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> strip_tac >>
     qexists_tac `p` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  Q.SUBGOAL_THEN
    `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = s3.cs_next_id`
    assume_tac
  >- (qpat_assum `compile_raw_call_outbuf M s3 = ((ov,op),s4)`
       (mp_then Any strip_assume_tac calldata_outbuf_compile) >>
     rename1 `compile_alloc_buffer _ s3 = (buf,sm)` >>
     `cs_extends s3 sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
     `cs_extends sm s4` by
       (qpat_assum `if _ then op = ov /\ s4 = sm else _` mp_tac >>
        Cases_on `M = 0`
        >- (qpat_assum `M = 0` (fn th => simp[NoAsms,th]) >>
            strip_tac >> asm_rewrite_tac[compileEnvTheory.cs_extends_refl]) >>
        qpat_assum `M <> 0` (fn th => simp[NoAsms,th]) >>
        disch_then (mp_then Any (ACCEPT_TAC o CONJUNCT1) exprSimAccountsTheory.emit_op_extends_next_var)) >>
     `fn_has_code s3 sm func` by metis_tac[fn_has_code_split] >>
     `payload < dimword (:256)` by decide_tac >>
     `payload = (if M = 0 then 0 else ((M+31) DIV 32)*32+32)` by simp[Abbr `payload`,MULT_COMM] >>
     `compile_alloc_buffer payload s3 = (buf,sm)` by
       (qpat_assum `payload = if M = 0 then _ else _` (PURE_REWRITE_TAC o single) >>
        first_assum ACCEPT_TAC) >>
     drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
     strip_tac >> qexists_tac `mk_inst s3.cs_next_id ALLOCA [Lit (n2w payload)] [out]` >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms,venomInstTheory.mk_inst_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee.storage_trace` mp_tac >>
     simp[NoAsms,storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspecl_then [`storage_trace_horizon ee.storage_trace`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `gas_origin_ptr_path (DF (storage_trace_horizon ee.storage_trace),lo,
       gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (tout,Gout,tnout) [] (OK t7,G7,tn7)` by
    (first_assum MATCH_ACCEPT_TAC) >>
  `payload = (if M = 0 then 0 else 32 * ((M+31) DIV 32) + 32)` by
    simp[Abbr `payload`] >>
  `eval_operand len t7 = SOME (n2w (LENGTH cx.txn.calldata))` by
    (qpat_assum `tout.vs_call_ctx.cc_calldata = cx.txn.calldata`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  apply_copy_frame ``storage_trace_horizon ee.storage_trace``
  >- (rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       (qpat_assum `tout.vs_call_ctx.cc_calldata = cx.txn.calldata`
          (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC))) >>
  pop_assum (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t7 /\ immutable_frame_mods func cenv cx ee t7 /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo dframe cenv cx ee G7 tn7 t7` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (tout,Gout,tnout) [] (OK t7,G7,tn7)` by first_assum MATCH_ACCEPT_TAC >>
     apply_copy_frame ``H:(bool # bytes32 # type_value) list # num list``
     >- (rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE
          (qpat_assum `tout.vs_call_ctx.cc_calldata = cx.txn.calldata`
             (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC))) >>
     pop_assum (MAP_EVERY assume_tac o CONJUNCTS) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "finish_entry"
QED

Resume raw_calldata_vv_from_parts_mods[finish_entry]:
  `ci_mono sa s3 /\ ci_mono s3 s5 /\ ci_mono sa s5` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ci_mono sa s2`,`ci_mono s2 s3`,`ci_mono s3 s4`,`ci_mono s4 s5`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[ci_mono_trans]) >>
  `safe_operand s5 len /\ safe_operand s5 dp` by
    (qpat_assum `compile_msg_data_to_memory s4 = ((dp,len),s5)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> disch_tac >>
     drule dallocaCalldataTheory.calldata_memory_insts >> strip_tac >>
     drule bodyFullRawCallCalldataCopyTheory.calldata_memory_placement >> strip_tac >>
     simp[not_fresh_at_def,safe_operand_def,ASCIInumbersTheory.toString_11] >> decide_tac) >>
  `EVERY (safe_operand s5) [addr;value;gas;ov;op]` by
    (qpat_assum `EVERY (safe_operand s4) _` mp_tac >>
     qpat_assum `ci_mono s4 s5` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM,ci_mono_def] >> metis_tac[safe_operand_mono]) >>
  `EVERY (safe_operand s5) [addr;len;dp;gas;value;ov;op]` by
    (qpat_assum `EVERY (safe_operand s5) [addr;value;gas;ov;op]`
       (strip_assume_tac o PURE_REWRITE_RULE [EVERY_DEF]) >> simp[]) >>
  `!x. MEM (Var x) [addr;len;dp;gas;value;ov;op] ==> not_fresh_at s5 x` by
    (gen_tac >> disch_tac >>
     qpat_assum `EVERY (safe_operand s5) [addr;len;dp;gas;value;ov;op]`
       (mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `Var x` drule) >> simp[NoAsms,safe_operand_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `!tail. eval_exprs cx (a::kws) _ = _` (qspec_then `[]` mp_tac) >>
        simp[NoAsms] >>
        disch_then (mp_then (Pat `f st = (res,st')`) mp_tac valid_horizon_frame) >>
        simp[cj 6 evaluate_storage_trace_frame]) >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `^rc_value = value` by
    (qpat_assum `vo = ext_call_kwarg EKValue flags.rcf_kws xs`
       (fn th => simp[NoAsms,Abbr `value`,GSYM th])) >>
  qpat_assum `!st0 sa sb vv. _`
    (fn rule =>
      let
        fun arg v = case fst (dest_var v) of
            "s6" => ``s3 : compile_state``
          | "sout" => ``s4 : compile_state``
          | "s7" => ``s5 : compile_state``
          | "bs" => ``cx.txn.calldata``
          | "ib" => ``w2n tout.vs_fmp``
          | "esK" => ``ee with gas_obs := []``
          | _ => v
        val instance = SPECL (map arg (fst (strip_forall (concl rule)))) rule
      in qpat_assum `^rc_value = value` (fn eq =>
        let val clean = PURE_REWRITE_RULE [eq,evaluation_state_accfupds] instance
        in SUBGOAL_THEN (lhand (concl clean)) (assume_tac o MP clean) end)
      end)
  >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
      >- simp[NoAsms,expr_has_effect_thm]
      >- simp[NoAsms,post_value_type_def]
      >- simp[NoAsms,lowered_value_type_def]
      >- simp[NoAsms,expr_type_def]
      >- (pure_rewrite_tac[expr_type_def] >> first_assum ACCEPT_TAC)
      >- (disch_tac >> qpat_assum `_ \/ _ ==> amount = 0` irule >> disj1_tac >> first_assum ACCEPT_TAC)
      >- (disch_tac >> qpat_assum `_ \/ _ ==> amount = 0` irule >> disj2_tac >> first_assum ACCEPT_TAC)
      >- (pure_rewrite_tac[bodyWriteSubscriptSourceModsTheory.write_subscript_source_gas_obs_mods] >>
          first_assum ACCEPT_TAC)
      >- simp[NoAsms,combinTheory.K_THM]
      >- (gen_tac >> disch_tac >>
          qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee t7 /\ _`
            (drule_then strip_assume_tac) >>
          conj_tac >- simp[stmt_state_rel_start_gas_obs] >>
          conj_tac >- (qpat_assum `immutable_frame_mods _ _ _ ee t7` mp_tac >>
            pure_rewrite_tac[immutable_frame_mods_def,bodyInvSplitTheory.immutables_rel_mods_def,
                 bodyInvSplitTheory.immutable_alloca_sep_mods_def,immutable_alloca_sep_def,
                 loweringStateRelDefsTheory.immutables_rel_def,evaluation_state_accfupds] >>
            disch_then ACCEPT_TAC) >>
          conj_tac >- (`storage_well_formed_on cx (ee with gas_obs := []) (FST H) <=>
                         storage_well_formed_on cx ee (FST H)` suffices_by simp[] >>
                       irule storage_well_formed_on_backends >> simp[]) >>
          qpat_assum `ghost_inv_at_mods (DF H) lo dframe cenv cx ee G7 tn7 t7` mp_tac >>
          pure_rewrite_tac[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def,evaluation_state_accfupds] >>
          disch_then ACCEPT_TAC)
      >- (pure_rewrite_tac[exprSimWordArgsTheory.wb_frame_gas_obs] >> first_assum ACCEPT_TAC)
      >- (qpat_assum `case ext_call_kwarg EKGas flags.rcf_kws kvs of NONE => _ | SOME gv => _` mp_tac >>
          Cases_on `ext_call_kwarg EKGas flags.rcf_kws kvs` >> simp[NoAsms])
      >- (qpat_assum `LENGTH cx.txn.calldata = 0 \/ _` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> metis_tac[])
      >> qpat_assum `EVERY (\p. op_taint tn7 p = {}) [addr;len;dp;gas;value;ov;op]`
           (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE [EVERY_DEF]) >> simp[]) >>
  suspend "finish_prefix"
QED

Resume raw_calldata_vv_from_parts_mods[finish_prefix]:
  `REPLICATE 1 F = [F]` by EVAL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (tk,GK,tnK) (REPLICATE (if IS_NONE go then 1 else 0) F) (OK t7,G7,tn7)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (tk,GK,tnK) _ (OK tout,Gout,tnout)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`tout`,`Gout`,`tnout`,`[]`] mp_tac) >>
     simp[NoAsms] >>
     disch_then (qspecl_then [`OK t7`,`G7`,`tn7`] mp_tac) >>
     (impl_tac >- first_assum MATCH_ACCEPT_TAC) >>
     Cases_on `go` >> simp[]) >>
  qpat_assum `vs = av::kvs` (fn vs_eq =>
    qpat_assum `_ = eval_raw_call cx flags target cx.txn.calldata amount _` (fn th =>
      let val rw = [vs_eq,HD,EL,prim_recTheory.PRE,
                    Q.SPECL [`1`,`LENGTH flags.rcf_kws`] ADD_COMM]
      in pure_rewrite_tac rw >> pure_once_rewrite_tac[PURE_REWRITE_RULE rw th] end)) >>
  irule ext_request_generated_prefix_mods >>
  conj_tac >- simp[NoAsms,storage_trace_frame_raw_call] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G7`,`if IS_NONE go then 1 else 0`,`t7`,`tn7`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule calldata_outcome_reset >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ (ee with gas_obs := [],t7,G7,tn7) _ _` mp_tac >>
  qpat_assum `vv = if M = 0 then _ else _` (fn eq => simp[NoAsms,eq,post_value_type_def,ADD_COMM])
QED

Finalise raw_calldata_vv_from_parts_mods
