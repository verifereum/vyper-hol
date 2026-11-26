(* From a reached calldata word list to the shared GAS/outbuf endpoint. *)
Theory bodyRawCalldataOutbufEntryMods
Ancestors
  bodyRawRequestWordsMods bodyFullRawCallRequestGas bodyFullHashKeccakFixed
  allocLimits exprSafeOperand stateRelProj venomMemProps vyperTypeExtCallSoundness
  vyperTypeInvariants vyperTyping vyperValue valueEncoding words list arithmetic
  exprSimPrecompiles exprSimSend vyperInterpreter exprSimRawCall vyperTypeSystem
  vyperState exprSimHypsDefs loweringStateRelDefs venomMemDefs bodyFullShadowBodyInv
  bodyFullIfExpReach fragGasOriginPtr gasShadowCompile vyperStorageFootprint
  allocaHistory bodyPtrDefs ptrDiscipline exprLowering finite_map pred_set
  exprLoweringProps builtinSystem loweringHalt context pair loweringPosts gasOutcomeFull
Libs monadsyntax

Triviality calldata_address_word:
  value_has_type (BaseTV AddressT) v ==>
  ?target. dest_AddressV v = SOME target /\
    typed_val_to_w256 (BaseTV AddressT) v = (w2w target : 256 word)
Proof
  Cases_on `v` >> simp[value_has_type_def,dest_AddressV_def] >>
  strip_tac >> simp[typed_val_to_w256_def] >>
  qspec_then `l` mp_tac
    (INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]
      w2w_word_of_bytes_be_pad_left) >>
  simp[dividesTheory.compute_divides, fcpLib.INDEX_CONV ``dimindex(:160)``,EQ_SYM_EQ]
QED

Triviality calldata_decode_word_list:
  expr_type a = BaseT AddressT /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                      value_has_type tv v) (a::kws) vs /\
  typed_args_post H ctx func cenv cx es sa s0 ee (a::kws) (addr::xs) vs tk ==>
  ?av kvs target. vs = av::kvs /\ dest_AddressV av = SOME target /\
    eval_operand addr tk = SOME (w2w target) /\ LENGTH kvs = LENGTH kws /\
    EVERY (value_has_type (BaseTV (UintT 256))) kvs /\
    LIST_REL (\x v. eval_operand x tk = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs kvs
Proof
  Cases_on `vs` >> simp[typed_args_post_def,vyperValueTheory.evaluate_type_def] >>
  strip_tac >> gvs[evaluate_type_def] >>
  drule calldata_address_word >> strip_tac >> simp[] >>
  conj_tac
  >- (fs[EVERY_EL,LIST_REL_EL_EQN] >> rpt strip_tac >>
      `expr_type (EL n kws) = BaseT (UintT 256)` by simp[] >>
      qpat_x_assum `!j. _ ==> ?tv. _` (qspec_then `n` mp_tac) >>
      simp[evaluate_type_def]) >>
  gvs[EVERY_EL,LIST_REL_EL_EQN,LENGTH_ZIP] >> rpt strip_tac >>
  `expr_type (EL n kws) = BaseT (UintT 256)` by fs[] >>
  qpat_x_assum `!j. _ ==> eval_operand _ _ = _` (qspec_then `n` mp_tac) >>
  simp[EL_ZIP,evaluate_type_def]
QED

Triviality aligned_kwarg_absence:
  !ks (xs : 'a list) (vs : 'b list).
    LENGTH xs = LENGTH vs ==>
    (ext_call_kwarg kw ks vs = NONE <=> ext_call_kwarg kw ks xs = NONE)
Proof
  Induct >> Cases_on `xs` >> Cases_on `vs` >> simp[ext_call_kwarg_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Triviality calldata_gas_selection:
  LIST_REL (\x v. eval_operand x tk = SOME
    (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs kvs /\
  EVERY (value_has_type (BaseTV (UintT 256))) kvs /\
  EVERY (\x. op_prov GK x = NONE /\ op_taint tnK x = {}) xs /\
  go = ext_call_kwarg EKGas ks xs ==>
  (case ext_call_kwarg EKGas ks kvs of NONE => go = NONE
   | SOME gv => ?op w. go = SOME op /\ eval_operand op tk = SOME w /\
       dest_NumV gv = SOME (w2n w) /\ op_taint tnK op = {})
Proof
  strip_tac >> Cases_on `ext_call_kwarg EKGas ks kvs` >> simp[]
  >- metis_tac[aligned_kwarg_absence,LIST_REL_LENGTH] >>
  `LIST_REL (\op v. ?w. eval_operand op tk = SOME w /\
      dest_NumV v = SOME (w2n w)) xs kvs` by
    (fs[LIST_REL_EL_EQN,EVERY_EL] >> rpt strip_tac >>
     simp[uint256_typed_dest]) >>
  drule_all raw_call_selected_gas_word >> strip_tac >> gvs[] >>
  drule raw_call_kwarg_mem >> fs[EVERY_MEM]
QED

Triviality calldata_payload_bound:
  type_alloc_ok cenv (raw_call_return_type flags) ==>
  (if flags.rcf_max_outsize = 0 then 0
   else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) < dimword (:256)
Proof
  Cases_on `flags.rcf_max_outsize = 0` >> simp[] >>
  Cases_on `flags.rcf_revert_on_failure` >>
  simp[raw_call_return_type_def,allocLimitsTheory.type_alloc_ok_def,
       compileEnvTheory.is_word_type_def,compileEnvTheory.type_memory_bytes_def] >>
  qabbrev_tac `rounded = 32 * ((flags.rcf_max_outsize + 31) DIV 32)` >>
  strip_tac >> irule LESS_TRANS >> qexists_tac `2 ** 64` >>
  simp[dimword_def] >> decide_tac
QED

(* Pure part of the reached continuation. *)
val checked_calldata_tail = ``\cx flags vs. do
  type_check (LENGTH vs = 1 + LENGTH flags.rcf_kws) "raw_call calldata args";
  target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
  amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 1 vs)) "raw_call value";
  eval_raw_call cx flags target cx.txn.calldata amount
    (ext_call_kwarg EKGas flags.rcf_kws (DROP 1 vs))
  od``;

Triviality calldata_tail_checks:
  LENGTH kvs = LENGTH flags.rcf_kws /\ dest_AddressV av = SOME target /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  (^checked_calldata_tail) cx flags (av::kvs) =
    eval_raw_call cx flags target cx.txn.calldata amount
      (ext_call_kwarg EKGas flags.rcf_kws kvs)
Proof
  strip_tac >> simp[type_check_def,lift_option_type_def,ignore_bind_def,
                    assert_def,FUN_EQ_THM,bind_def,return_def]
QED

Triviality calldata_restricted_amount:
  raw_call_kws_ok flags kws /\ raw_call_value flags.rcf_kws kvs = SOME amount ==>
  (flags.rcf_is_delegate \/ flags.rcf_is_static ==> amount = 0)
Proof
  strip_tac >> strip_tac >> fs[raw_call_kws_ok_def,raw_call_value_def] >>
  `ext_call_kwarg EKValue flags.rcf_kws kvs = NONE` by
    (irule ext_call_kwarg_not_mem >> simp[]) >> fs[]
QED

Triviality calldata_copy_entry:
  stmt_state_rel H ctx func cenv cx ee tout /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee Gout tnout tout /\
  expr_sim_inv_mods mods cenv cx env ee ==>
  tout.vs_call_ctx.cc_calldata = cx.txn.calldata /\
  LENGTH tout.vs_call_ctx.cc_calldata < dimword (:256) /\
  allocas_from lo tout /\ lo <= tout.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp tout /\
     w2n tout.vs_initial_fmp <= w2n tout.vs_fmp)
Proof
  strip_tac >> drule_then assume_tac stmt_state_rel_state_rel >>
  drule_then assume_tac state_rel_call_ctx_rel >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `context_well_typed cx` by fs[expr_sim_inv_mods_def] >>
  fs[call_ctx_rel_def,context_well_typed_def,dimword_def,ghost_inv_at_mods_def] >>
  strip_tac >> `allocas_below_fmp tout` by simp[] >> fs[allocas_below_fmp_def]
QED

Triviality calldata_emit_mono:
  emit_op opc ops s = (p,t) ==> s.cs_next_var <= t.cs_next_var
Proof
  strip_tac >> qspecl_then [`opc`,`ops`,`s`] mp_tac ci_mono_emit_op >>
  simp[ci_mono_def]
QED

Triviality calldata_safe_outbuf:
  compile_raw_call_outbuf M s3 = ((ov,op),s4) ==>
  safe_operand s4 ov /\ safe_operand s4 op
Proof
  Cases_on `M = 0` >>
  simp[compile_raw_call_outbuf_def,compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
  >- (strip_tac >> gvs[] >> drule compile_alloc_buffer_parts >>
      simp[safe_operand_def]) >>
  strip_tac >> gvs[] >>
  drule_then assume_tac emit_op_safe_operand >> simp[] >>
  drule_then assume_tac calldata_emit_mono >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  irule safe_operand_mono >> goal_assum drule >> fs[safe_operand_def]
QED

Triviality calldata_safe_gas_cut:
  (case go of NONE => emit_op GAS [] s2 | SOME p => (p,s2)) = (gas,s3) /\
  (!p. go = SOME p ==> safe_operand s2 p) ==>
  s2.cs_next_var <= s3.cs_next_var /\ safe_operand s3 gas
Proof
  Cases_on `go` >> simp[] >> strip_tac >> gvs[] >>
  drule_then assume_tac calldata_emit_mono >> drule_then assume_tac emit_op_safe_operand >> simp[]
QED

(* The applicable common run is an antecedent.  Extra common-run facts, e.g.
   reading equations and allocation separation, pass through P unmodified. *)
val calldata_out_endpoint = ``\tout Gout tnout ob gw.
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (tk,GK,tnK)
      (if IS_NONE go then [F] else []) (OK tout,Gout,tnout) /\
    stmt_state_rel H ctx func cenv cx ee tout /\ immutable_frame_mods func cenv cx ee tout /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gout tnout tout) /\
  (!p. safe_operand s2 p ==> eval_operand p tout = eval_operand p tk /\
    op_prov Gout p = op_prov GK p /\ op_taint tnout p = op_taint tnK p) /\
  (case go of NONE => T | SOME p => eval_operand p tk = SOME gw) /\
  eval_operand gas tout = SOME gw /\ op_taint tnout gas = {} /\
  eval_operand ov tout = SOME (n2w ob) /\
  eval_operand op tout = SOME (n2w (if M = 0 then ob else ob + 32)) /\
  (M = 0 ==> ov = op) /\ ob + payload < dimword (:256) /\
  FLOOKUP tout.vs_allocas s3.cs_next_id = SOME (ob,payload) /\
  op_prov Gout ov = SOME (ob,payload) /\ op_prov Gout op = SOME (ob,payload) /\
  op_taint tnout ov = {} /\ op_taint tnout op = {} /\
  ~tout.vs_halted /\ tout.vs_current_bb = s4.cs_current_bb /\
  tout.vs_inst_idx = LENGTH s4.cs_current_insts /\
  alloca_history func tout /\ tk.vs_alloca_next <= tout.vs_alloca_next /\
  (IS_NONE go ==> gas_prefix 1 tk.vs_gas_readings = [gw]) /\
  tout.vs_gas_readings = DROP (if IS_NONE go then 1 else 0) tk.vs_gas_readings /\
  wb_frame cenv es ee sa s0 tout /\ return_buf_frame d cenv sa tout /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gout tnout /\ P tout Gout tnout ob gw``;

val calldata_word_horizon = ``!H. valid_horizon cx st0 H ee.storage_trace ==>
  typed_args_post H ctx func cenv cx es sa s0 ee (a::kws) (addr::xs) vs tk /\
  immutable_frame_mods func cenv cx ee tk /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee GK tnK tk /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 GK tnK``;

val calldata_selected_clean = ``!p. go = SOME p ==> safe_operand s2 p /\
  (?w. eval_operand p tk = SOME w) /\ op_taint tnK p = {} /\ op_prov GK p = NONE``;

val calldata_source_gas_ready = ``case ext_call_kwarg EKGas flags.rcf_kws (DROP 1 vs) of
  NONE => go = NONE
  | SOME gv => ?op w. go = SOME op /\ eval_operand op tk = SOME w /\
    dest_NumV gv = SOME (w2n w) /\ op_taint tnK op = {}``;

Theorem raw_calldata_outbuf_from_words_mods:
  expr_type a = BaseT AddressT /\ LENGTH kws = LENGTH flags.rcf_kws /\
  raw_call_kws_ok flags kws /\ type_alloc_ok cenv (raw_call_return_type flags) /\
  M = flags.rcf_max_outsize /\ payload = (if M = 0 then 0 else 32 * ((M+31) DIV 32) + 32) /\
  go = ext_call_kwarg EKGas flags.rcf_kws xs /\ vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
  (case go of NONE => emit_op GAS [] s2 | SOME p => (p,s2)) = (gas,s3) /\
  (case go of NONE => emit_op GAS [] h2 | SOME p => (p,h2)) = (gas,h3) /\
  compile_raw_call_outbuf M s3 = ((ov,op),s4) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ^calldata_word_horizon /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) (a::kws) vs /\
  EVERY (\p. op_prov GK p = NONE /\ op_taint tnK p = {}) (addr::xs) /\
  EVERY (safe_operand s2) (addr::xs) /\ expr_sim_inv_mods mods cenv cx env ee /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. contextRawReachable$frag_reachable ctx func tk fn inst u ==> dalloca_fmp_headroom inst u) /\
  ((case go of NONE => emit_op GAS [] s2 | SOME p => (p,s2)) = (gas,s3) /\
   (case go of NONE => emit_op GAS [] h2 | SOME p => (p,h2)) = (gas,h3) /\
   compile_raw_call_outbuf M s3 = ((ov,op),s4) /\
   ^calldata_word_horizon /\ payload < dimword (:256) /\ ^calldata_selected_clean /\
   ^calldata_source_gas_ready ==>
     ?tout Gout tnout ob gw. (^calldata_out_endpoint) tout Gout tnout ob gw) ==>
  ?av kvs target amount tout Gout tnout ob gw.
    vs = av::kvs /\ dest_AddressV av = SOME target /\
    (^checked_calldata_tail) cx flags vs = eval_raw_call cx flags target cx.txn.calldata amount
        (ext_call_kwarg EKGas flags.rcf_kws kvs) /\
    amount < dimword (:256) /\ ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0) /\
    eval_operand addr tout = SOME (w2w target) /\
    eval_operand (case vo of NONE => Lit 0w | SOME p => p) tout = SOME (n2w amount) /\
    op_taint tnout addr = {} /\ op_taint tnout (case vo of NONE => Lit 0w | SOME p => p) = {} /\
    EVERY (safe_operand s4) [addr; (case vo of NONE => Lit 0w | SOME p => p); gas; ov; op] /\
    (case ext_call_kwarg EKGas flags.rcf_kws kvs of NONE => go = NONE
     | SOME gv => dest_NumV gv = SOME (w2n gw)) /\
    (^calldata_out_endpoint) tout Gout tnout ob gw /\
    tout.vs_call_ctx.cc_calldata = cx.txn.calldata /\
    LENGTH tout.vs_call_ctx.cc_calldata < dimword (:256) /\
    allocas_from lo tout /\ lo <= tout.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp tout /\ w2n tout.vs_initial_fmp <= w2n tout.vs_fmp) /\
    (!fn inst u. contextRawReachable$frag_reachable ctx func tout fn inst u ==> dalloca_fmp_headroom inst u)
Proof
  BETA_TAC >> strip_tac >>
  drule raw_call_kwargs_types >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all calldata_decode_word_list >> strip_tac >>
  `EVERY (\p. op_prov GK p = NONE /\ op_taint tnK p = {}) xs /\
   safe_operand s2 addr /\ EVERY (safe_operand s2) xs /\ op_taint tnK addr = {}` by fs[] >>
  drule_all raw_call_value_operand >> disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  `payload < dimword (:256)` by (drule calldata_payload_bound >> simp[]) >>
  `^calldata_selected_clean` by
    (rpt strip_tac >> `MEM p xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM] >> drule_all_then strip_assume_tac LIST_REL_MEM_IMP >> gvs[]) >>
  `^calldata_source_gas_ready` by
    (drule_all calldata_gas_selection >> fs[]) >>
  qpat_x_assum `_ ==> ?tout Gout tnout ob gw. _` mp_tac >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `tout` (qx_choose_then `Gout` (qx_choose_then `tnout`
    (qx_choose_then `ob` (qx_choose_then `gw` assume_tac))))) >>
  pop_assum (fn th => assume_tac th >> strip_assume_tac th) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac calldata_copy_entry >>
  `!fn inst u. contextRawReachable$frag_reachable ctx func tout fn inst u ==>
     dalloca_fmp_headroom inst u` by
    (rpt strip_tac >> drule gas_origin_ptr_path_dalloca_fmp_headroom >>
     disch_then (qspecl_then [`fn`,`inst`,`u`] mp_tac) >> simp[] >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `safe_operand s2 (case vo of NONE => Lit 0w | SOME p => p) /\
   op_taint tnK (case vo of NONE => Lit 0w | SOME p => p) = {}` by
    (Cases_on `vo` >- simp[safe_operand_def,op_taint_def] >>
     rename1 `SOME p = ext_call_kwarg EKValue _ xs` >>
     `MEM p xs` by metis_tac[raw_call_kwarg_mem] >> fs[EVERY_MEM]) >>
  `case ext_call_kwarg EKGas flags.rcf_kws kvs of NONE => go = NONE
   | SOME gv => dest_NumV gv = SOME (w2n gw)` by
    (drule_all calldata_gas_selection >>
     Cases_on `ext_call_kwarg EKGas flags.rcf_kws kvs` >> simp[] >>
     strip_tac >> gvs[]) >>
  `flags.rcf_is_delegate \/ flags.rcf_is_static ==> amount = 0` by
    (disch_tac >> irule calldata_restricted_amount >> metis_tac[]) >>
  `!p. go = SOME p ==> safe_operand s2 p` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all_then strip_assume_tac calldata_safe_gas_cut >>
  drule_then strip_assume_tac calldata_safe_outbuf >>
  `s3.cs_next_var <= s4.cs_next_var` by
    (qspecl_then [`M`,`s3`] mp_tac ci_mono_compile_raw_call_outbuf >> simp[ci_mono_def]) >>
  `s2.cs_next_var <= s4.cs_next_var` by decide_tac >>
  `EVERY (safe_operand s4) [addr; (case vo of NONE => Lit 0w | SOME p => p); gas; ov; op]` by
    (simp_tac std_ss [EVERY_DEF] >> conj_tac
     >- (irule safe_operand_mono >> qexists_tac `s2` >> simp[]) >>
     conj_tac
     >- (irule safe_operand_mono >> qexists_tac `s2` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     conj_tac >- (irule safe_operand_mono >> qexists_tac `s3` >> simp[]) >>
     simp[]) >>
  qexistsl_tac [`av`,`kvs`,`target`,`amount`,`tout`,`Gout`,`tnout`,`ob`,`gw`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (once_asm_rewrite_tac [] >> irule (BETA_RULE calldata_tail_checks) >> simp[]) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
