Theory bodyFullAbiDecodeExprConditional
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  bodyFullAbiDecodeCallerFull bodyFullAbiDecodeCallerSetupOrigin
  bodyFullAbiDecodeCallerCutEndpoint bodyFullAbiDecodeCallerEntryOrigin
  bodySimFull exprSimAbiDecodeEntryTyping
  gasOutcomeFullCompose exprSimHyps exprSimSource exprLowering compileEnv
  exprSimAbiDecodeBodySuccess exprSimAbiDecodeOblivious exprSimAbiDecodeCompose
  exprSimUnwrap exprLoweringProps exprOpenFirstOperand gasShadow gasShadowCompileStmtHelpers
  gasShadowState fragExec stmtSimProps haltExitProj vyperStorageTrace
  vyperContext vyperInterpreter vyperState vyperAST
  vyperStorageFootprint exprSimHypsDefs vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperTyping bodyInvCodeProps exprBodyPreProps exprSimFullBundleProps

(* Retain the two closed producer propositions at the checked caller boundary. *)
local
  val normalized = CONV_RULE (REPEATC (REWR_CONV boolTheory.LET_THM THENC BETA_CONV))
    bodyFullAbiDecodeCallerFullTheory.abi_decode_caller_full_conditional
  val (premises, _) = boolSyntax.dest_imp (concl normalized)
  val (setup, rest) = boolSyntax.dest_conj premises
  val (guarded, rest) = boolSyntax.dest_conj rest
  val (selector, rest) = boolSyntax.dest_conj rest
  val (endpoint, entry) = boolSyntax.dest_conj rest
  val _ = if null (free_vars guarded) andalso null (free_vars selector) then ()
          else raise Fail "ABI decoder producer hypotheses must be closed"
in
  val decode_guarded_producer = guarded
  val decode_cut_selector = selector
  val decode_setup_producer = setup
  val decode_endpoint_producer = endpoint
  val decode_caller_requirements = entry
end

Theorem abi_decode_singleton_compile:
  compile_expr ce ty0 (TypeBuiltin ty (AbiDecode unwrap) ty [e]) sa = (vv,final) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ fn_has_code sa final fn ==>
  ?data start out.
    lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce (if unwrap /\
      needs_external_call_wrap ty then TupleT [ty] else ty))
      (abi_static_size ce.ce_struct_fields (if unwrap /\ needs_external_call_wrap ty then TupleT [ty]
        else ty)) (abi_size_bound ce.ce_struct_fields (if unwrap /\ needs_external_call_wrap ty then
        TupleT [ty] else ty))
      (type_memory_bytes ce (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start =
        (out,final) /\
    vv = LocatedValue ty (mk_ptr out LocMemory) /\
    fn_has_code sa start fn /\ fn_has_code start final fn
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_type_builtin_dispatch,
       Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline exprLoweringTheory.as_ptr_val_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `unwrap_value ce evv sm = (data,start)` >>
  drule (cj 1 compile_expr_extends) >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `cs_extends sa start` by metis_tac[cs_extends_trans] >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  simp[lower_value_def, comp_bind_def] >> metis_tac[]
QED

Theorem abi_decode_setup_producer_checked[local]:
  ^decode_setup_producer
Proof
  rpt gen_tac >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (BETA_RULE abi_decode_caller_setup_origin_observed)) >>
  simp[CONJ_ASSOC] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_decode_endpoint_producer_checked[local]:
  ^decode_endpoint_producer
Proof
  rpt gen_tac >>
  mp_tac (SPEC_ALL abi_decode_caller_endpoint_committed) >>
  simp[boolTheory.LET_THM, CONJ_ASSOC] >> disch_then ACCEPT_TAC
QED

(* The caller's physical entry premises, built from the one normal child
   endpoint and its horizon-uniform post. Shared by the two consumers. *)
Theorem abi_decode_caller_entry_from_child:
  body_inv (cx_tops cx) ctx ce cx /\ MEM func ctx.ctx_functions /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  (let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
      (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) start = (out,final)) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  storage_trace_domain cx st0 es1.storage_trace /\
  ~s.vs_halted /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
      expr_sim_full_post (DF,lo,delta,ctx,func) ce cx e (es,sa,start,s0,data,G0,tn0)
        H (INL (BytesV bs)) es1 G tn s /\ stmt_state_rel H ctx func ce cx es s0) ==>
  ^decode_caller_requirements
Proof
  strip_tac >>
  qpat_x_assum `let wty = _ in _` (assume_tac o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx func ce cx e es sa start s0 es1 (BytesV bs) data s /\
    ghost_inv_at (DF H) lo delta ce cx es1 G tn s /\
    ptr_val_ok cx (post_value_type ce e) (BytesV bs) data G tn s /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[expr_sim_full_post_def]) >>
  `s.vs_current_bb = start.cs_current_bb /\ s.vs_inst_idx = LENGTH start.cs_current_insts /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next` by
    (`valid_horizon cx st0 (storage_trace_horizon es1.storage_trace) es1.storage_trace` by
        fs[storage_trace_domain_def] >>
     qpat_assum `!H. _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
         [expr_sim_full_post_def,expr_sim_full_endpoint_def])) >> simp[]) >>
  conj_tac >- simp[] >>
  qabbrev_tac `wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty` >>
  drule_then strip_assume_tac abiBuiltinDecodeCorrectTheory.lower_abi_decode_setup_trace >>
  mp_tac (BETA_RULE (Q.INST
    [`tops` |-> `cx_tops cx`, `es0` |-> `es`, `es` |-> `es1`,
     `origin` |-> `sa`, `st` |-> `start`, `fn` |-> `func`, `input_bytes` |-> `bs`,
     `V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`,
     `min_size` |-> `abi_static_size ce.ce_struct_fields wty`,
     `max_size` |-> `abi_size_bound ce.ce_struct_fields wty`,
     `outsz` |-> `type_memory_bytes ce wty`]
    (SPEC_ALL abi_decode_body_setup_entry_origin))) >>
  impl_tac >-
    (simp[Abbr `wty`] >>
     conj_tac >- (qexists `storage_trace_horizon es1.storage_trace` >> fs[storage_trace_domain_def]) >>
     rpt strip_tac >> res_tac >> fs[]) >>
  BETA_TAC >>
  disch_then (qx_choose_then `b` $ qx_choose_then `data_var` $
    qx_choose_then `d` $ mk_asm "entry_origin") >>
  qexistsl [`b`,`data_var`,`d`,`ops`,`ready`] >> BETA_TAC >>
  conj_tac >- asm "entry_origin" ACCEPT_TAC >>
  reverse conj_tac >- simp[] >>
  qabbrev_tac `wtv = if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv` >>
  `abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields wty wtv /\
   type_memory_bytes ce wty = type_memory_size wtv` by
    (drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_coherent >> strip_tac >>
     drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >> strip_tac >>
     `evaluate_type (get_tenv cx) wty = SOME wtv` by
       simp[Abbr `wty`, Abbr `wtv`, abi_decode_wrapped_type] >>
     fs[abiDecoderCoherenceTheory.abi_decoder_header_def, Abbr `wty`]) >>
  `fn_has_code ready final func` by
    (`cs_extends start ready` by
       (drule abiBuiltinDecodeSetupTheory.abi_builtin_decode_setup_shape >>
        strip_tac >> irule abiEncoderChildContextTheory.abi_encoder_straight_extends >> simp[]) >>
     `cs_extends ready final` by
       (drule abiDecoderAppendTheory.cs_extends_abi_decode >> simp[]) >>
     drule_all_then strip_assume_tac fn_has_code_split) >>
  BETA_TAC >> rpt gen_tac >> disch_tac >>
  pop_assum (CONJUNCTS_THEN2 (mk_asm "setup_success") (mk_asm "ready_origin")) >>
  asm_x "entry_origin" (CONJUNCTS_THEN2 (mk_asm "setup_pre") kall_tac) >>
  asm "setup_pre" (fn pre =>
    qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` (fn code =>
      mp_tac (PART_MATCH (funpow 6 rand o lhand o lhand)
        (PART_MATCH (lhand o lhand o lhand) (BETA_RULE (Q.INST
          [`V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`,
           `G'` |-> `Gs`, `tn'` |-> `ts`, `env` |-> `get_tenv cx`,
           `ty` |-> `wty`, `tv` |-> `wtv`]
          (SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
             abi_decode_caller_guarded_entry_origin)))) (concl pre)) (concl code)))) >>
  (impl_tac >-
    (conj_tac >-
      (conj_tac >- asm "setup_pre" ACCEPT_TAC >>
       conj_tac >- asm "setup_success" ACCEPT_TAC >> simp[]) >>
     asm "ready_origin" ACCEPT_TAC)) >>
  let val rules = [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  in
    disch_then (assume_tac o SIMP_RULE (srw_ss()) rules) >>
    SIMP_TAC (srw_ss()) rules >> pop_assum ACCEPT_TAC
  end
QED

Theorem abi_decode_singleton_vv_full[local]:
  ^decode_guarded_producer /\ ^decode_cut_selector /\
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  body_exprs_full_ok cx [e] ==>
  expr_vv_sim_full (DF,lo,delta,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty0 (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "guarded")
    (CONJUNCTS_THEN2 (mk_asm "selector") (map_every assume_tac o CONJUNCTS))) >>
  drule expr_body_pre_type_builtin_head >> strip_tac >>
  `expr_sim_full (DF,lo,delta,ctx,shadow_ctx,PG,func,shadow_func)
       ce cx (expr_type e) e es` by
    (qpat_assum `body_exprs_full_ok _ [_]`
       (mp_tac o SIMP_RULE (srw_ss()) [body_exprs_full_ok_def]) >>
     disch_then (drule_all o cj 1 o CONJUNCT1 o
       ONCE_REWRITE_RULE [body_expr_full_ok_def]) >> simp[]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all abi_decode_singleton_compile >> simp[] >> strip_tac >> gvs[] >>
  `?shadow_start. lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
     (gas_shadow_expr e) shadow_sa = (data,shadow_start) /\
     gas_shadow_state start shadow_start` by
    (qpat_assum `gas_shadow_state sa shadow_sa`
       (mp_then Any mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
     disch_then (qspecl_then [`expr_type e`,`e`,`ce`] mp_tac) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `fn_has_code shadow_sa shadow_start shadow_func` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     `expr_type (gas_shadow_expr e) = BaseT (BytesT (Dynamic n))` by simp[] >>
     drule_all abi_decode_singleton_compile >> simp[] >> strip_tac >> gvs[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (qpat_assum `expr_body_pre _ _ _ e es`
       (ACCEPT_TAC o MATCH_MP expr_body_pre_gas_admissible)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`start`,`shadow_sa`,`shadow_start`,
    `data`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- gvs[] >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ srcQ srcR` >>
  rewrite_tac[abi_decode_singleton_source] >>
  irule gas_outcome_full_bind_all >>
  `!res : value + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=>
       expr_exit res r` by (Cases >> simp[expr_exit_INR_type]) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_lifts,
       storage_trace_frame_return] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> ho_match_mp_tac gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl [`v`,`mid`,`t`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  qexists `\H res ee G tn t. srcQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "continuation" >>
  irule gas_outcome_full_post_source >>
  qexistsl [`srcQ`,`srcR`] >>
  asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> simp[]) >>
  simp[Abbr `srcR`] >>
  qpat_x_assum `!res r. (?exc. _ /\ _) <=> expr_exit res r`
    (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!res r. _` (qspecl_then [`res`,`r`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  metis_tac[halt_exit_INR_type]
QED

Resume abi_decode_singleton_vv_full[continuation]:
  map_every qx_gen_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`s`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> srcQ H _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `srcQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `srcQ`, NoAsms] >>
  disch_then (qx_choose_then `v` strip_assume_tac) >> gvs[] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> gvs[] >>
  `expr_result_typed env e (Value v)` by
    (irule (cj 3 expr_body_pre_eval) >>
     qexistsl [`ce`,`cx`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `mid`] >>
     fs[bind_def]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n)))` by
    (qpat_assum `expr_body_pre _ _ _ e _` (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `?bs. v = BytesV bs` by
    (`env.type_defs = get_tenv cx` by
       (qpat_assum `expr_body_pre _ _ _ e _`
          (ACCEPT_TAC o MATCH_MP expr_body_pre_env_type_defs)) >>
     qpat_assum `evaluate_type _ (expr_type e) = SOME _` (fn ty_th =>
       qpat_assum `env.type_defs = get_tenv cx` (fn env_th =>
         qpat_x_assum `expr_result_typed _ _ _` (fn res_th =>
           POP_ASSUM_LIST (K (map_every assume_tac [ty_th,env_th] >> mp_tac res_th))))) >>
     Cases_on `v` >> simp[expr_result_typed_def, expr_runtime_typed_def,
       value_result_typed_def, value_has_type_def]) >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule abi_decode_observed_scopes_dom >> simp[]) >>
  `?tyv. evaluate_type (get_tenv cx) ty = SOME tyv` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  mp_tac (BETA_RULE (Q.INST
    [`ann` |-> `ty`, `final` |-> `sb`, `es1` |-> `mid`,
     `G` |-> `G1`, `tn` |-> `tn1`, `tv` |-> `tyv`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (CONV_RULE (REPEATC (REWR_CONV boolTheory.LET_THM THENC BETA_CONV))
       abi_decode_caller_full_conditional))) >>
  impl_tac >-
    (conj_tac >- ACCEPT_TAC (BETA_RULE abi_decode_setup_producer_checked) >>
     conj_tac >- asm "guarded" (ACCEPT_TAC o BETA_RULE) >>
     conj_tac >- asm "selector" (ACCEPT_TAC o BETA_RULE) >>
     conj_tac >- ACCEPT_TAC (BETA_RULE abi_decode_endpoint_producer_checked) >>
     `cx_tops cx = tops` by drule_then (ACCEPT_TAC o cj 2) body_inv_main_code >>
     irule (BETA_RULE (Q.INST [`env` |-> `env`, `n` |-> `n`]
       abi_decode_caller_entry_from_child)) >>
     simp[expr_sim_full_post_def,expr_sim_full_endpoint_def] >> rpt strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (drule_at_then (Pos (el 2)) mp_tac valid_horizon_frame >>
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result]) >>
     res_tac >> fs[]) >>
  qpat_assum `expr_type e = BaseT _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  disch_tac >> irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >>
  simp[expr_type_def] >>
  rpt strip_tac >> gvs[]
QED

Finalise abi_decode_singleton_vv_full

Theorem abi_decode_expr_full_from_producers:
  (^decode_guarded_producer /\ ^decode_cut_selector) ==>
  (!cx v11 b typ es.
     (!s'' x t.
        type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
          "TypeBuiltin args" s'' = (INL x,t) ==>
        body_exprs_full_ok cx es) ==>
     body_expr_full_ok cx (TypeBuiltin v11 (AbiDecode b) typ es))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "guarded") (mk_asm "selector")) >>
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `expr_body_pre _ _ _ _ _`
    (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
  drule abi_decode_parent_type >> strip_tac >> gvs[] >>
  `body_exprs_full_ok cx [e]` by
    (first_x_assum irule >>
     simp[vyperStateTheory.type_check_def,
          vyperContextTheory.type_builtin_args_length_ok_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def]) >>
  reverse conj_asm2_tac
  >- (irule abi_decode_singleton_vv_full >>
      conj_tac >- asm "guarded" ACCEPT_TAC >>
      conj_tac >- asm "selector" ACCEPT_TAC >>
      qpat_assum `shadow_body_inv tops ctx shadow_ctx` (irule_at Any) >>
      qpat_assum `body_const_cells_agree [(NONE,tops)] cx env es'` (irule_at Any) >>
      simp[] >> goal_assum (drule_at Any)) >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  asm_x "guarded" kall_tac >> asm_x "selector" kall_tac >>
  `expr_body_pre cenv cx env (TypeBuiltin typ (AbiDecode b) typ [e])
     (es' with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
