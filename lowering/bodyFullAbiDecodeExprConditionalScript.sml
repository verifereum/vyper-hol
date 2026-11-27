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
  vyperTypeInvariants vyperTyping bodyInvCodeProps exprBodyPreProps
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] bodyFullPostsMods
  exprSimSliceCompose gasOutcomeFullBindMods gasOutcomeFullMods gasExemptCertMods
  exprSimAbiDecodeBodyEntry exprBodyPreTypingProps vyperTypeEvalSoundness
  exprSimAbiDecodeEntryLayout exprSimAbiDecodeEntryMetadata allocLimits vyperTypeSystem
  bodyPtrDefs loweringPosts loweringStateRelDefs

(* Retain the two closed producer propositions at the checked caller boundary. *)
local
  val normalized = CONV_RULE (REPEATC (REWR_CONV boolTheory.LET_THM THENC BETA_CONV))
    bodyFullAbiDecodeCallerFullTheory.abi_decode_caller_full_conditional
  val (premises, _) = boolSyntax.dest_imp (concl normalized)
  val (setup, rest) = boolSyntax.dest_conj premises
  val (guarded, rest) = boolSyntax.dest_conj rest
  val (_, rest) = boolSyntax.dest_conj rest
  val (endpoint, _) = boolSyntax.dest_conj rest
  val _ = if null (free_vars guarded) then ()
          else raise Fail "ABI decoder guarded producer hypothesis must be closed"
in
  val decode_guarded_producer = guarded
  val decode_cut_selector =
    concl bodyFullAbiDecodeCallerFullTheory.abi_decode_caller_cut_choice
  val decode_setup_producer = setup
  val decode_endpoint_producer = endpoint
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

Theorem abi_decode_immutable_frame[local,simp]:
  stmt_state_rel H ctx fn ce cx es s ==>
  immutable_frame_mods fn ce cx es s
Proof
  simp_tac bool_ss [stmt_state_rel_def, state_rel_def, immutable_frame_mods_def,
    bodyInvSplitTheory.immutables_rel_mods_def, bodyInvSplitTheory.immutable_alloca_sep_mods_def,
    optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem abi_decode_expr_post_mods[local,simp]:
  expr_post_mods H ctx fn ce cx e es sa sb s0 ee v op t <=>
  expr_post H ctx fn ce cx e es sa sb s0 ee v op t
Proof
  simp[expr_post_mods_def] >>
  metis_tac[loweringPostsTheory.expr_post_def, abi_decode_immutable_frame]
QED

Theorem abi_decode_stmt_frame[local,simp]:
  (stmt_state_rel H ctx fn ce cx es s /\ immutable_frame_mods fn ce cx es s /\ rest) <=>
  (stmt_state_rel H ctx fn ce cx es s /\ rest)
Proof
  metis_tac[abi_decode_immutable_frame]
QED

Theorem abi_decode_vv_post_mods[local,simp]:
  vv_post_mods H ctx fn ce cx e es sa sb s0 ee v (LocatedValue ann (mk_ptr out LocMemory)) t <=>
  vv_post H ctx fn ce cx e es sa sb s0 ee v (LocatedValue ann (mk_ptr out LocMemory)) t
Proof
  Cases_on `v` >> TRY (Cases_on `p`) >>
  simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
    vv_place_ptr_mods_def, vv_place_ptr_def, contextTheory.mk_ptr_def] >>
  metis_tac[abi_decode_immutable_frame]
QED

Theorem abi_decode_ghost_mods[local,simp]:
  (dead_lo_ok_mods H D lo ce cx <=> dead_lo_ok H D lo ce cx) /\
  (ghost_inv_at_mods D lo delta ce cx es G tn s <=> ghost_inv_at D lo delta ce cx es G tn s)
Proof
  simp[dead_lo_ok_mods_def, dead_lo_ok_def, ghost_inv_at_mods_def, ghost_inv_at_def]
QED

Theorem abi_decode_expr_sim_mods[local]:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,fn,shadow_fn) ce cx ty e es <=>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,fn,shadow_fn) ce cx ty e es
Proof
  simp[expr_sim_full_mods_def, expr_sim_full_def, SF CONJ_ss]
QED

Theorem abi_decode_operand_sim[local]:
  body_exprs_full_ok_mods mods exps cx [e] /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods ce cx env e es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,fn,shadow_fn) ce cx (expr_type e) e es
Proof
  rewrite_tac[GSYM abi_decode_expr_sim_mods] >>
  simp_tac bool_ss [Once bodyFullPredsModsTheory.body_expr_full_ok_mods_def] >>
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [bodyFullPredsModsTheory.body_expr_full_ok_mods_def]) >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem abi_decode_typed_bytes[local]:
  value_runtime_typed env ty v /\
  evaluate_type env.type_defs ty = SOME (BaseTV (BytesT (Dynamic n))) ==>
  ?bs. v = BytesV bs
Proof
  Cases_on `v` >> simp[value_runtime_typed_def, value_has_type_def]
QED

Theorem abi_decode_singleton_vv_full[local]:
  ^decode_guarded_producer /\ ^decode_cut_selector /\
  (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  body_exprs_full_ok_mods mods exps cx [e] ==>
  expr_vv_sim_full (DF,lo,delta,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty0 (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "guarded")
    (CONJUNCTS_THEN2 (mk_asm "selector") (map_every assume_tac o CONJUNCTS))) >>
  drule_then assume_tac abi_decode_operand_pre_mods >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `expr_sim_full (DF,lo,delta,ctx,shadow_ctx,PG,func,shadow_func)
       ce cx (expr_type e) e es` by
    (irule abi_decode_operand_sim >>
     goal_assum (drule_at Any) >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `body_exprs_full_ok_mods _ _ _ [_]` (irule_at Any) >>
     qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >> simp[]) >>
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
    (qpat_assum `gas_admissible (eval_expr _ (TypeBuiltin _ _ _ _)) _ _`
       (mp_tac o REWRITE_RULE [abi_decode_singleton_source]) >>
     disch_then (ACCEPT_TAC o MATCH_MP slice_gas_admissible_expr_head)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`start`,`shadow_sa`,`shadow_start`,
    `data`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- gvs[] >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ srcQ srcR` >>
  rewrite_tac[abi_decode_singleton_source] >>
  irule gas_outcome_full_mods_bind_all >>
  `!res : value + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=>
       expr_exit res r` by (Cases >> simp[expr_exit_INR_type]) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_lifts,
       storage_trace_frame_return] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> ho_match_mp_tac gas_exempt_cert_mods_bind_value >>
      qexistsl [`v`,`mid`,`t`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[]) >>
  qexists `\H res ee G tn t. srcQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "continuation" >>
  irule gas_outcome_full_mods_post_source >>
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
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n)))` by
    (drule_all abi_decode_body_operand_evaluates >> simp[]) >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_THM] eval_expr_read_type_sound) >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_body_pre_mods_def, expr_sim_inv_mods_def]) >>
  `?bs. v = BytesV bs` by
    (`env.type_defs = get_tenv cx` by
       (qpat_assum `expr_body_pre_mods _ ce cx env e es`
          (ACCEPT_TAC o MATCH_MP abi_decode_inv_type_env o MATCH_MP expr_body_pre_mods_inv)) >>
     irule (Q.INST [`ty` |-> `expr_type e`] abi_decode_typed_bytes) >>
     qexistsl_tac [`e`, `env`, `n`] >> simp[] >>
     qpat_assum `expr_type e = BaseT (BytesT (Dynamic n))` (fn eq =>
       qpat_assum `evaluate_type (get_tenv cx) (expr_type e) = SOME _`
         (ACCEPT_TAC o ONCE_REWRITE_RULE [eq]))) >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule abi_decode_observed_scopes_dom >> simp[]) >>
  `?tyv. evaluate_type (get_tenv cx) ty = SOME tyv` by
    (drule abi_decode_body_target >> strip_tac >>
     drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
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
     conj_tac >-
       (simp[] >> qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
     asm_x "guarded" kall_tac >> asm_x "selector" kall_tac >>
     qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` kall_tac >>
     qabbrev_tac `wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty` >>
     drule_then strip_assume_tac abiBuiltinDecodeCorrectTheory.lower_abi_decode_setup_trace >>
     mp_tac (BETA_RULE (Q.INST
       [`ann` |-> `ty`, `mods` |-> `ce.ce_modules`, `es0` |-> `es`, `es` |-> `mid`,
        `origin` |-> `sa`, `st` |-> `start`, `final` |-> `sb`, `fn` |-> `func`,
        `G` |-> `G1`, `tn` |-> `tn1`, `input_bytes` |-> `bs`,
        `V` |-> `\H. valid_horizon cx st0 H mid.storage_trace`,
        `min_size` |-> `abi_static_size ce.ce_struct_fields wty`,
        `max_size` |-> `abi_size_bound ce.ce_struct_fields wty`,
        `outsz` |-> `type_memory_bytes ce wty`]
       (SPEC_ALL abi_decode_body_setup_entry_origin))) >>
     impl_tac >-
       (simp[Abbr `wty`] >>
        conj_tac >- (qexists `storage_trace_horizon mid.storage_trace` >> simp[]) >>
        rpt strip_tac >>
        `valid_horizon cx st0 H es.storage_trace` by
          (drule_at_then (Pos (el 2)) mp_tac valid_horizon_frame >>
           simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
                storage_trace_frame_read_result]) >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
          (drule_then strip_assume_tac)) >>
     BETA_TAC >>
     disch_then (qx_choose_then `b` $ qx_choose_then `data_var` $
       qx_choose_then `d` $ mk_asm "entry_origin") >>
     qexistsl [`b`,`data_var`,`d`,`ops`,`ready`] >>
     conj_asm1_tac >- asm "entry_origin" ACCEPT_TAC >>
     pop_assum (fn entry => asm_x "entry_origin" kall_tac >>
                            mk_asm "entry_origin" entry) >>
     reverse conj_tac >- simp[] >>
     qabbrev_tac `wtv = if unwrap /\ needs_external_call_wrap ty then TupleTV [tyv] else tyv` >>
     `abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields wty wtv /\
      type_memory_bytes ce wty = type_memory_size wtv` by
       (drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_coherent >> strip_tac >>
        drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >> strip_tac >>
        `evaluate_type (get_tenv cx) wty = SOME wtv` by
          simp[Abbr `wty`, Abbr `wtv`, abi_decode_wrapped_type] >>
        fs[abiDecoderCoherenceTheory.abi_decoder_header_def, Abbr `wty`]) >>
     `fn_has_code ready sb func` by
       (`cs_extends start ready` by
          (drule abiBuiltinDecodeSetupTheory.abi_builtin_decode_setup_shape >>
           strip_tac >> irule abiEncoderChildContextTheory.abi_encoder_straight_extends >> simp[]) >>
        `cs_extends ready sb` by
          (drule abiDecoderAppendTheory.cs_extends_abi_decode >> simp[]) >>
        drule_all_then strip_assume_tac fn_has_code_split) >>
     BETA_TAC >> rpt gen_tac >> disch_tac >>
     pop_assum (CONJUNCTS_THEN2 (mk_asm "setup_success") (mk_asm "ready_origin")) >>
     asm_x "entry_origin" (CONJUNCTS_THEN2 (mk_asm "setup_pre") kall_tac) >>
     asm "setup_pre" (fn pre =>
       qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` (fn code =>
         mp_tac (PART_MATCH (funpow 6 rand o lhand o lhand)
           (PART_MATCH (lhand o lhand o lhand) (BETA_RULE (Q.INST
             [`V` |-> `\H. valid_horizon cx st0 H mid.storage_trace`,
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
     end) >>
  qpat_assum `expr_type e = BaseT _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  disch_tac >> irule gas_outcome_full_mods_post_mono >>
  goal_assum (drule_at Any) >>
  simp[expr_type_def] >>
  rpt strip_tac >> gvs[]
QED

Finalise abi_decode_singleton_vv_full

Theorem abi_decode_vv_sim_full_mods[local]:
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,fn,shadow_fn)
    ce cx cty (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,fn,shadow_fn)
    ce cx cty (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es
Proof
  rewrite_tac[expr_vv_sim_full_mods_def, expr_vv_sim_full_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_decode_singleton_compile >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then
    [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,
     `LocatedValue ty (mk_ptr out LocMemory)`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem abi_decode_expr_full_from_producers:
  (^decode_guarded_producer /\ ^decode_cut_selector) ==>
  (!cx v11 b typ es.
     (!s'' x t.
        type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
          "TypeBuiltin args" s'' = (INL x,t) ==>
        body_exprs_full_ok_mods mods exps cx es) ==>
     body_expr_full_ok_mods mods exps cx (TypeBuiltin v11 (AbiDecode b) typ es))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "guarded") (mk_asm "selector")) >>
  rpt gen_tac >> strip_tac >>
  simp[Once bodyFullPredsModsTheory.body_expr_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule abi_decode_parent_type >> strip_tac >> gvs[] >>
  `cenv.ce_module = src` by fs[bodyInvSplitTheory.module_body_inv_def] >> gvs[] >>
  `body_exprs_full_ok_mods mods exps cx [e]` by
    (first_x_assum irule >>
     simp[vyperStateTheory.type_check_def,
          vyperContextTheory.type_builtin_args_length_ok_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (TypeBuiltin typ (AbiDecode b) typ [e]) es'` by
    (irule abi_decode_singleton_vv_full >>
     conj_tac >- asm "guarded" ACCEPT_TAC >>
     conj_tac >- asm "selector" ACCEPT_TAC >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> qexists_tac `exps` >> simp[]) >>
  conj_tac
  >- (rewrite_tac[abi_decode_expr_sim_mods] >>
      `env.type_defs = get_tenv cx` by
        (qpat_assum `expr_body_pre_mods _ cenv cx env _ es'`
           (ACCEPT_TAC o MATCH_MP abi_decode_inv_type_env o MATCH_MP expr_body_pre_mods_inv)) >>
      `?tvt. evaluate_type (get_tenv cx) typ = SOME tvt` by
        (drule assignable_type_well_formed >>
         simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
      irule (Q.INST [`rty` |-> `tvt`] expr_sim_full_of_vv) >>
      simp[post_value_type_def, expr_type_def] >>
      conj_tac
      >- (rpt strip_tac >>
          `abi_decode_root_metadata cenv (get_tenv cx)` by
            (qpat_assum `expr_body_pre_mods _ cenv cx env _ es'`
               (ACCEPT_TAC o MATCH_MP abi_decode_root_metadata_inv o MATCH_MP expr_body_pre_mods_inv)) >>
          `type_memory_bytes cenv typ = type_memory_size tvt` by
            (irule abi_decode_descended_memory_size >>
             qexistsl [`get_tenv cx`,`get_tenv cx`] >> simp[]) >>
          `type_alloc_ok cenv typ` by
            (qpat_assum `expr_body_pre_mods _ cenv cx env (TypeBuiltin _ _ _ _) es'`
               (mp_tac o cj 4 o PURE_REWRITE_RULE [expr_body_pre_mods_def]) >>
             disch_then (mp_tac o MATCH_MP alloc_limits_expr_type_alloc_ok) >>
             simp[expr_type_def]) >>
          gvs[type_alloc_ok_def]) >>
      rpt gen_tac >> strip_tac >>
      `bind (eval_expr cx (TypeBuiltin typ (AbiDecode b) typ [e])) (read_result cx)
        (es' with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
      `value_runtime_typed env typ v` by
        (drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_THM] eval_expr_read_type_sound) >>
         disch_then (qspec_then `env` mp_tac) >>
         gvs[expr_body_pre_mods_def, expr_sim_inv_mods_def, expr_type_def]) >>
      gvs[value_runtime_typed_def]) >>
  irule abi_decode_vv_sim_full_mods >> simp[] >> metis_tac[]
QED
