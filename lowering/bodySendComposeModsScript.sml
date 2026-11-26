(* Linked Send: align the real/shadow operand slices before the CALL/ASSERT. *)
Theory bodySendComposeMods
Ancestors
  bodyRawRequestInputsMods bodyRawRequestWordsMods bodyForcedStorageFrameMods
  bodySendTailOutcomeMods
  bodyFullPostsMods bodyFullPredsMods bodyFullWordArgs exprSimFullBundleProps
  bodyInvSplit loweringStateRelDefs bodyFullShadowBodyInv
  exprSimSend exprSimStack exprSimMemDefs exprSimPrecompiles exprBodyPreProps
  gasOutcomeFullMods gasOutcomeFullPostMods gasExemptCertMods gasStorage gasShadowCompile
  gasShadow gasShadowState exprLoweringProps fragExec wordArgsPtr
  vyperStorageTrace vyperStorageFootprint vyperTypeExtCallCore callStepPtr
  bodyPtrDefs loweringPosts list compileEnv vyperState vyperInterpreter
  vyperValue venomState vyperAST exprLowering exprSimDefs vyperTypeSystem context

Triviality send_word_cut_code:
  MAP expr_type args = [BaseT AddressT; BaseT (UintT 256)] ++
    (if hg then [BaseT (UintT 256)] else []) /\
  lower_value compile_expr cenv ty (Call NoneT (Send hg) args dflt) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call NoneT (Send hg) args dflt)) sha = (op,shb) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb) ==>
  ?ao vo go sm shm out s3.
    op = Lit 0w /\
    lower_word_args cenv expr_type args sa =
      ([ao;vo] ++ (if hg then [go] else []),sm) /\
    lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr args) sha =
      ([ao;vo] ++ (if hg then [go] else []),shm) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sm,sha,shm) /\
    (~hg ==> go = Lit 0w) /\
    emit_op CALL [go;ao;vo;Lit 0w;Lit 0w;Lit 0w;Lit 0w] sm = (out,s3) /\
    emit_void ASSERT [out] s3 = ((),sb) /\ fn_has_code sm sb func
Proof
  strip_tac >> drule lower_value_send >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac compile_expr_send >>
  `MAP expr_type (MAP gas_shadow_expr args) = MAP expr_type args` by
    simp[MAP_MAP_o, combinTheory.o_DEF, gas_shadow_expr_type, ETA_AX] >>
  qpat_assum `lower_value _ (gas_shadow_env T _) _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP lower_value_send o REWRITE_RULE [gas_shadow_expr_def]) >>
  qpat_assum `compile_expr (gas_shadow_env T _) _ _ _ = _`
    (mp_then Any mp_tac compile_expr_send) >> simp[] >> strip_tac >>
  `gas_shadow_compiles (lower_word_args cenv expr_type args)
      (lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr args))` by
    simp[gas_shadow_compiles_lower_word_args, gas_shadow_expr_type] >>
  fs[expr_sim_full_code_def] >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >>
  qpat_assum `lower_word_args cenv _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  qpat_assum `lower_word_args (gas_shadow_env T _) _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  `cs_extends sm sb` by
    (qpat_assum `emit_op CALL _ sm = _` (mp_then (Pos hd) mp_tac send_tail_shape) >> simp[]) >>
  `cs_extends sm' shb` by
    (qpat_assum `emit_op CALL _ sm' = _` (mp_then (Pos hd) mp_tac send_tail_shape) >> simp[]) >>
  qexistsl_tac [`gas_op`,`success`,`s3`] >> simp[] >>
  rpt conj_tac >> metis_tac[fn_has_code_mid,cs_extends_refl]
QED

Triviality send_action_bind:
  LENGTH args = (if hg then 3 else 2) ==>
  bind (eval_expr cx (Call NoneT (Send hg) args dflt)) (read_result cx) =
  bind (eval_exprs cx args) (\vs. bind (eval_send cx hg vs) (read_result cx))
Proof
  strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (Call NoneT (Send hg) args dflt)) (read_result cx) x` >>
  drule_all_then strip_assume_tac (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_send_cases) >>
  gvs[bind_def]
QED

Triviality send_word_values:
  MAP expr_type args = [BaseT AddressT; BaseT (UintT 256)] ++
    (if hg then [BaseT (UintT 256)] else []) /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      value_has_type tv v) args vs /\
  typed_args_post H ctx func cenv cx es sa s0 ee args
    ([ao;vo] ++ (if hg then [go] else [])) vs t /\
  (~hg ==> go = Lit 0w) ==>
  ?a v gs aw vw gw. vs = a::v::gs /\
    LENGTH gs = (if hg then 1 else 0) /\
    eval_operand ao t = SOME aw /\ dest_AddressV a = SOME (w2w aw) /\
    eval_operand vo t = SOME vw /\ dest_NumV v = SOME (w2n vw) /\
    eval_operand go t = SOME gw /\
    w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gs) dest_NumV of
                NONE => 0 | SOME g => g)
Proof
  Cases_on `hg` >> simp[LENGTH_EQ_NUM_compute] >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, typed_args_post_def, MAP_EQ_CONS, MAP_EQ_NIL,
      evaluate_type_def, eval_operand_def, ext_call_kwarg_def] >>
  simp[address_typed_dest, uint256_typed_dest]
QED

Triviality send_unforce_outcome:
  (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,f,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q R /\
  (!H v ee g n u. Q H (INL v) ee g n u ==> Q' H (INL (Value v)) ee g n u) /\
  (!H ex ee g n u. Q H (INR ex) ee g n u ==> Q' H (INR ex) ee g n u) /\
  (!H v ee gt r. R H (INL v) ee gt r ==> R' H (INL (Value v)) ee gt r) /\
  (!H ex ee gt r. R H (INR ex) ee gt r ==> R' H (INR ex) ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,f,PG) mods cx st0
    (eval_expr cx e) (es,s,G,tn) Q' R'
Proof
  strip_tac >> drule eval_expr_force_value >> strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_full_mods_def]) >>
  REWRITE_TAC[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> reverse conj_tac
      >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
          asm_rewrite_tac[]) >>
      fs[gas_bad_storage_at_def] >> gen_tac >>
      qmatch_goalsub_abbrev_tac `eval_expr cx e st` >>
      Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
      first_x_assum drule >> strip_tac >>
      qpat_x_assum `!tail. ~storage_trace_domain _ _ _`
        (qspec_then `tail` mp_tac) >> gvs[Abbr `st`])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                   `ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- (gen_tac >> first_x_assum irule >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >> first_x_assum drule >>
      Cases_on `res` >> simp[] >> strip_tac >>
      fs[createSizeExitTheory.create_size_exit_ok_def]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac >- (irule gas_exempt_cert_mods_unforce_result >> simp[]) >>
  qexists_tac `H` >> asm_rewrite_tac[]
QED

Triviality send_vv_post:
  expr_post_mods H ctx f cenv cx (Call NoneT (Send hg) args dflt)
    es sa sb s0 ee v (Lit 0w) u ==>
  vv_post_mods H ctx f cenv cx (Call NoneT (Send hg) args dflt)
    es sa sb s0 ee (Value v) (StackValue NoneT (Lit 0w)) u /\
  vv_own cenv cx NoneT sa sb ee (Value v) (StackValue NoneT (Lit 0w)) u
Proof
  simp[expr_post_mods_def, expr_post_def, vv_post_mods_def, vv_holds_mods_def,
       vv_holds_def, vv_at_def, vv_place_ptr_mods_def, vv_place_ptr_def,
       vv_own_def, read_result_def, return_def, vv_storage_live_def,
       post_value_type_def, expr_type_def, expr_val_own_def] >>
  strip_tac >> Cases_on `v` >>
  simp[eval_operand_def, val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
  first_assum ACCEPT_TAC
QED

Triviality send_vv_of_value:
  expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty
    (Call NoneT (Send hg) args dflt) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty
    (Call NoneT (Send hg) args dflt) es
Proof
  disch_tac >> rw[expr_vv_sim_full_mods_def] >>
  drule compile_expr_send_stack >> strip_tac >> gvs[] >>
  `lower_value compile_expr cenv ty (Call NoneT (Send hg) args dflt) sa = (Lit 0w,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call NoneT (Send hg) args dflt)) shadow_sa = (Lit 0w,shadow_sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `!s tv t. eval_expr cx (Call NoneT (Send hg) args dflt) s = (INL tv,t) ==>
      ?v. tv = Value v` by (rpt strip_tac >> drule eval_expr_send_value >> simp[]) >>
  drule_all_then assume_tac eval_expr_force_admissible >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`Lit 0w`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule send_unforce_outcome >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule_then strip_assume_tac send_vv_post >>
      simp[expr_type_def, ptr_vv_ok_def, vv_location_def, read_result_def, return_def] >>
      reverse conj_tac >- fs[expr_type_def] >>
      irule vv_store_bound_stack_value >>
      simp[lowered_value_type_def, expr_type_def, evaluate_type_def,
           valueEncodingTheory.type_memory_size_def, expr_store_bound_none]) >>
  rpt strip_tac >> gvs[expr_exit_success_map, halt_exit_def] >>
  ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

(* Source actions consume an explicitly quantified observation tail, so the
   inactive observation field at a prefix endpoint can be reset for Send. *)
Triviality send_outcome_entry_obs:
  gas_outcome_full_mods (DF,lo,explicit,ctx,f,PG) mods cx st0 source
    (es with gas_obs := [],s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,f,PG) mods cx st0 source
    (es,s,G,tn) Q R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> fs[]) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac
  >- (drule gas_exempt_cert_start_gas_obs_mods >> disch_then (qspec_then `es.gas_obs` mp_tac) >>
      simp[evaluation_state_component_equality]) >>
  qexists_tac `H` >> fs[]
QED

Triviality send_entry_obs_frames:
  (immutable_frame_mods func cenv cx (ee with gas_obs := gs) t <=>
    immutable_frame_mods func cenv cx ee t) /\
  (ghost_inv_at_mods D lo d cenv cx (ee with gas_obs := gs) G tn t <=>
    ghost_inv_at_mods D lo d cenv cx ee G tn t) /\
  (storage_well_formed_on cx (ee with gas_obs := gs) rg <=> storage_well_formed_on cx ee rg) /\
  (wb_frame cenv es (ee with gas_obs := gs) sa s0 t <=> wb_frame cenv es ee sa s0 t)
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def,
       immutable_alloca_sep_def, immutables_rel_def, ghost_inv_at_mods_def,
       wb_frame_def, locals_kept_def, popped_kept_def] >>
  irule storage_well_formed_on_backends >> simp[]
QED

(* Keep the suffix conditional, using the checked theorem's exact contract. *)
val send_tail_premise = concl (GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
  bodySendTailOutcomeModsTheory.send_tail_outcome_full_mods));
val send_prefix_premise = concl (GEN_ALL request_word_prefix_mods);
val send_shape_premise = concl (GEN_ALL send_pre_types_mods);
val send_member_premise = concl (GEN_ALL request_operand_pre_mods);

Triviality send_tail_link:
  ^send_tail_premise /\
  fn_inst_ids_distinct func /\ fn_has_code sm sb func /\
  emit_op CALL [go;ao;vo;Lit 0w;Lit 0w;Lit 0w;Lit 0w] sm = (out,s3) /\
  emit_void ASSERT [out] s3 = ((),sb) /\
  ci_mono sa sm /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    immutable_frame_mods func cenv cx ee t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t) /\
  wb_frame cenv es ee sa s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts /\
  op_taint tn go = {} /\ op_taint tn ao = {} /\ op_taint tn vo = {} /\
  eval_operand go t = SOME gw /\
  w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gs) dest_NumV of
                NONE => 0 | SOME g => g) /\
  eval_operand ao t = SOME aw /\ dest_AddressV a = SOME (w2w aw) /\
  eval_operand vo t = SOME vw /\ dest_NumV v = SOME (w2n vw) /\
  LENGTH gs = (if hg then 1 else 0) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_send cx hg (a::v::gs)) (read_result cx)) (ee,t,G,tn)
    (\H res ef G' tn' z. ?ret. res = INL ret /\
       expr_post_mods H ctx func cenv cx (Call NoneT (Send hg) args dflt)
         es sa sb s0 ef ret (Lit 0w) z /\
       expr_store_bound cx (expr_type (Call NoneT (Send hg) args dflt)) ret (Lit 0w) z /\
       z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' z /\
       ptr_val_ok cx (expr_type (Call NoneT (Send hg) args dflt)) ret (Lit 0w) G' tn' z /\
       (~is_word_type (expr_type (Call NoneT (Send hg) args dflt)) ==>
        ptr_buf_ok cenv (Call NoneT (Send hg) args dflt) (Lit 0w) G' z) /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  irule send_outcome_entry_obs >>
  qabbrev_tac `e = Call NoneT (Send hg) args dflt` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ef G' tn' z. res = INL NoneV /\
      expr_post_mods H ctx func cenv cx e es sa sb s0 ef NoneV (Lit 0w) z /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' z /\
      ghost_kept_at lo cenv (ee with gas_obs := []) sm G tn t G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ z.vs_alloca_next = t.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z)`,
    `\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)`] >>
  BETA_TAC >> simp[] >> reverse conj_tac
  >- (first_assum irule >>
      simp[send_entry_obs_frames, stmt_state_rel_start_gas_obs, Abbr `e`,
           supportedExprTraverseTheory.expr_has_effect_def, expr_type_def, post_value_type_def] >>
      conj_tac >- (gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
      qexistsl_tac [`ao`,`aw`,`go`,`gw`,`s3`,`out`,`vo`] >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Abbr `e`, expr_type_def, expr_store_bound_none, ptr_val_ok_none,
       ptr_buf_ok_zero_type, send_none_buffer_size] >>
  irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`func`] >>
      fs[storage_trace_domain_def] >> first_x_assum drule >> simp[]) >>
  qexistsl_tac [`G`,`ee`,`ee with gas_obs := []`,`t`,`sm`,`tn`] >> simp[]
QED

Triviality send_value_from_parts:
  ^send_tail_premise /\ ^send_prefix_premise /\ ^send_member_premise /\
  MAP expr_type args = [BaseT AddressT; BaseT (UintT 256)] ++
      (if hg then [BaseT (UintT 256)] else []) /\
  LENGTH args = (if hg then 3 else 2) /\ EVERY (\e. is_word_type (expr_type e)) args /\
  body_exprs_full_ok_mods mods exps cx args /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Call NoneT (Send hg) args dflt) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call NoneT (Send hg) args dflt) es
Proof
  strip_tac >> rw[expr_sim_full_mods_def] >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (all_tac >> suspend "prefix") >>
  irule gas_outcome_full_mods_bad_nil >> simp[] >>
  qmatch_goalsub_abbrev_tac `SND (action _)` >>
  `storage_trace_frame action` by
    simp[Abbr `action`, bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
  drule_all_then mp_tac gas_bad_storage_at_initial >>
  disch_then (qspecl_then [`s0`,`[]`] mp_tac o REWRITE_RULE [gas_bad_storage_at_def]) >> simp[]
QED

Resume send_value_from_parts[prefix]:
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then strip_assume_tac send_word_cut_code >> gvs[] >>
  drule_then assume_tac send_action_bind >> fs[] >>
  first_assum irule >>
  simp[storage_trace_frame_bind_all, storage_trace_frame_send,
       storage_trace_frame_read_result, combinTheory.o_DEF] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> goal_assum drule) >>
  qexistsl_tac [`expr_type`,`d`,`env`,`exps`,`mods`,`sa`,`sm`,
                `shadow_func`,`shadow_sa`,`shm`,`src`,`tops`,
                `[ao;vo] ++ (if hg then [go] else [])`] >>
  simp[gas_shadow_expr_type] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`NoneT`,`args`,`dflt`,`es`,`ARB`,`hg`,`Send hg`] >> simp[]) >>
  reverse conj_tac
  >- (drule_then assume_tac expr_body_pre_mods_inv >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "continuation"
QED

Resume send_value_from_parts[continuation]:
  qx_genl_tac [`reads`,`vs`,`ee`,`G`,`tn`,`t`] >> strip_tac >>
  `?obs. ee.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `!tail. eval_exprs cx args _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     simp[evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac (SIMP_RULE bool_ss [APPEND] send_word_values) >> gvs[] >>
  `ci_mono sa sm` by
    (qpat_assum `lower_word_args cenv _ _ _ = (_,sm)`
       (ACCEPT_TAC o MATCH_MP ci_mono_lower_word_args)) >>
  `op_taint tn go = {}` by
    (Cases_on `hg` >> fs[ptrDisciplineTheory.op_taint_def]) >>
  `accounts_runtime_well_typed ee.accounts /\ outcomes_accounts_typed ee.outcomes` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ ee`
       (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_mods_def]) >>
     simp[accounts_runtime_well_typed_accounts_well_typed]) >>
  qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [typed_args_post_def])) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `wb_frame _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def,locals_kept_def]) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  irule send_tail_link >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_gen_tac `hor` >> strip_tac >>
      `valid_horizon cx st0 hor es.storage_trace` by
        (irule gasOutcomeFullTheory.valid_horizon_append >> qexists_tac `obs` >> fs[]) >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _`
        (qspec_then `hor` mp_tac) >>
      fs[typed_args_post_def]) >>
  qexistsl_tac [`ao`,`aw`,`go`,`gw`,`out`,`s3`,`sm`,`vo`] >> simp[]
QED

Finalise send_value_from_parts

Theorem send_case_from_parts_mods:
  ^send_shape_premise /\ ^send_member_premise /\ ^send_prefix_premise /\
  ^send_tail_premise /\
  (!s x t. type_check (LENGTH args = (if hg then 3 else 2)) "Send args" s =
     (INL x,t) ==> body_exprs_full_ok_mods mods exps cx args) ==>
  body_expr_full_ok_mods mods exps cx (Call ann (Send hg) args dflt)
Proof
  strip_tac >> pure_once_rewrite_tac[body_expr_full_ok_mods_def] >> simp[NoAsms] >>
  rpt gen_tac >> strip_tac >> first_assum drule >> strip_tac >>
  qpat_x_assum `ann = NoneT` SUBST_ALL_TAC >>
  qpat_x_assum `dflt = NONE` SUBST_ALL_TAC >>
  `body_exprs_full_ok_mods mods exps cx args` by
    (qpat_assum `!s x t. type_check _ _ _ = _ ==> _` irule >>
     qexistsl_tac [`es`,`es`,`()`] >>
     simp[type_check_def, check_def, assert_def, return_def]) >>
  conj_asm1_tac
  >- (irule send_value_from_parts >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule send_vv_of_value >> simp[]
QED
