(* Joint RawRevert value composition, conditional on the compiled abort tail. *)
Theory bodyFullRawRevertValue
Ancestors
  bodyFullRawRevertInterfaces bodyFullPreds bodySimFull exprSimHypsDefs
  exprLowering gasOutcomeFullCompose
  exprOperandVar exprSimProps loweringPosts bodyPtrDefs exprSimMemDefs
  gasExemptCert vyperSystemControl vyperStorageFootprint
  vyperAST gasShadow vyperInterpreter vyperState compileEnv builtinSystem
Libs
  pairLib

Theorem raw_revert_value_full_from_tail:
  (!(H : (bool # 256 word # type_value) list # num list) ctx func cenv cx e es (sa:compile_state) (sm:compile_state)
    (sb:compile_state) (s0:venom_state) ee bs op (t:venom_state)
    cap G tn D lo d explicit PG.
    compile_raw_revert op sm = ((),sb) /\
    fn_has_code sm sb func /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ~t.vs_halted /\ ~ctx_has_dalloca ctx /\
    (!x. op = Var x ==> not_fresh_at sm x) /\
    expr_post H ctx func cenv cx e es sa sm s0 ee (BytesV bs) op t /\
    expr_store_bound cx (expr_type e) (BytesV bs) op t /\
    expr_type e = BaseT (BytesT (Dynamic cap)) /\
    evaluate_type (get_tenv cx) (expr_type e) =
      SOME (BaseTV (BytesT (Dynamic cap))) /\
    ptr_val_ok cx (post_value_type cenv e) (BytesV bs) op G tn t /\
    ghost_inv_at D lo d cenv cx ee G tn t ==>
    ?w G' tn'. !D'.
      gas_origin_ptr_path (D',lo,explicit,ctx,func,PG)
        (t,G,tn) [] (Abort Revert_abort w,G',tn')) ==>
  !cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func
   cenv env ty es.
    (!ce ct e. gas_shadow_compiles (lower_value compile_expr ce ct e)
       (lower_value compile_expr ce ct (gas_shadow_expr e))) /\
    body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Call ann RawRevert args dflt) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann RawRevert args dflt) es
Proof
  disch_then (mk_asm "tail_contract") >> rpt gen_tac >> strip_tac >>
  drule raw_revert_source_pre >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (first_x_assum irule >> gvs[expr_body_pre_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (gvs[body_exprs_full_ok_def] >>
     qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  suspend "compiler"
QED

Resume raw_revert_value_full_from_tail[compiler]:
  `!child ss. ?sm. compile_expr cenv ty (Call NoneT RawRevert [child] NONE) ss =
       (StackValue NoneT (Lit 0w),sm)` by
    (rpt gen_tac >> simp[Once compile_expr_def, compile_call_def, expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> metis_tac[]) >>
  `compile_expr cenv ty (Call NoneT RawRevert [e] NONE) sa =
       (StackValue NoneT (Lit 0w),sb) /\
   compile_expr cenv ty (gas_shadow_expr (Call NoneT RawRevert [e] NONE))
       shadow_sa = (StackValue NoneT (Lit 0w),shadow_sb)` by
    (qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _` mp_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def] >>
     simp[lower_value_def, comp_bind_def] >>
     rpt (pairarg_tac >> simp[]) >>
     `vv' = StackValue NoneT (Lit 0w) /\ vv = StackValue NoneT (Lit 0w)` by
       metis_tac[pairTheory.PAIR_EQ] >>
     gvs[unwrap_value_def, comp_return_def]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e))` by simp[] >>
  drule_all raw_revert_layout_shadow >> strip_tac >>
  suspend "operand"
QED

Resume raw_revert_value_full_from_tail[operand]:
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (rw[gasContextTheory.gas_admissible_def] >>
     Cases_on `res` >- simp[exprSimDefsTheory.expr_res_ok_def] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `INR y`, `ee`] mp_tac) >>
     asm_rewrite_tac[] >>
     once_rewrite_tac[bind_assoc] >>
     pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >>
     simp[exprSimDefsTheory.expr_res_ok_def]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ssm`, `data`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "compose"
QED

Resume raw_revert_value_full_from_tail[compose]:
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (fn th => assume_tac th) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  asm_rewrite_tac[] >> once_rewrite_tac[bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  suspend "bind"
QED

Resume raw_revert_value_full_from_tail[bind]:
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl [`mid`, `t`, `v`] >> fs[]) 
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) 
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> simp[bind_assoc] >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_lifts] >>
      gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_raise,
           vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def]
QED

Resume raw_revert_value_full_from_tail[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists `v` >> simp[] >>
  suspend "tail"
QED

Resume raw_revert_value_full_from_tail[tail]:
  `?bs. dest_BytesV v = SOME bs` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[] >> Cases_on `dest_BytesV v` >> simp[] >>
     qpat_x_assum `gas_admissible (bind (eval_expr cx (Call _ _ _ _)) _) _ _`
       (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,
       `INR (Error (TypeError "raw_revert data"))`, `mid`] mp_tac) >>
     asm_rewrite_tac[] >> once_rewrite_tac[bind_assoc] >>
     pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >>
     simp[lift_option_type_def, bind_def, raise_def, read_result_def,
       exprSimDefsTheory.expr_res_ok_def, vyperStateTheory.evaluation_state_component_equality]) >>
  `?bs. v = BytesV bs` by
    (Cases_on `v` >> gvs[vyperValueTheory.dest_BytesV_def]) >> gvs[] >>
  `env.type_defs = get_tenv cx /\
   well_typed_expr env e /\
   (!id et. FLOOKUP env.var_types id = SOME et ==>
       well_formed_type env.type_defs et)` by
    (qpat_x_assum `expr_body_pre cenv cx env e es` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rewrite_tac[expr_body_pre_def, expr_sim_inv_def] >> strip_tac >>
     qpat_x_assum `env_consistent _ _ _` mp_tac >>
     rewrite_tac[vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def,
        vyperTypeInvariantsTheory.env_scopes_consistent_def] >> strip_tac >>
     simp[vyperTypeSystemTheory.well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `well_formed_type (get_tenv cx) (expr_type e)` by
    metis_tac[exprSafeOperandTheory.well_typed_expr_type_well_formed] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic n)))` by
    (gvs[vyperTypeSystemTheory.well_formed_type_def,
         vyperValueTheory.evaluate_type_def] >> metis_tac[]) >>
  `!x. data = Var x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e
      es sa sm s0 mid (BytesV bs') data t /\
   ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid G1 tn1 t /\
   expr_store_bound cx (expr_type e) (BytesV bs') data t` by simp[] >>
  `?w G2 tn2. !D'.
     gas_origin_ptr_path (D',lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (Abort Revert_abort w,G2,tn2)` by
    (asm "tail_contract"
       (fn th => let val curried = pp (Pos (el 8)) th
                 in drule curried end) >>
     disch_then (drule_then mp_tac o pp (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_then mp_tac o pp (Pos hd)) >>
     disch_then (drule_then mp_tac o pp (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >>
     simp[] >>
     disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] mp_tac) >>
     simp[]) >>
  irule gas_outcome_full_exit >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G2`, `mid`, `Abort Revert_abort w`,
    `INR (Error (RevertData bs'))`, `tn2`] >>
  simp[lift_option_type_def, vyperValueTheory.dest_BytesV_def,
    bind_def, return_def, raise_def, Abbr `childR`,
    exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def] >>
  gvs[vyperValueTheory.dest_BytesV_def]
QED

Finalise raw_revert_value_full_from_tail
