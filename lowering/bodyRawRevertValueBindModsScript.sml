(* The linked forced operand and abort use a single counted execution. *)
Theory bodyRawRevertValueBindMods
Ancestors
  bodyFullPostsMods bodyFullRawRevertInterfaces gasShadowCompileStmtHelpers
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  bodyForcedStorageFrameMods exprSimSliceCompose stmtSimForRounds
  exprOperandVar haltExitProj loweringPosts bodyPtrDefs vyperStorageTrace
  vyperStorageFootprint vyperSystemControl exprSimDefs vyperValue
  exprLowering compileEnv vyperAST vyperState gasContext gasShadow stmtSimProps
Libs pairLib

val revert_tail = ``\v. bind (lift_option_type (dest_BytesV v) "raw_revert data")
                              (\data. (raise (Error (RevertData data)) :
                                evaluation_state -> eval_result evaluation_result))``;
val revert_source = ``bind (eval_expr cx e) (read_result cx)``;

Theorem raw_revert_compiles_stack[local]:
  compile_expr ce ty (Call NoneT RawRevert [e] NONE) sa = (vv,sb) ==>
  vv = StackValue NoneT (Lit 0w)
Proof
  simp[Once compile_expr_def, compile_call_def, expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[])
QED

Theorem raw_revert_lower_value_compile[local]:
  lower_value compile_expr ce ty (Call NoneT RawRevert [e] NONE) sa = (op,sb) ==>
  compile_expr ce ty (Call NoneT RawRevert [e] NONE) sa = (StackValue NoneT (Lit 0w),sb)
Proof
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >>
  drule_then SUBST_ALL_TAC raw_revert_compiles_stack >>
  simp[unwrap_value_def, comp_return_def]
QED

Theorem raw_revert_reached_bytes[local]:
  gas_admissible (bind (^revert_tail v) (read_result cx))
    expr_res_ok (mid with gas_obs := []) ==>
  ?bs. v = BytesV bs
Proof
  Cases_on `dest_BytesV v` >> strip_tac
  >- (qpat_x_assum `gas_admissible _ _ _` (mp_tac o REWRITE_RULE[gas_admissible_def]) >>
      disch_then (qspecl_then [`[]`, `INR (Error (TypeError "raw_revert data"))`,
        `mid with gas_obs := []`] mp_tac) >>
      simp[bind_def, lift_option_type_def, raise_def, expr_res_ok_def]) >>
  Cases_on `v` >> gvs[dest_BytesV_def]
QED

Theorem raw_revert_value_from_tail_mods:
  (!(H : (bool # 256 word # type_value) list # num list)
   ctx func cenv cx e es (sa:compile_state) (sm:compile_state)
   (sb:compile_state) (s0:venom_state) ee bs op (t:venom_state)
   cap G tn D lo d explicit PG.
    compile_raw_revert op sm = ((),sb) /\ fn_has_code sm sb func /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ~t.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!x. op = Var x ==> not_fresh_at sm x) /\
    expr_post H ctx func cenv cx e es sa sm s0 ee (BytesV bs) op t /\
    expr_store_bound cx (expr_type e) (BytesV bs) op t /\
    expr_type e = BaseT (BytesT (Dynamic cap)) /\
    evaluate_type (get_tenv cx) (expr_type e) =
      SOME (BaseTV (BytesT (Dynamic cap))) /\
    ptr_val_ok cx (post_value_type cenv e) (BytesV bs) op G tn t /\
    ghost_inv_at_mods D lo d cenv cx ee G tn t ==>
    ?w G' tn'. !D'.
      gas_origin_ptr_path (D',lo,explicit,ctx,func,PG)
        (t,G,tn) [] (Abort Revert_abort w,G',tn')) ==>
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx e es ty cap.
    expr_type e = BaseT (BytesT (Dynamic cap)) /\
    evaluate_type (get_tenv cx) (expr_type e) =
      SOME (BaseTV (BytesT (Dynamic cap))) /\
    eval_expr cx (Call NoneT RawRevert [e] NONE) = bind ^revert_source ^revert_tail /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call NoneT RawRevert [e] NONE) es
Proof
  disch_then (mk_asm "tail") >> rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `compile_expr cenv ty (Call NoneT RawRevert [e] NONE) sa =
       (StackValue NoneT (Lit 0w),sb) /\
   compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Call NoneT RawRevert [e] NONE))
       shadow_sa = (StackValue NoneT (Lit 0w),shadow_sb)` by
    (conj_tac
     >- (irule raw_revert_lower_value_compile >> goal_assum (drule_at Any)) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _`
       (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def]) >>
     simp[gas_shadow_expr_def, raw_revert_lower_value_compile]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  drule_all raw_revert_layout_shadow >> strip_tac >>
  `gas_admissible (bind ^revert_source (\v. bind (^revert_tail v) (read_result cx)))
      expr_res_ok es` by
    (pure_once_rewrite_tac[GSYM bind_assoc] >> BETA_TAC >>
     qpat_assum `eval_expr _ (Call _ _ _ _) = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  drule_then assume_tac slice_gas_admissible_value_head >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`ssm`,`data`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE[expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "compose"
QED

Resume raw_revert_value_from_tail_mods[compose]:
  asm_rewrite_tac[] >> once_rewrite_tac[bind_assoc] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >- (gen_tac >> simp[bind_assoc] >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_raise,storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac >- suspend "selected" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
  simp[Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                    INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]
QED

Resume raw_revert_value_from_tail_mods[selected]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  rename1 `res = INL v` >> qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >>
  pure_rewrite_tac[REFL_CLAUSE, AND_CLAUSES] >> suspend "abort"
QED

Resume raw_revert_value_from_tail_mods[abort]:
  `gas_admissible (bind (^revert_tail v) (read_result cx))
     expr_res_ok (mid with gas_obs := [])` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  `?bs. v = BytesV bs` by (drule raw_revert_reached_bytes >> simp[]) >>
  rename1 `v = BytesV bs` >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `!x. data = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> drule_all compile_lower_value_var >> simp[]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `expr_store_bound cx (expr_type e) (BytesV bs) data t` by
    (qpat_x_assum `expr_store_bound _ (post_value_type _ _) _ _ _` mp_tac >> simp[]) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     e es sa sm s0 mid (BytesV bs) data t` by fs[expr_post_mods_def] >>
  `?w G2 tn2. !D'.
      gas_origin_ptr_path (D',lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (Abort Revert_abort w,G2,tn2)` by
    (asm "tail" (fn th => drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) th) >>
     disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `compile_raw_revert _ _ = _`)) >>
     disch_then (qspecl_then [`cap`,`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
     simp[]) >>
  irule gas_outcome_full_mods_exit >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G2`,`mid`,`Abort Revert_abort w`,`INR (Error (RevertData bs))`,`tn2`] >>
  simp[lift_option_type_def, dest_BytesV_def, bind_def, return_def, raise_def,
       Abbr `childR`, expr_exit_def, halt_exit_def, fragExecTheory.exit_result_def]
QED

Finalise raw_revert_value_from_tail_mods
