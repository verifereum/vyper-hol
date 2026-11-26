(* Compose the no-keyword positional run with the reached custom-error tail. *)
Theory bodyCustomErrorBindMods
Ancestors
  bodyFullPostsMods bodyFullPredsMods bodyFullCustomErrorLayout
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  augAssignFullRhsSaved exprSimFullBundleProps exprSimHypsDefs gasShadow
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState

val encoding = ``\vs. (bind
  (lift_option (build_custom_error_data (get_tenv cx) (SND (id:num option # string))
    (MAP SND (params:(string # type) list)) vs) "custom error encoding")
  (\data. raise (Error (RevertData data))) : evaluation_state -> unit evaluation_result)``;

val expr_exit_post = ``\(H:(bool # 256 word # type_value) list # num list) (res:value list + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val stmt_exit_post = ``\(H:(bool # 256 word # type_value) list # num list) (res:unit + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
  (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
  halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)``;

val member_pre = ``!e st. MEM e args /\ expr_sim_inv_mods cenv.ce_modules cenv cx env st ==>
  expr_body_pre_mods cenv.ce_modules cenv cx env e st``;

val entry = ``local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val pos_code = ``compile_ext_call_args compile_expr cenv []
    (MAP (lowered_value_type cenv) args) args sa = (saved,se) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) []
    (MAP (lowered_value_type cenv) args) (MAP gas_shadow_expr args) sha = (saved,te) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,se,sha,te)``;

val layout = ``\tys.
  compile_alloc_buffer (abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32)
    se = (buf,sm) /\
  emit_void MSTORE
    [buf.buf_operand; Lit (n2w (cenv.ce_method_id (SND (id:num option # string)) (MAP SND (params:(string # type) list))))]
    sm = ((),ss) /\
  fn_has_code se sm func /\ fn_has_code sm ss func /\
  (if NULL (args:expr list) then
     ?offset sn. emit_op ADD [buf.buf_operand; Lit 28w] ss = (offset,sn) /\
                 emit_inst REVERT [offset; Lit 4w] [] sn = ((),sb) /\
                 fn_has_code ss sn func /\ fn_has_code sn sb func
   else
     ?dst st encoded en offset sr len sn.
       emit_op ADD [buf.buf_operand; Lit 32w] ss = (dst,st) /\
       compile_abi_encode_values_to_buf cenv dst (ZIP (saved,tys)) st = (encoded,en) /\
       emit_op ADD [buf.buf_operand; Lit 28w] en = (offset,sr) /\
       emit_op ADD [Lit 4w; encoded] sr = (len,sn) /\
       emit_inst REVERT [offset; len] [] sn = ((),sb) /\
       fn_has_code ss st func /\ fn_has_code st en func /\
       fn_has_code en sr func /\ fn_has_code sr sn func /\ fn_has_code sn sb func)``;

Theorem custom_error_frag_from_stages_mods:
  err = CustomError id pos kw /\
  get_module_code cx (FST id) = SOME error_tops /\
  lookup_custom_error_args_in (SND id) error_tops = SOME params /\
  order_custom_error_args params err = SOME args /\
  args = custom_error_exprs err /\ MAP expr_type args = MAP SND params /\
  eval_stmt cx (Raise (RaiseCustomError err)) = bind (eval_exprs cx args) ^encoding /\
  cenv.ce_error_info (nsid_to_string id) = SOME params /\
  (!id' pos' kw' error_tops' params' args'.
    err = CustomError id' pos' kw' /\ get_module_code cx (FST id') = SOME error_tops' /\
    lookup_custom_error_args_in (SND id') error_tops' = SOME params' /\
    order_custom_error_args params' err = SOME args' ==>
    body_exprs_full_ok_mods cenv.ce_modules exps cx args') /\
  ^member_pre /\
  (!st0 sa se sha te saved s0 G0 tn0.
    body_exprs_full_ok_mods cenv.ce_modules exps cx args /\ ^member_pre /\
    ^pos_code /\ ^entry ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
      (\H res mid G1 tn1 t. ?vs. res = INL vs /\ Pos st0 sa se saved s0 G0 tn0 H vs mid G1 tn1 t)
      ^expr_exit_post) /\
  (!st0 sa sb se sha te saved buf sm ss s0 G0 tn0 marks vs mid t G1 tn1 Q.
    ^pos_code /\ ^entry /\ ci_mono sa se /\
    ^layout (MAP (lowered_value_type cenv) args) /\
    (!tail. eval_exprs cx args (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL vs, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> Pos st0 sa se saved s0 G0 tn0 H vs mid G1 tn1 t) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 (^encoding vs) (mid,t,G1,tn1) Q ^stmt_exit_post) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Raise (RaiseCustomError err))))
    (eval_stmt cx (Raise (RaiseCustomError err))) es
Proof
  BETA_TAC >> strip_tac >>
  `body_exprs_full_ok_mods cenv.ce_modules exps cx args` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[stmt_frag_full_mods_def] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`s0`,`G0`,`tn0`,`cenv'`] >> strip_tac >>
  qpat_x_assum `err = CustomError _ _ _` SUBST_ALL_TAC >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o REWRITE_RULE [gas_shadow_stmt_def, gas_shadow_raise_reason_def]) >>
  drule_all_then strip_assume_tac
    (SIMP_RULE bool_ss []
      (Q.INST [`tys` |-> `MAP (lowered_value_type cenv) args`, `ce` |-> `cenv`]
        compile_raise_custom_layout_full)) >>
  `^pos_code` by simp[expr_sim_full_code_def] >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
    (\H res mid G1 tn1 t. ?vs. res = INL vs /\ Pos st0 sa se saved s0 G0 tn0 H vs mid G1 tn1 t)
    ^expr_exit_post` by
    (qpat_assum `!st0 sa se sha te saved s0 G0 tn0. _ ==> _` irule >>
     asm_rewrite_tac [] >> qexistsl_tac [`sha`,`te`] >> simp[]) >>
  qpat_assum `eval_stmt cx (Raise (RaiseCustomError _)) = _`
    (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts, storage_trace_frame_raise]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[]) >>
  conj_tac >- simp[cj 6 evaluate_storage_trace_frame] >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_exprs cx args) _ PosQ _` >>
  qexists_tac `PosQ` >> reverse conj_tac
  >- suspend "exit" >>
  suspend "success"
QED

Resume custom_error_frag_from_stages_mods[exit]:
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs cx args) _ PosQ _`
    (irule_at Any) >>
  simp[] >> rpt gen_tac >> Cases_on `res` >>
  simp[] >> strip_tac >> drule_all augassign_expr_exit_to_stmt_exit >>
  disch_then (qspecl_then [`gt`,`RetQ`] strip_assume_tac) >> asm_rewrite_tac []
QED

Resume custom_error_frag_from_stages_mods[success]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  qunabbrev_tac `PosQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?vs. _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >> disj1_tac >> simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    Pos st0 sa se saved s0 G0 tn0 H vs mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?vs'. _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  qpat_x_assum `args = custom_error_exprs _` SUBST_ALL_TAC >>
  qpat_assum `!st0 sa sb se sha te saved buf sm ss s0 G0 tn0 marks vs mid t G1 tn1 Q. _ ==> _`
    irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`buf`,`marks`,`s0`,`sa`,`saved`,`sb`,`se`,`sha`,`sm`,`ss`,`te`,`tn0`] >>
  asm_rewrite_tac []
QED

Finalise custom_error_frag_from_stages_mods
