(* Execute the linked offset once, before considering the calldata suffix. *)
Theory bodyCalldataSliceBindMods
Ancestors
  bodyFullPredsMods bodyFullIfExpReach bodyBopBytestringPrepareMods
  bodyForcedStorageFrameMods bodyWriteSubscriptSourceMods
  exprBodyPreProps exprWordOperand exprSimSliceCompose exprSimWordArgs
  exprSimHypsDefs vyperTypeExprSoundness vyperTypeEvalCaseProofs vyperTypeSystem
  exprSimCalldataSlice exprSimHash exprSimDefs exprSimSource loweringPosts bodyFullPostsMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods haltExitProj stmtSimProps fragGasOriginPtr gasOutcomeFull
  bodyPtrDefs bodyMemoryDefs bodyFullShadowBodyInv
  stateRelProj loweringStateRelDefs allocLimits valueTypingMemoryProps
  vyperInterpreter vyperStorageTrace vyperStorageFootprint vyperState
  vyperAST vyperContext vyperTypeInvariants vyperValue vyperTyping
  exprLoweringProps compileEnv words arithmetic list
Libs monadsyntax

val E = ``Builtin (BaseT (BytesT (Dynamic m))) (CalldataSlice n) [e]``;
val read_e = ``bind (eval_expr cx e) (read_result cx)``;
val action = ``\v (u:evaluation_state).
  ((case builtin_result cx u.accounts (BaseT (BytesT (Dynamic m)))
       (CalldataSlice n) [expr_type e] [v] of
      INL w => INL (Value w) | INR exc => INR exc),u)``;
val exit = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:eval_result + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val child_post = ``
  expr_post_mods (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid v x t /\
  expr_store_bound cx (post_value_type cenv e) v x t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
  ptr_val_ok cx (post_value_type cenv e) v x G1 tn1 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1``;
val headroom = ``!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u``;

Triviality calldata_slice_action:
  eval_expr cx ^E = bind ^read_e ^action
Proof
  irule eval_expr_unary_builtin_action >>
  simp[precompile_builtin_def,builtin_args_length_ok_def,is_self_codesize_def]
QED

Triviality calldata_slice_capacity:
  expr_body_pre_mods mods cenv cx env ^E es /\ n <= m ==>
  32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) /\
  type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) < dimword (:256)
Proof
  strip_tac >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) < 2 ** 64` by
    (qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_mods_def, alloc_limits_expr_def, type_alloc_ok_def,
          is_word_type_def]) >>
  `m <= 32 * word_size m` by simp[word_size_capacity] >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) = 32 + 32 * word_size m` by
    (simp_tac bool_ss [type_memory_bytes_def, vfmConstantsTheory.word_size_def] >> decide_tac) >>
  gvs[] >> simp[dimword_def] >> decide_tac
QED

Triviality calldata_slice_source_ready:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\ expr_type e = BaseT (UintT 256) /\
  ^read_e (es with gas_obs := obs) = (INL v,mid) ==>
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  context_well_typed cx /\ ?a. v = IntV (&a) /\ a < dimword (:256)
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  simp[] >> conj_tac >- fs[expr_sim_inv_mods_def] >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >> simp[env_consistent_def,env_context_consistent_def]) >>
  fs[value_runtime_typed_def] >> gvs[evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  qexists_tac `Num i` >> simp[dimword_def] >> intLib.COOPER_TAC
QED

Triviality calldata_slice_word_shape:
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) ==>
  sa.cs_next_var <= sm.cs_next_var /\ (!z. x = Var z ==> not_fresh_at sm z)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
  drule_all_then strip_assume_tac exprWordOperandTheory.lower_value_word_shape >> simp[]
QED

(* Q is the caller's VV success post.  The exit post is fixed by the
   linked VV judgment even when the child, rather than the suffix, exits. *)
Theorem calldata_slice_bind_reached_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env ^E es /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  expr_type e = BaseT (UintT 256) /\ 0 < n /\ n <= m /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) sha = (x,shm) /\
  gas_shadow_state sa sha /\ gas_shadow_state sm shm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  gas_admissible (eval_expr cx ^E) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!marks v a mid G1 tn1 t.
    v = IntV (&a) /\ a < dimword (:256) /\
    (!tail. ^read_e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
    expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
    context_well_typed cx /\ t.vs_call_ctx.cc_calldata = cx.txn.calldata /\
    LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
    eval_operand x t = SOME (n2w a) /\ op_prov G1 x = NONE /\ op_taint tn1 x = {} /\
    (!z. x = Var z ==> not_fresh_at sm z) /\
    local_ptrs_reserved cenv sm /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    return_buf_frame d cenv sm t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ ^headroom /\
    (ctx_has_dalloca ctx ==>
       t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> ^child_post) /\
    32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) /\
    type_memory_bytes cenv (BaseT (BytesT (Dynamic m))) < dimword (:256) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 ((^action) v) (mid,t,G1,tn1) Q ^exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_expr cx ^E) (es,s0,G0,tn0) Q ^exit
Proof
  BETA_TAC >> strip_tac >>
  drule_all_then strip_assume_tac calldata_slice_capacity >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     rpt (goal_assum (drule_at Any))) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (irule bop_bytestring_child_sim_mods >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `gas_admissible ^read_e expr_res_ok es` by
    (qpat_assum `gas_admissible (eval_expr cx _) _ _` mp_tac >>
     once_rewrite_tac[calldata_slice_action] >>
     disch_then (ACCEPT_TAC o MATCH_MP slice_gas_admissible_expr_head)) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  once_rewrite_tac[calldata_slice_action] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> BETA_TAC >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >- simp[storage_trace_frame_def] >>
  qexists_tac `\H res mid G1 tn1 t. (?v. res = INL v /\ ^child_post) /\
    mid.gas_obs = [] /\ ~t.vs_halted /\ ^headroom` >>
  BETA_TAC >> conj_tac >- suspend "reached" >> suspend "post"
QED

Resume calldata_slice_bind_reached_mods[post]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res mid G1 tn1 t. childQ H res mid G1 tn1 t /\ ^headroom`, `childR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                       INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  simp[Abbr `childQ`] >> rpt strip_tac
  >- (qexists_tac `v` >> asm_rewrite_tac[]) >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Resume calldata_slice_bind_reached_mods[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> ^child_post` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  `^read_e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL,frame])))) >>
  drule_all_then strip_assume_tac calldata_slice_source_ready >>
  drule_all_then strip_assume_tac calldata_slice_word_shape >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame ^read_e` by
       ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame >>
     drule_all_then strip_assume_tac vyperStorageTraceTheory.storage_trace_frame_prefix >>
     simp[] >> REWRITE_TAC[gasOutcomeFullTheory.valid_horizon_append]) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid v x t` by
    fs[expr_post_mods_def] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid t` by
    fs[expr_post_def] >>
  `eval_operand x t = SOME (n2w a)` by
    (drule expr_post_word_operand >>
     simp[evaluate_type_def, loweringSliceTheory.word_value_def,
          valueEncodingTheory.val_to_w256_def,integer_wordTheory.i2w_pos]) >>
  `post_value_type cenv e = BaseT (UintT 256)` by
    (qpat_assum `is_word_type (expr_type e)`
       (mp_then Any mp_tac post_value_type_word) >> simp[]) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    (qpat_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `post_value_type cenv e = _` (fn th =>
       simp_tac bool_ss [ptr_val_ok_def,th,is_word_type_def]) >>
     strip_tac >> asm_rewrite_tac[]) >>
  `t.vs_call_ctx.cc_calldata = cx.txn.calldata` by
    fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def] >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by fs[context_well_typed_def,dimword_def] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp` by
    (drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[expr_post_def]) >>
  `local_ptrs_reserved cenv sm` by (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> first_x_assum irule >> goal_assum (drule_at Any)) >>
  disj1_tac >> qexists_tac `v` >> conj_tac >- simp[] >>
  qpat_x_assum `!mk w a mid G1 tn1 t. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qspecl_then [`marks`,`v`,`a`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  impl_tac >- rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  simp[]
QED

Finalise calldata_slice_bind_reached_mods
