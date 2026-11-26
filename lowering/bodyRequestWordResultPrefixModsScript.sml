(* Retype the reached word-list continuation without a second traversal. *)
Theory bodyRequestWordResultPrefixMods
Ancestors
  bodyRawRequestWordsMods bodyBranchCellFrameMods gasOutcomeFullBindMods
  gasOutcomeFullPostMods haltExitProj stmtSimProps
  exprSimHypsDefs vyperTypeInvariants loweringStateRelDefs
  exprSimPrecompiles exprSimWordArgs vyperStorageFootprint vyperState
  gasContext fragGasOriginPtr gasExemptCertMods vyperStorageTrace vyperInterpreter
  bodyFullPredsMods bodyFullPostsMods gasOutcomeFull exprSimDefs
  bodyInvSplit exprLoweringProps bodyFullShadowBodyInv stmtSimForRounds
Libs monadsyntax

val pack = ``\vs. return (ArrayV (TupleV vs))``;
val unpack = ``\v. case v of ArrayV (TupleV vs) => vs | _ => []``;

Triviality packed_bind_retype:
  bind (bind source ^pack) (\v. next ((^unpack) v)) = bind source next
Proof
  simp[bind_assoc, bind_return, ETA_THM]
QED

Triviality packed_bind_success:
  bind source ^pack es = (INL (ArrayV (TupleV vs)),ee) <=>
  source es = (INL vs,ee)
Proof
  Cases_on `source es` >> Cases_on `q` >> simp[bind_def,return_def]
QED

Triviality packed_bind_admissible:
  gas_admissible (bind source next) ok es /\
  (!exc. ok (INR exc) ==> expr_res_ok (INR exc)) ==>
  gas_admissible (bind source ^pack) expr_res_ok es
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >>
  Cases_on `source (es with gas_obs := gs)` >> Cases_on `q` >>
  simp[bind_def, return_def] >> strip_tac >> gvs[]
  >- simp[expr_res_ok_def] >>
  rename1 `source _ = (INR exc,ee)` >> first_assum irule >>
  qpat_assum `gas_admissible _ _ _` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  disch_then (qspecl_then [`gs`,`INR exc`,`ee`] mp_tac) >> simp[bind_def]
QED

Triviality packed_exit_retype:
  expr_exit (res : value + exception) r /\ halt_exit H cx ee res r ==>
  ?exc. res = INR exc /\ expr_exit (INR exc : 'a + exception) r /\
        halt_exit H cx ee (INR exc : 'a + exception) r
Proof
  Cases_on `res` >> simp[halt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Triviality packed_endpoint_frames:
  (typed_args_post H ctx func cenv cx es sa s0 (ee with gas_obs := gs) ws xs vs t <=>
   typed_args_post H ctx func cenv cx es sa s0 ee ws xs vs t) /\
  (immutable_frame_mods func cenv cx (ee with gas_obs := gs) t <=>
   immutable_frame_mods func cenv cx ee t) /\
  (ghost_inv_at_mods D lo d cenv cx (ee with gas_obs := gs) G tn t <=>
   ghost_inv_at_mods D lo d cenv cx ee G tn t)
Proof
  `storage_well_formed_on cx (ee with gas_obs := gs) (FST H) <=>
   storage_well_formed_on cx ee (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  simp[typed_args_post_def,wb_frame_gas_obs,immutable_frame_mods_def,
       immutables_rel_mods_def,immutable_alloca_sep_mods_def,
       immutable_alloca_sep_def,immutables_rel_def,ghost_inv_at_mods_def]
QED

Triviality packed_inv_obs:
  expr_sim_inv_mods mods cenv cx env (ee with gas_obs := gs) <=>
  expr_sim_inv_mods mods cenv cx env ee
Proof
  simp[expr_sim_inv_mods_def,gas_obs_type_invariants]
QED

val at_horizon = ``\(H : (bool # 256 word # type_value) list # num list).
  typed_args_post H ctx func cenv cx es sa s0 ee ws xs vs t /\
  immutable_frame_mods func cenv cx ee t /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val reached = ``
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                      value_has_type tv v) ws vs /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) xs /\
  EVERY (\op. (!l. op <> Label l) /\ (!z. op = Var z ==> not_fresh_at sb z)) xs /\
  expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val packed_post = ``\H (res : value + exception) ee G tn t. ?vs.
  res = INL (ArrayV (TupleV vs)) /\ (^at_horizon) H /\ ^reached``;

val result_outcome = ``\action entry Q R.
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 action entry Q R``;

Theorem request_word_result_prefix_mods:
  !ws es sa shadow_sa xs sb shadow_sb s0 G0 tn0
      (next : value list -> evaluation_state -> 'a evaluation_result).
  body_exprs_full_ok_mods mods exps cx ws /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  (!e mid. MEM e ws /\ expr_sim_inv_mods mods cenv cx env mid /\
     body_const_cells_agree_mods mods cx env mid ==>
     expr_body_pre_mods mods cenv cx env e mid) /\
  EVERY (is_word_type o expr_type) ws /\
  (!e. MEM e ws ==> arg_ty (gas_shadow_expr e) = arg_ty e) /\
  lower_word_args cenv arg_ty ws sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) arg_ty
    (MAP gas_shadow_expr ws) shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_exprs cx ws) next) ok es /\
  (!exc. ok (INR exc) ==> expr_res_ok (INR exc)) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!H (res : 'a + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
     (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r) /\
  (!reads vs ee G tn t.
     (!tail. eval_exprs cx ws (es with gas_obs := reads ++ tail) =
         (INL vs,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> (^at_horizon) H) /\
     ^reached /\ gas_admissible (next vs) ok ee ==>
     (^result_outcome) (next vs) (ee,t,G,tn) Q R) ==>
  (^result_outcome) (bind (eval_exprs cx ws) next) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (bind (eval_exprs cx ws) ^pack) (es,s0,G0,tn0)
     ^packed_post (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)`
    by (BETA_TAC >> suspend "packed") >>
  once_rewrite_tac[GSYM packed_bind_retype] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >> BETA_TAC >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_return]
  >- simp[] >>
  qexists_tac `^packed_post` >> BETA_TAC >>
  reverse conj_tac >- first_assum (ACCEPT_TAC o BETA_RULE) >> suspend "continue"
QED

Resume request_word_result_prefix_mods[packed]:
  `gas_admissible (bind (eval_exprs cx ws) ^pack) expr_res_ok es` by
    (drule_all packed_bind_admissible >> simp[]) >>
  irule request_word_prefix_mods >> simp[storage_trace_frame_return] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "exit" >>
  goal_assum (drule_at (Pat `module_body_inv _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_full_code _ _`)) >>
  goal_assum (drule_at (Pat `lower_word_args cenv _ ws sa = _`)) >>
  goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
  goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  suspend "pure"
QED

Resume request_word_result_prefix_mods[pure]:
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_mods_pure >> simp[return_def] >>
  qexistsl_tac [`G`,`ee`,`INL (ArrayV (TupleV vs))`,`t`,`tn`] >>
  simp[gas_origin_ptr_path_rules, packed_endpoint_frames, packed_inv_obs] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> qpat_assum `!fn inst u. frag_reachable ctx func t fn inst u ==> _`
    (drule_then ACCEPT_TAC)
QED

Resume request_word_result_prefix_mods[exit]:
  rpt strip_tac >> drule_all_then strip_assume_tac packed_exit_retype >>
  qexists_tac `exc` >> simp[] >> first_x_assum irule >> simp[]
QED

Resume request_word_result_prefix_mods[continue]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?vs. _`
    (drule_then strip_assume_tac) >> gvs[packed_bind_success] >>
  `gas_admissible (next vs) ok mid` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  first_x_assum irule >> simp[] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Finalise request_word_result_prefix_mods
