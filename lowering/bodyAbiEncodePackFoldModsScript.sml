(* The positional argument fold, factored at the reached snapshot and suffix. *)
Theory bodyAbiEncodePackFoldMods
Ancestors
  bodyAbiEncodePosHeadPostMods bodyAbiEncodePackedPostMods bodyAbiEncodePackNilMods
  bodyECRecoverForcedTailMods bodyECRecoverOperandReturnConsMods
  bodyForcedStorageFrameMods exprSimFullBundleProps freshWrites
  gasOutcomeFullBindPathMods gasOutcomeFullPostPathMods gasOutcomeFullPostMods
  gasOriginPtrLabels gasExemptCertMods stmtSimProps exprSimSource exprSimWordArgs
  vyperStorageFootprint vyperStorageTrace exprLoweringProps bodyFullPredsMods
  gasContext gasExplicitSites exprSimDefs vyperState list finite_map bodyPtrDefs ptrDiscipline

val forced = ``\e. vyperState$bind (eval_expr cx e) (read_result cx)``;
val next = ``\xs v. vyperState$bind (eval_exprs cx xs) (\vs. return (v::vs))``;
val list_ok = ``\res : value list + exception.
  case res of INL vs => T | INR ex => expr_res_ok (INR ex)``;
fun expr_exit_quote result_ty = inst [alpha |-> result_ty]
  ``\(H:(bool # 256 word # type_value) list # num list)
    (res:'a + exception) ee (gt:(string |-> (num # num)) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val head_exit = expr_exit_quote ``:value``;
val exit = expr_exit_quote ``:value list``;
val pack = inst [alpha |-> ``:exception``] ``abi_encode_packed_post_mods mods (DF:((bool # 256 word # type_value) list # num list) -> dead)
    lo d ctx func ce cx env``;
val head_post = ``abi_encode_pos_head_post_mods mods (DF:((bool # 256 word # type_value) list # num list) -> dead)
    lo d ctx func ce cx env``;
val code = ``expr_sim_full_code (ctx,shadow_ctx,func,shadow_func)``;
val gas_config =
  rand (rator ``gasOutcomeFullMods$gas_outcome_full_mods
    (DF,lo,gasExplicitSites$gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods``);

val entry = ``\sa es s0 G0 tn0.
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods ce cx env es /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val head_cut = ``\e xs sa sha sm shm ss shs vv sv.
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  compile_snapshot_vv (gas_shadow_env T ce) (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) shm = (sv,shs) /\
  ^code (sa,ss,sha,shs) /\ ^code (sa,sm,sha,shm) /\ fn_has_code sm ss func``;

val suffix_cut = ``\xs svs ss sb shs shb.
  compile_abi_encode_args compile_expr ce xs ss = (svs,sb) /\
  compile_abi_encode_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr xs) shs = (svs,shb) /\ ^code (ss,sb,shs,shb)``;

val cut_rule = ``!e xs sa sb sha shb all.
  ^suffix_cut (e::xs) all sa sb sha shb ==>
  ?vv sm shm sv ss shs svs. all = sv::svs /\
    ^head_cut e xs sa sha sm shm ss shs vv sv /\
    ^suffix_cut xs svs ss sb shs shb /\ ci_mono sa ss /\ ci_mono ss sb``;

val head_rule = ``!e xs sa sha sm shm ss shs vv sv es s0 G0 tn0.
  ^head_cut e xs sa sha sm shm ss shs vv sv /\
  ^entry sa es s0 G0 tn0 /\ body_expr_full_ok_mods mods exps cx e /\
  expr_body_pre_mods mods ce cx env e es /\ type_alloc_ok ce (lowered_value_type ce e) /\
  gas_admissible (^forced e) expr_res_ok es ==>
  gas_outcome_full_mods ^gas_config mods cx st0 (^forced e) (es,s0,G0,tn0)
    (^head_post e sa sm ss vv sv (exprs_can_mutate ce xs) es s0 G0 tn0) ^head_exit``;

(* The already evaluated prefix is relative to the original source argument list. *)
val prefix = ``\pre xs vs0 obs0 es.
  args = pre ++ xs /\
  (!tail. eval_exprs cx pre (root with gas_obs := obs0 ++ tail) =
    (INL vs0,es with gas_obs := tail))``;

val finish_rule = ``!pre e xs vs0 obs0 sa sb sha shb sm shm ss shs vv sv svs
                      es s0 G0 tn0 marks v mid t G1 tn1 reads vs ee u G2 tn2 H.
  ^prefix pre (e::xs) vs0 obs0 es /\
  ^head_cut e xs sa sha sm shm ss shs vv sv /\
  ^suffix_cut xs svs ss sb shs shb /\ ci_mono sa ss /\ ci_mono ss sb /\
  ^entry sa es s0 G0 tn0 /\
  body_exprs_full_ok_mods mods exps cx (e::xs) /\
  expr_body_pre_mods mods ce cx env e es /\
  (!tail. ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  (!tail. eval_exprs cx xs (mid with gas_obs := reads ++ tail) =
    (INL vs,ee with gas_obs := tail)) /\
  mid.gas_obs = [] /\ ee.gas_obs = [] /\
  valid_horizon cx st0 H es.storage_trace /\ valid_horizon cx st0 H mid.storage_trace /\
  valid_horizon cx st0 H ee.storage_trace /\
  gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s0,G0,tn0) marks (OK t,G1,tn1) /\
  t.vs_labels = s0.vs_labels /\ u.vs_labels = t.vs_labels /\
  ^head_post e sa sm ss vv sv (exprs_can_mutate ce xs) es s0 G0 tn0 H (INL v) mid G1 tn1 t /\
  ^pack xs svs ss sb mid t G1 tn1 H (INL vs) ee G2 tn2 u ==>
  ^pack (e::xs) (sv::svs) sa sb es s0 G0 tn0 H (INL (v::vs)) ee G2 tn2 u``;

Triviality abi_pack_append_action:
  !pre xs. eval_exprs cx (pre ++ xs) =
    vyperState$bind (eval_exprs cx pre)
      (\vs. vyperState$bind (eval_exprs cx xs) (\ws. return (vs ++ ws)))
Proof
  Induct
  >- (simp[FUN_EQ_THM,bind_def,eval_exprs_nil,return_def] >> rpt gen_tac >>
      Cases_on `eval_exprs cx xs x` >> rename1 `_ = (res,_)` >> Cases_on `res` >> simp[]) >>
  simp[Once eval_exprs_cons_action] >>
  simp[Once eval_exprs_cons_action,bind_assoc,bind_return]
QED

Triviality abi_pack_extend_prefix:
  (!tail. eval_exprs cx pre (root with gas_obs := obs0 ++ tail) =
    (INL vs0,es with gas_obs := tail)) /\
  (!tail. ^forced e (es with gas_obs := obs1 ++ tail) =
    (INL v,mid with gas_obs := tail)) ==>
  !tail. eval_exprs cx (pre ++ [e]) (root with gas_obs := (obs0 ++ obs1) ++ tail) =
    (INL (vs0 ++ [v]),mid with gas_obs := tail)
Proof
  BETA_TAC >> strip_tac >> gen_tac >>
  pure_once_rewrite_tac[abi_pack_append_action] >>
  `obs0 ++ obs1 ++ tail = obs0 ++ (obs1 ++ tail)` by metis_tac[APPEND_ASSOC] >>
  pop_assum SUBST1_TAC >>
  simp[Once bind_def] >>
  pure_once_rewrite_tac[eval_exprs_cons_action] >>
  simp[Once bind_def] >>
  simp[Once bind_def] >>
  simp[Once bind_def,eval_exprs_nil,return_def]
QED

Triviality abi_pack_prepend_replay:
  ^next xs v st = (INL (v::vs),ee) ==> eval_exprs cx xs st = (INL vs,ee)
Proof
  BETA_TAC >> Cases_on `eval_exprs cx xs st` >> rename1 `_ = (res,_)` >>
  Cases_on `res` >> simp[bind_def, return_def]
QED

Triviality abi_pack_tail_source:
  body_exprs_full_ok_mods mods exps cx (e::xs) /\
  gas_admissible (eval_exprs cx (e::xs)) ^list_ok es /\
  (!tail. ^forced e (es with gas_obs := obs ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  body_exprs_full_ok_mods mods exps cx xs /\ gas_admissible (eval_exprs cx xs) ^list_ok mid
Proof
  BETA_TAC >> strip_tac >> conj_tac
  >- (qpat_assum `!tail. _ = (INL v,_)` (qspec_then `[]` mp_tac) >>
      disch_then (strip_assume_tac o MATCH_MP (REWRITE_RULE [ETA_AX] eval_expr_read_INL)) >>
      qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
      first_x_assum irule >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_admissible (eval_exprs _ (_::_)) _ _` mp_tac >>
  rewrite_tac[gas_admissible_def,eval_exprs_cons_action] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >- simp[] >>
  first_x_assum (qspec_then `obs ++ gs` mp_tac) >> simp[bind_def] >>
  disch_then irule >> goal_assum (drule_at Any)
QED

Triviality abi_pack_replay_horizon:
  storage_trace_frame f /\ valid_horizon cx st0 H ee.storage_trace /\
  (!tail. f (es with gas_obs := obs ++ tail) = (res,ee with gas_obs := tail)) ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  qpat_x_assum `!tail. f _ = _` (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  drule valid_horizon_frame >> disch_then drule >> simp[]
QED

Theorem abi_encode_pack_fold_mods:
  ^cut_rule /\ ^head_rule /\ ^finish_rule /\
  (!e es. MEM e args /\ expr_sim_inv_mods mods ce cx env es ==>
    expr_body_pre_mods mods ce cx env e es) /\
  (!e. MEM e args ==> type_alloc_ok ce (lowered_value_type ce e)) ==>
  !xs pre vs0 obs0 svs sa sb sha shb es s0 G0 tn0.
    ^prefix pre xs vs0 obs0 es /\ ^entry sa es s0 G0 tn0 /\
    ^suffix_cut xs svs sa sb sha shb /\
    body_exprs_full_ok_mods mods exps cx xs /\ gas_admissible (eval_exprs cx xs) ^list_ok es ==>
    gas_outcome_full_mods ^gas_config mods cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
      (^pack xs svs sa sb es s0 G0 tn0) ^exit
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >> Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule abi_encode_pack_nil_mods >> asm_rewrite_tac[]) >>
  suspend "cons"
QED

Resume abi_encode_pack_fold_mods[cons]:
  qx_gen_tac `e` >> rpt gen_tac >> strip_tac >>
  `MEM e args` by (simp[MEM_APPEND]) >>
  `expr_body_pre_mods mods ce cx env e es` by simp[] >>
  `body_expr_full_ok_mods mods exps cx e` by
    (qpat_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_then assume_tac ecrecover_head_admissible_mods >>
  qpat_x_assum `!e xs sa sb sha shb all. _ ==> ?vv sm. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `svs = _::_` SUBST_ALL_TAC >>
  `type_alloc_ok ce (lowered_value_type ce e)` by simp[] >>
  qpat_x_assum `!e xs sa sha sm shm ss shs vv sv es s0 G0 tn0. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (drule_all_then assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ headQ headR` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_mods_bind_all_path >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- irule bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`storage_trace_frame (bind (eval_exprs _ _) _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_return]
  >> qexists_tac `\H res mid G tn t. mid.gas_obs = [] /\ headQ H res mid G tn t` >>
  BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ headQ headR` (irule_at Any) >>
      reverse conj_tac
      >- (qx_genl_tac [`H`,`res`,`ee`,`gt`,`r`] >> Cases_on `res` >>
          simp[Abbr `headR`, halt_exit_def, expr_exit_def,
               INST_TYPE [alpha |-> ``:value``, beta |-> ``:value list``] expr_exit_INR_type]) >>
      simp[]) >>
  suspend "tail"
QED

Resume abi_encode_pack_fold_mods[tail]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _.storage_trace ==> _ /\ headQ _ _ _ _ _ _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `headQ` >>
  qhdtm_assum `abi_encode_pos_head_post_mods`
    (strip_assume_tac o REWRITE_RULE [abi_encode_pos_head_post_mods_def]) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  rename1 `gas_outcome_full_mods _ _ _ _ _ _
    (abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ (_::_) (_::svtail) _ _ _ _ _ _) _` >>
  drule_all_then strip_assume_tac (BETA_RULE abi_pack_tail_source) >>
  `gas_outcome_full_mods ^gas_config mods cx st0 (eval_exprs cx xs) (mid,t,G1,tn1)
      (^pack xs svtail ss sb mid t G1 tn1) ^exit` by suspend "ih" >>
  suspend "finish"
QED

Resume abi_encode_pack_fold_mods[ih]:
  BETA_TAC >>
  qpat_x_assum `!pre vs0 obs0 svs sa sb sha shb es s0 G0 tn0. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    irule >>
  qhdtm_assum `abi_encode_packed_post_mods`
    (strip_assume_tac o REWRITE_RULE [abi_encode_packed_post_mods_def]) >>
  rename1 `return_buf_frame d ce tail_sa t` >>
  rename1 `compile_expr ce (expr_type e) e head_sa = (vv,sm)` >>
  `head_sa.cs_next_var <= tail_sa.cs_next_var` by fs[ci_mono_def] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!fn inst u. frag_reachable _ _ t fn inst u ==> _` (drule_then ACCEPT_TAC))
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `head_sa` >> simp[])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `head_sa` >> simp[])
  >~ [`valid_horizon _ _ _ _`]
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> mid.gas_obs = [] /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (strip_assume_tac o REWRITE_RULE
        [abi_encode_pos_head_post_mods_def, abi_encode_packed_post_mods_def]) >>
      simp[])
  >- (qexistsl_tac [`obs0 ++ gas_explicit marks s0.vs_gas_readings`,`vs0 ++ [v]`] >>
      drule_all_then ACCEPT_TAC (BETA_RULE abi_pack_extend_prefix))
  >- (qexistsl_tac [`shs`,`shb`] >> simp[])
  >> irule local_ptrs_reserved_next_var >> qexists_tac `head_sa` >> simp[]
QED

Resume abi_encode_pack_fold_mods[finish]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ tailQ tailR` >>
  `gas_outcome_full_mods ^gas_config mods cx st0 (eval_exprs cx xs) (mid,t,G1,tn1)
    (\H res ee G tn u. u.vs_labels = t.vs_labels /\ tailQ H res ee G tn u) tailR` by
    (irule gas_outcome_full_mods_post_path >>
     qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ tailQ tailR` (irule_at Any) >>
     BETA_TAC >> rpt gen_tac >> strip_tac >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_origin_ptr_path_preserves_labels >> goal_assum (drule_at Any)) >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any ecrecover_operand_return_cons_mods >>
  qexistsl_tac [`tailR`, `\H res ee G tn u. u.vs_labels = t.vs_labels /\ tailQ H res ee G tn u`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (BETA_TAC >> rpt gen_tac >> disch_then (qx_choose_then `rt` strip_assume_tac) >>
      Cases_on `rt` >> gvs[Abbr `tailR`, expr_exit_def, halt_exit_def]) >>
  suspend "replay"
QED

Resume abi_encode_pack_fold_mods[replay]:
  BETA_TAC >> qx_genl_tac [`H`,`res`,`ee`,`G2`,`tn2`,`u`] >> strip_tac >>
  rename1 `tailQ H rt ee G2 tn2 u` >>
  Cases_on `rt`
  >- (gvs[Abbr `tailQ`] >> suspend "land") >>
  gvs[] >> qpat_x_assum `tailQ _ (INR _) _ _ _ _` mp_tac >>
  simp[Abbr `tailQ`, abi_encode_packed_post_mods_def]
QED

Resume abi_encode_pack_fold_mods[land]:
  rename1 `abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (INL (v::vs)) _ _ _ _` >>
  rename1 `!tail. bind (eval_exprs cx xs) (\ws. return (v::ws))
    (mid with gas_obs := reads ++ tail) = (INL (v::vs),ee with gas_obs := tail)` >>
  `!tail. eval_exprs cx xs (mid with gas_obs := reads ++ tail) = (INL vs,ee with gas_obs := tail)` by
    suspend "strip_return" >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (irule (INST_TYPE [``:'a`` |-> ``:value list``] abi_pack_replay_horizon) >>
     qexistsl_tac [`ee`,`eval_exprs cx xs`,`reads`,`INL vs`] >>
     simp[evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule (INST_TYPE [``:'a`` |-> ``:value``] abi_pack_replay_horizon) >>
     qexistsl_tac [`mid`,`bind (eval_expr cx e) (read_result cx)`,
       `gas_explicit marks s0.vs_gas_readings`,`INL v`] >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    abi_encode_pos_head_post_mods mods DF lo d ctx func ce cx env e sa sm ss vv sv
      (exprs_can_mutate ce xs) es s0 G0 tn0 H (INL v) mid G1 tn1 t`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) _ _ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `t.vs_labels = s0.vs_labels` by
    (irule gas_origin_ptr_path_preserves_labels >> goal_assum (drule_at Any)) >>
  first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (strip_tac >>
     qpat_assum `!H'. valid_horizon _ _ H' es.storage_trace ==> _`
       (qspec_then `H'` mp_tac) >> simp[]) >>
  conj_tac >- (qexistsl_tac [`obs0`,`vs0`] >> first_assum ACCEPT_TAC) >>
  qhdtm_assum `abi_encode_pos_head_post_mods` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ _ marks _` (irule_at Any) >>
  qpat_assum `compile_expr (gas_shadow_env T ce) _ (gas_shadow_expr e) _ = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ _ _ shm = _` (irule_at Any) >>
  qpat_assum `compile_abi_encode_args compile_expr _ _ shs = _` (irule_at Any) >>
  qexists `reads` >> simp[]
QED

Resume abi_encode_pack_fold_mods[strip_return]:
  qx_gen_tac `tail` >>
  qpat_assum `!tail. bind (eval_exprs cx xs) (\ws. return (v::ws))
    (mid with gas_obs := reads ++ tail) = (INL (v::vs),ee with gas_obs := tail)`
    (qspec_then `tail` mp_tac) >>
  disch_then (ACCEPT_TAC o MATCH_MP (BETA_RULE abi_pack_prepend_replay))
QED

Finalise abi_encode_pack_fold_mods
