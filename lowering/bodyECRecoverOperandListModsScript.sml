(* Linked runs of heterogeneous word operands at paired compiler cuts. *)
Theory bodyECRecoverOperandListMods
Ancestors
  bodyECRecoverOperandConsCodeMods bodyECRecoverForcedTailMods
  bodyECRecoverOperandHeadMods bodyECRecoverOperandHeadAdapterMods
  bodyECRecoverOperandReturnConsMods bodyECRecoverOperandConsPostMods
  bodyForcedStorageFrameMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  vyperStorageFootprint immutableRegionFrameProps immutableRegionTypingProps
  bodyFullWordArgs bodyMemoryDefs exprSimWordArgs wordArgsPtr
  bodyFullPostsMods bodyInvSplit exprLoweringProps
  vyperState vyperStorageTrace fragGasOriginPtr exprSimPrecompiles bodyFullShadowBodyInv
  bodyFullPredsMods exprSimDefs loweringPosts
Libs monadsyntax

val list_ok = ``\rr : value list + exception.
  case rr of INL vs => T | INR ex => expr_res_ok (INR ex)``;

val typed_at = ``\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                              value_has_type tv v``;

val list_post = ``\todo xs sa sb es s0 G0 tn0
    (H:(bool # bytes32 # type_value) list # num list) res ee G tn u.
  ?vs. (res : value list + exception) = INL vs /\
    typed_args_post H ctx func cenv cx es sa s0 ee todo xs vs u /\
    LIST_REL (^typed_at) todo vs /\ immutable_frame_mods func cenv cx ee u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
    EVERY (\x. (!l. x <> Label l) /\ (!q. x = Var q ==> not_fresh_at sb q)) xs``;

val list_exit = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:value list + exception) ee (gt:(string |-> num # num) # taint) r.
  wb_args_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Triviality ecrecover_nil_gas_frame:
  immutable_frame_mods func cenv cx (es with gas_obs := gs) s =
    immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx (es with gas_obs := gs) locs =
    storage_well_formed_on cx es locs
Proof
  conj_tac
  >- simp[immutable_frame_mods_def, immutables_rel_mods_def,
          immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
          loweringStateRelDefsTheory.immutables_rel_def] >>
  irule storage_well_formed_on_backends >> simp[]
QED

Triviality ecrecover_operand_nil_mods:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx []) (es,s0,G0,tn0)
    ((^list_post) [] [] sa sa es s0 G0 tn0) (^list_exit)
Proof
  BETA_TAC >> strip_tac >> irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`es`,`INL []`,`s0`,`tn0`] >>
  simp[eval_exprs_nil, return_def, gas_origin_ptr_path_rules, typed_args_post_def,
       wb_frame_refl, ghost_kept_at_refl, ecrecover_nil_gas_frame] >>
  rpt strip_tac >> qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
  PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]
QED

Theorem ecrecover_operand_list_run_mods:
  !todo DF lo d PG mods exps src tops ctx shadow_ctx func shadow_func cenv cx env
     ty st0 es sa xs sb shadow_sa shadow_sb s0 G0 tn0.
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
  (!e st. MEM e todo /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env e st) /\
  (!e. MEM e todo ==> is_word_type (expr_type e) /\
        (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv)) /\
  body_exprs_full_ok_mods mods exps cx todo /\
  gas_admissible (eval_exprs cx todo) ^list_ok es /\
  lower_word_args cenv (\e. ty) todo sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) (\e. ty)
    (MAP gas_shadow_expr todo) shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx todo) (es,s0,G0,tn0)
    ((^list_post) todo xs sa sb es s0 G0 tn0) (^list_exit)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[lower_word_args_nil] >>
      match_mp_tac (SIMP_RULE (srw_ss()) [] ecrecover_operand_nil_mods) >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre_mods mods cenv cx env h es` by simp[] >>
  `is_word_type (expr_type h) /\ ?tv. evaluate_type (get_tenv cx) (expr_type h) = SOME tv` by simp[] >>
  drule_all_then strip_assume_tac ecrecover_operand_cons_code_mods >> gvs[] >>
  qpat_assum `lower_word_args cenv _ todo s1 = _`
    (assume_tac o MATCH_MP ci_mono_lower_word_args) >>
  `expr_body_pre_mods mods cenv cx env h es` by simp[] >>
  drule_then assume_tac ecrecover_head_admissible_mods >>
  `body_expr_full_ok_mods mods exps cx h` by
    (qpat_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all_then (qspec_then `PG` assume_tac) ecrecover_operand_head_run_mods_normalized >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ headQ0 headR0` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_mods_bind_all >>
  BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- irule bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`storage_trace_frame (bind (eval_exprs _ _) _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_return] >>
  qexists_tac `headQ0` >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ headQ0 headR0` (irule_at Any) >>
      reverse conj_tac
      >- (simp[Abbr `headR0`, wb_args_exit_def, halt_exit_def] >>
          rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >> simp[]) >>
  suspend "tail"
QED

Resume ecrecover_operand_list_run_mods[tail]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `headQ0` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac ecrecover_forced_tail_mods >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ parentQ parentR` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (eval_exprs cx todo) (mid,t,G1,tn1)
     ((^list_post) todo ys s1 sb mid t G1 tn1) (^list_exit)` by suspend "ih" >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ tailQ tailR` >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any ecrecover_operand_return_cons_mods >>
  qexistsl_tac [`tailR`,`tailQ`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (simp[Abbr `parentR`, Abbr `tailR`] >> rpt gen_tac >> strip_tac >>
      Cases_on `res'` >> gvs[wb_args_exit_def, halt_exit_def]) >>
  suspend "cons"
QED

Resume ecrecover_operand_list_run_mods[ih]:
  BETA_TAC >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >>
      qpat_assum `!x sz. cenv.ce_return_buf = _ ==> _` irule >>
      goal_assum (drule_at Any)) >>
  conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >>
      qpat_assum `!x sz. cenv.ce_return_pc = _ ==> _` irule >>
      goal_assum (drule_at Any)) >>
  conj_tac
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
      qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def]) >> simp[]) >>
  conj_tac
  >- (qexistsl_tac [`shadow_func`,`shadow_s1`,`shadow_sb`,`ty`] >> simp[]) >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >>
      qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def]) >>
      qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >> simp[]) >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume ecrecover_operand_list_run_mods[cons]:
  rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[Abbr `tailQ`] >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!tail. bind (eval_exprs _ _) _ _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame)) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame)) >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `ptr_val_ok cx (expr_type h) v x G1 tn1 t` by fs[] >>
  `is_word_type (expr_type h)` by simp[] >>
  `(^typed_at) h v` by (BETA_TAC >> qexists_tac `tv` >> simp[]) >>
  RULE_ASSUM_TAC BETA_RULE >>
  drule_all (BETA_RULE ecrecover_operand_cons_post_mods) >> simp[Abbr `parentQ`]
QED

Finalise ecrecover_operand_list_run_mods
