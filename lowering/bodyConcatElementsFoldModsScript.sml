(* Linked Concat traversal, conditional only on the one-head cut and
   observation transport for the endpoint certificates. *)
Theory bodyConcatElementsFoldMods
Ancestors
  bodyConcatCutsMods bodyAugGuardedPrefixMods gasOutcomeFullBindMods
  gasOutcomeFullMods gasOutcomeFullPostMods gasExemptCertMods gasSummary
  fragGasOriginPtr fragGasSeqPtr fragExec gasExplicitSites
  exprSimWordArgs stmtSimProps haltExitProj exprLowering exprSimDefs compileEnv
  vyperAST vyperContext vyperValue vyperTyping venomState
  vyperStorageFootprint vyperStorageTrace vyperInterpreter vyperState words list

(* At a normal endpoint retain the source equation and the whole family
   of paths for the same marks and witnesses, not just the current H. *)
Theorem concat_keep_head_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f
    (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f
    (es,s,G,tn)
    (\H res mid g ts t. mid.gas_obs = [] /\ ~t.vs_halted /\
      ?marks. (!tail. f (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                        (res,mid with gas_obs := tail)) /\
        (!K. valid_horizon cx st0 K mid.storage_trace ==>
          gas_origin_ptr_path (DF K,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,g,ts) /\
          Q K res mid g ts t)) R
Proof
  disch_then (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> gvs[] >>
      disj1_tac >> conj_tac
      >- (qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
            (drule_then (assume_tac o CONJUNCT1)) >>
          drule gas_origin_ptr_path_projections >> strip_tac >>
          drule gas_path_ptr_ok_not_halted >> simp[]) >>
      qexists_tac `marks` >> simp[] >> rpt strip_tac >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> gvs[exit_result_def]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

val list_post = ``\args bs (H : (bool # bytes32 # type_value) list # num list)
    (res : value list + vyperState$exception) ee g ts t.
    ?vs. res = INL vs /\ ee.gas_obs = [] /\
      LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                             value_has_type tv v) args vs /\
      concat_live_mods (func,cenv,lo) scratch (ee,sb,t,g,ts)
        (bs ++ FLAT (MAP concat_payload_mods vs)) /\
      concat_old_frame_mods (func,cenv,lo,pure) scratch anchor (ee,sb,t,g,ts) /\
      concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,sb,t,g,ts) /\
      expr_sim_inv_mods mods cenv cx env ee /\ return_buf_frame d cenv sb t``;

val list_exit = ``\(H : (bool # bytes32 # type_value) list # num list)
   (res : value list + vyperState$exception) ee
   (gt : (string |-> num # num) # taint) r.
   expr_exit res r /\ halt_exit H cx ee res r /\
   (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

val fold_obs = ``!ee s1 t g ts bs H gs.
  concat_live_mods (func,cenv,lo) scratch (ee,s1,t,g,ts) bs /\
  concat_old_frame_mods (func,cenv,lo,pure) scratch anchor (ee,s1,t,g,ts) /\
  concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,s1,t,g,ts) /\
  expr_sim_inv_mods mods cenv cx env ee ==>
  concat_live_mods (func,cenv,lo) scratch (ee with gas_obs := gs,s1,t,g,ts) bs /\
  concat_old_frame_mods (func,cenv,lo,pure) scratch anchor (ee with gas_obs := gs,s1,t,g,ts) /\
  concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee with gas_obs := gs,s1,t,g,ts) /\
  expr_sim_inv_mods mods cenv cx env (ee with gas_obs := gs)``;

Theorem concat_fold_nil[local]:
  ^fold_obs /\
  concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
    [] (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx []) (es,s,G,tn) (^list_post [] bs) ^list_exit
Proof
  BETA_TAC >> strip_tac >>
  qhdtm_x_assum `concat_loop_entry_mods`
    (strip_assume_tac o REWRITE_RULE[concat_loop_entry_mods_def]) >>
  `sa = sb /\ shadow_sa = shadow_sb` by
    (PairCases_on `scratch` >> fs[concat_loop_code_mods_def,compile_concat_def,comp_return_def]) >>
  `~s.vs_halted` by (PairCases_on `scratch` >> fs[concat_live_mods_def]) >>
  gvs[] >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G`,`es`,`INL []`,`s`,`tn`] >>
  simp[eval_exprs_nil,gas_origin_ptr_path_rules] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> concat_horizon_mods _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!ee s1 t g ts bs H gs. _ ==> _`
    (qspecl_then [`es`,`sa`,`s`,`G`,`tn`,`bs`,`H`,`[]`] mp_tac) >> simp[]
QED

Theorem concat_fold_tail[local]:
  mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,G2,tn2)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx args) (mid,u,G2,tn2)
    (^list_post args (bs ++ concat_payload_mods v)) ^list_exit ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx args) (\vs. return (v::vs))) (mid,t,G1,tn1)
    (^list_post (e::args) bs) ^list_exit
Proof
  BETA_TAC >> strip_tac >> irule augassign_zero_prefix_guarded_mods >>
  conj_tac >- (irule storage_trace_frame_bind_all >>
    simp[evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`G2`,`u`,`tn2`] >> conj_tac >- first_assum ACCEPT_TAC >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!w. storage_trace_frame (return (_::w))`]
  >- simp[storage_trace_frame_return]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[]) >>
  qexists_tac `^list_post args (bs ++ concat_payload_mods v)` >> BETA_TAC >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ _ _` (irule_at Any) >>
      BETA_TAC >> conj_tac
      >- (rpt strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
      qx_genl_tac [`H`,`res`] >> Cases_on `res` >> simp[]) >>
  suspend "return_cons"
QED

Resume concat_fold_tail[return_cons]:
  qx_genl_tac [`marks`,`res`,`ee`,`g`,`ts`,`w`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> ?vs. _` (drule_then strip_assume_tac) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  irule gas_outcome_full_mods_pure >>
  `~w.vs_halted` by (PairCases_on `scratch` >> fs[concat_live_mods_def]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[] >> qexistsl_tac [`g`,`ee`,`INL (v::vs)`,`w`,`ts`] >>
  simp[return_def,gas_origin_ptr_path_rules,APPEND_ASSOC] >>
  rpt strip_tac >>
  qpat_assum `!H. _ ==> ?vs. _` (drule_then strip_assume_tac) >> gvs[]
QED
Finalise concat_fold_tail

Theorem concat_elements_from_head_mods:
  ^fold_obs /\
  (!e args sb shadow_sa shadow_sb es sa s G tn bs P.
     concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
       (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
       (e::args) (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P ==>
     concat_head_cut_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
       (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
       e args (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P) ==>
  !args sb shadow_sa shadow_sb es sa s G tn bs P.
    concat_loop_entry_mods (mods,exps,cx,env,src,tops,st0,cenv,pure)
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch anchor
      args (sb,shadow_sa,shadow_sb) (es,sa,s,G,tn) bs P ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (eval_exprs cx args) (es,s,G,tn)
      (^list_post args bs) ^list_exit
Proof
  BETA_TAC >> strip_tac >> Induct
  >- (rpt strip_tac >> irule (BETA_RULE concat_fold_nil) >>
      qhdtm_assum `concat_loop_entry_mods` (irule_at Any) >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!e args sb sha shb es sa s G tn bs P. _ ==> concat_head_cut_mods _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE[concat_head_cut_mods_def])) >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sc)` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) (read_result _))`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`!v. storage_trace_frame (bind (eval_exprs _ _) (\vs. return (v::vs)))`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_return])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[]) >>
  qexists_tac `\H res mid g ts t. mid.gas_obs = [] /\ ~t.vs_halted /\
      ?marks. (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (res,mid with gas_obs := tail)) /\
        (!K. valid_horizon cx st0 K mid.storage_trace ==>
          gas_origin_ptr_path (DF K,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (s,G,tn) marks (OK t,g,ts) /\
          concat_head_post_mods (DF,lo,d,ctx,func,cenv,cx) e
            (es,sa,s,G,tn) (op,sc) K res mid g ts t)` >> BETA_TAC >>
  reverse conj_tac
  >- (irule concat_keep_head_path >> irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
        (irule_at Any) >> BETA_TAC >> simp[] >>
      qx_genl_tac [`H`,`res`] >> Cases_on `res` >> simp[] >>
      once_rewrite_tac[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                       INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "head_next"
QED

Resume concat_elements_from_head_mods[head_next]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> mid.gas_obs = [] /\ _`
    (drule_then strip_assume_tac) >>
  `?v. res = INL v` by
    (qpat_assum `!K. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (drule_then (strip_assume_tac o REWRITE_RULE[concat_head_post_mods_def] o CONJUNCT2)) >>
     goal_assum (drule_at Any)) >>
  rename1 `res = INL v` >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp_tac bool_ss [] >>
  qpat_assum `!m v ee g ts t. _ ==> ?tv u G2 tn2. _`
    (qspecl_then [`marks'`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule (BETA_RULE concat_fold_tail) >>
  qpat_assum `evaluate_type _ _ = SOME _` (irule_at Any) >>
  rename1 `concat_loop_entry_mods _ _ _ _ args _ (mid,_,u,G2,tn2) _ _` >>
  qexistsl_tac [`u`,`tn2`,`G2`] >> asm_rewrite_tac[] >>
  qpat_assum `!sb sha shb es sa s G tn bs P. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (drule_then ACCEPT_TAC)
QED
Finalise concat_elements_from_head_mods
