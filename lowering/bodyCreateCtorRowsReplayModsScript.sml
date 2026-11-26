(* Bind at the very list endpoint that supplied the saved constructor rows. *)
Theory bodyCreateCtorRowsReplayMods
Ancestors
  gasOutcomeFullBindPathMods gasOutcomeFullPostMods gasExemptCertMods
  stmtSimProps haltExitProj exprSimDefs bodyPtrDefs compileEnv
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState

val src = ``eval_exprs cx xs``;
Theorem create_ctor_rows_replay_bind_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 ^src (es,s0,G0,tn0) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!H res mid G1 tn1 t. P H res mid G1 tn1 t ==> ?vs. res = INL vs) /\
  (!vs. storage_trace_frame (next vs)) /\
  (!marks vs mid G1 tn1 t.
    (!tail. ^src (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
             (INL vs,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> P H (INL vs) mid G1 tn1 t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G1,tn1)) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (next vs) (mid,t,G1,tn1) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind ^src next) (es,s0,G0,tn0) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_mods_bind_all_path >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC >>
  qexists_tac `P` >> BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ ^src _ P _` (irule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_INL] >>
      metis_tac[expr_exit_INR_type,halt_exit_INR_type]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> P H res _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H res mid G1 tn1 t. P H res mid G1 tn1 t ==> _`
    (drule_then (qx_choose_then `vs` SUBST_ALL_TAC)) >>
  disj1_tac >> qexists_tac `vs` >> simp[] >>
  qpat_assum `!marks vs mid G1 tn1 t. _ ==> gas_outcome_full_mods _ _ _ _ (next vs) _ _ _`
    irule >> conj_tac >- (qexists_tac `marks` >> simp[]) >> simp[]
QED
