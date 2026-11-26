(* Keep the argument observation and machine endpoint fixed when passing
   from the positional snapshot to the Log suffix. *)
Theory bodyLogArgBindMods
Ancestors
  bodyAbiEncodePackedPostMods stmtSimLogSource stmtSimProps haltExitProj
  exprSimDefs bodyPtrDefs bodySimFull gasSummary compileEnv
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasStorage gasExemptCertMods
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState

Triviality log_arg_exit:
  expr_exit (res : value list + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  ?ex. res = INR ex /\
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\
    (ctx_has_dalloca ctx ==>
      !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  simp[GSYM expr_exit_def,stmt_exit_ptr_def,expr_exit_INR_type,halt_exit_INR_type] >>
  Cases_on `r` >> simp[expr_exit_def]
QED

Triviality log_arg_bad_domain:
  ~s.vs_halted /\ ~storage_trace_domain cx st0 es.storage_trace ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmt cx (Log id args)) (es,s,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_mods_bad_nil >> simp[] >> gen_tac >>
  Cases_on `eval_stmt cx (Log id args) (es with gas_obs := tail)` >> simp[] >>
  drule_at (Pat `f st = _`) storage_trace_frame_preserves_bad_domain >>
  simp[evaluate_storage_trace_frame] >> qexistsl_tac [`st0`,`cx`] >> simp[]
QED

Theorem log_arg_bind_mods:
  let cfg = (DF,lo,explicit,ctx,func,PG) in
  let P = abi_encode_packed_post_mods cenv.ce_modules DF lo d ctx func cenv cx
            env args saved sa sm es s0 G0 tn0 in
  let R = \H res ee gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==>
      !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s) in
  let next = \vs. bind (lift_option (encode_source_event (get_tenv cx)
                         cx.sources cx.txn.target id vs) "Log encode event")
                  (\event. ignore_bind (check_not_static cx) (push_log event)) in
  ~s0.vs_halted /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    gas_outcome_full_mods cfg cenv.ce_modules cx st0 (eval_exprs cx args)
      (es,s0,G0,tn0) P
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) /\
  (!marks vs mid G1 tn1 t.
     (!tail. eval_exprs cx args
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL vs,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          P H (INL vs) mid G1 tn1 t /\
          (!bw capacity. d = SOME (bw,capacity) ==>
                         allocas_from (w2n bw + capacity) t)) ==>
     gas_outcome_full_mods cfg cenv.ce_modules cx st0 (next vs)
       (mid,t,G1,tn1) Q R) ==>
  gas_outcome_full_mods cfg cenv.ce_modules cx st0 (eval_stmt cx (Log id args))
    (es,s0,G0,tn0) Q R
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (qpat_x_assum `storage_trace_domain _ _ _ ==> _` (drule_then assume_tac) >>
      drule_all_then assume_tac gas_outcome_full_mods_return_buf_allocas >>
      qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ (abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _` kall_tac >>
      suspend "bind") >>
  irule log_arg_bad_domain >> simp[]
QED

Resume log_arg_bind_mods[bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ArgQ ArgR` >>
  rewrite_tac[log_eval_bind] >> irule gas_outcome_full_mods_bind_all >>
  BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_check_not_static,storage_trace_frame_state_updates]) >>
  qexists_tac `\H res ee G tn t. ArgQ H res ee G tn t /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ ArgQ ArgR` (irule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >>
      simp[Abbr `ArgR`, Excl "AND_IMP_INTRO"] >>
      rpt gen_tac >> disch_tac >> irule log_arg_exit >> simp[]) >>
  suspend "reached"
QED

Resume log_arg_bind_mods[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `ArgQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `?vs. res = INL vs` by
    (qpat_assum `abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (mp_tac o CONJUNCT1) >> rewrite_tac[abi_encode_packed_post_mods_def] >>
     disch_then (qx_choose_then `vals` (assume_tac o CONJUNCT1)) >>
     qexists_tac `vals` >> first_assum ACCEPT_TAC) >>
  rename1 `res = INL vals` >> qpat_x_assum `res = INL vals` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vals` >> simp[] >>
  qpat_assum `!marks vs mid G1 tn1 t. _` irule >>
  conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o CONJUNCT1)) >> simp[]
QED

Finalise log_arg_bind_mods
