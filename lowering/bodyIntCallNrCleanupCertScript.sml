Theory bodyIntCallNrCleanupCert
Ancestors
  bodyIntCallNrGuardCert bodyIntCallSeamDefs gasExemptCert
  gasOutcomeInitialObsPtr gasSummary vyperState vyperInterpreter
Libs
  monadsyntax

(* Expose conditional cleanup using certificate-supported handler and bind. *)
Theorem finally_unless_halt_handler:
  finally_unless_halt f g =
  bind (try f (\ex. if ex = HaltException then raise ex
                   else ignore_bind g (raise ex)))
       (\v. ignore_bind g (return v))
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
  Cases_on `f st` >> rename1 `f st = (res,ee)` >>
  Cases_on `res`
  >- simp[finally_unless_halt_def, try_def, bind_def] >>
  rename1 `f st = (INR ex,ee)` >> Cases_on `ex` >>
  simp[finally_unless_halt_def, try_def, bind_def] >>
  simp[ignore_bind_def, bind_def, raise_def] >>
  Cases_on `g ee` >> rename1 `g ee = (answer,eu)` >>
  Cases_on `answer` >> simp[return_def, raise_def]
QED

Theorem unlock_if_nr_transport:
  !cx nr view st. ?eu.
    unlock_if_nr cx nr view st = (INL (),eu) /\
    (!gs. unlock_if_nr cx nr view (st with gas_obs := gs) =
       (INL (),eu with gas_obs := gs)) /\
    (!gs scopes. unlock_if_nr cx nr view
       (st with <|gas_obs := gs; scopes := scopes|>) =
       (INL (),eu with <|gas_obs := gs; scopes := scopes|>))
Proof
  rpt gen_tac >> Cases_on `nr /\ ~view` >>
  simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[release_nonreentrant_lock_def, get_transient_storage_def,
       update_transient_def, bind_def, ignore_bind_def, return_def]
QED

Theorem gas_exempt_cert_unless_halt:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (f : evaluation_state -> value evaluation_result) (return ()))
    (es,s) marks (err,ee) (leaf,fin) /\
  (!tail. g (ee with gas_obs := tail) = (INL (),eu with gas_obs := tail)) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (finally_unless_halt f g) k) (return ()))
    (es,s) marks (err,eu) (leaf,fin)
Proof
  strip_tac >>
  rewrite_tac[finally_unless_halt_handler, ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  rewrite_tac[GSYM ignore_bind_def, ignore_bind_try_unit] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[ignore_bind_def, bind_def, raise_def]
QED

Theorem lock_if_nr_result_cases:
  lock_if_nr cx nr view st = (res,ee) ==>
  (?u. res = INL u) \/
  (?err. res = INR (Error err) /\ !tops. ~unspecified_behaviour_exempt tops err)
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[raise_def, return_def, e2eDefsTheory.unspecified_behaviour_exempt_def] >>
  simp[acquire_nonreentrant_lock_def, get_transient_storage_def,
       update_transient_def, check_not_static_def, ignore_bind_def, bind_def,
       check_def, vyperStateTheory.assert_def, return_def, raise_def] >>
  rpt IF_CASES_TAC >>
  simp[vyperStateTheory.assert_def, return_def, raise_def,
       e2eDefsTheory.unspecified_behaviour_exempt_def] >>
  Cases_on `cx.txn.is_static` >>
  gvs[vyperStateTheory.assert_def, update_transient_def, return_def,
      e2eDefsTheory.unspecified_behaviour_exempt_def]
QED

Theorem lock_if_nr_gas_obs:
  lock_if_nr cx nr view (st with gas_obs := gs) =
    (FST (lock_if_nr cx nr view st),
     SND (lock_if_nr cx nr view st) with gas_obs := gs)
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  simp[acquire_nonreentrant_lock_def, get_transient_storage_def,
       update_transient_def, check_not_static_def, ignore_bind_def, bind_def,
       check_def, vyperStateTheory.assert_def, return_def, raise_def] >>
  rpt IF_CASES_TAC >>
  simp[vyperStateTheory.assert_def, return_def, raise_def, update_transient_def]
QED

Theorem intcall_rest_successful_lock:
  (?u eu. lock_if_nr cx nr (is_view_mut mut) st = (INL u,eu)) ==>
  intcall_rest cx name mut nr ss prev rtv st =
    bind (finally_unless_halt
      (finally (intcall_callee_src cx name mut nr ss) (pop_function prev))
      (unlock_if_nr cx nr (is_view_mut mut)))
      (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                 (\crv. return (Value crv))) st
Proof
  strip_tac >>
  asm_simp_tac std_ss [intcall_rest_def, intcall_callee_src_def,
                       ignore_bind_def, bind_def, finally_def,
                       finally_unless_halt_def] >> simp[]
QED

Theorem lock_if_nr_exempt_success:
  unspecified_behaviour_exempt tops err /\
  bind (lock_if_nr cx nr view) k st = (INR (Error err),ee) ==>
  ?u eu. lock_if_nr cx nr view st = (INL u,eu)
Proof
  Cases_on `lock_if_nr cx nr view st` >> rename1 `_ = (res,eu)` >>
  drule lock_if_nr_result_cases >> strip_tac
  >- metis_tac[] >>
  gvs[ignore_bind_def, bind_def] >> metis_tac[]
QED

Theorem intcall_cleanup_exempt_cert:
  gas_invoke_entry (ctx,func) s callee entered /\
  gas_exempt_cert memory tops (ctx,callee)
    (ignore_bind (intcall_callee_src cx name mut nr ss) (return ()))
    (es,entered) marks (err,ee) (leaf,fin) ==>
  ?eu. gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (intcall_rest cx name mut nr ss prev rtv) (return ()))
    (es,s) marks (err,eu) (leaf,fin)
Proof
  strip_tac >>
  `~s.vs_halted` by gvs[fragGasFocusTheory.gas_invoke_entry_def] >>
  drule_all gas_exempt_cert_invoke >> strip_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qabbrev_tac `b = \st. ?u eu. lock_if_nr cx nr (is_view_mut mut) st = (INL u,eu)` >>
  `!st gs. b (st with gas_obs := gs) = b st` by
    (rpt gen_tac >>
     simp[Abbr `b`, lock_if_nr_gas_obs, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
     Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
     Cases_on `q` >> simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  `b es` by
    (qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[intcall_callee_src_def, ignore_bind_def, bind_assoc] >>
     pure_rewrite_tac[GSYM ignore_bind_def] >>
     strip_tac >> drule_all lock_if_nr_exempt_success >>
     metis_tac[]) >>
  `gas_exempt_cert memory tops (ctx,func)
     (ignore_bind (finally (intcall_callee_src cx name mut nr ss)
                          (pop_function prev)) (return ()))
     (es with gas_obs := [],s) marks
     (err,ee with scopes := prev) (leaf,fin)` by
    (rewrite_tac[ignore_bind_finally_unit] >>
     irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
     conj_tac
     >- simp[pop_function_def, set_scopes_def, return_def] >>
     simp[gas_exempt_cert_initial_obs]) >>
  qspec_then `ee with scopes := prev` strip_assume_tac
    (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_transport) >>
  qexists_tac `eu` >>
  irule gas_exempt_cert_guarded >> conj_tac >- simp[] >>
  qexistsl_tac [`b`,
    `ignore_bind (bind (finally_unless_halt
       (finally (intcall_callee_src cx name mut nr ss) (pop_function prev))
       (unlock_if_nr cx nr (is_view_mut mut)))
       (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                  (\crv. return (Value crv)))) (return ())`] >>
  asm_simp_tac std_ss [] >> conj_tac
  >- (qx_gen_tac `st` >> simp_tac std_ss [Abbr `b`] >>
      disch_tac >> drule intcall_rest_successful_lock >>
      simp[ignore_bind_def, bind_def]) >>
  irule gas_exempt_cert_unless_halt >> qexists_tac `ee with scopes := prev` >>
  simp[]
QED
