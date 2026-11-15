Theory bodyIntCallNrCleanup
Ancestors
  bodyIntCallNrCleanupCert bodyIntCallSeamDefs bodyIntCallCompletedSource bodyIntCallCompletedFacts
  bodyIntCallAssembly bodyIntCallCompletedPath fragExec gasOutcome gasSummary gasContext exprSimDefs fragGasFocus fragGasMode
  vyperInterpreter vyperState vyperTyping loweringHalt
Libs monadsyntax

Theorem intcall_nr_normal_source[local]:
  intcall_callee_src cx name mut nr ss st = (INL v,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu) ==>
  intcall_rest cx name mut nr ss prev rtv st =
    bind (lift_option_type (safe_cast rtv v) "IntCall cast ret")
      (\crv. return (Value crv)) (eu with scopes := prev)
Proof
  strip_tac >>
  `?u el. lock_if_nr cx nr (is_view_mut mut) st = (INL u,el)` by
    (qpat_x_assum `intcall_callee_src _ _ _ _ _ _ = _` mp_tac >>
     pure_rewrite_tac[intcall_callee_src_def, ignore_bind_def, bind_def] >>
     Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
     rename1 `_ = (res,el)` >> Cases_on `res` >> simp[]) >>
  dep_rewrite.DEP_REWRITE_TAC[intcall_rest_successful_lock] >>
  conj_tac >- metis_tac[] >>
  qspec_then `ee` strip_assume_tac
    (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_transport) >>
  gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  `eu with gas_obs := ee.gas_obs = eu` by
    (qpat_x_assum `!gs. unlock_if_nr _ _ _ (ee with gas_obs := gs) = _`
       (qspec_then `ee.gas_obs` mp_tac) >>
     simp[Excl "unlock_if_nr_def", Excl "is_view_mut_def"]) >>
  qpat_x_assum `!gs scopes. _` (qspecl_then [`ee.gas_obs`,`prev`] mp_tac) >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  disch_tac >>
  simp[finally_def, finally_unless_halt_def, pop_function_def,
    set_scopes_def, bind_def, return_def, ignore_bind_def,
    Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem intcall_nr_return_typed[local]:
  gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es /\
  intcall_callee_src cx name mut nr ss (es with gas_obs := gs) = (INL v,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu) ==>
  value_has_type rtv v /\
  intcall_rest cx name mut nr ss prev rtv (es with gas_obs := gs) =
    (INL (Value v),eu with scopes := prev)
Proof
  strip_tac >> drule_all intcall_nr_normal_source >> strip_tac >>
  Cases_on `safe_cast rtv v`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `gs` mp_tac) >>
      simp[bind_def, lift_option_type_def, raise_def, expr_vv_res_ok_def]) >>
  rename1 `safe_cast rtv v = SOME crv` >>
  drule (cj 1 safe_cast_some_eq) >> strip_tac >> gvs[] >>
  simp[bind_def, lift_option_type_def, return_def] >>
  drule safe_cast_result_well_typed >> simp[]
QED

Theorem intcall_nr_return_summary[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es /\
  gas_marked_exec F (ctx,callee) (intcall_callee_src cx name mut nr ss)
    (es,entered) marks (INL v) ee (IntRet ir cs) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu) /\
  gas_path ctx func t (LENGTH marks + k) (OK out) /\
  Q (INL (Value v)) (eu with <|scopes := prev; gas_obs := []|>) out ==>
  gas_summary_at F (ctx,func) (marks ++ REPLICATE k F)
    (intcall_rest cx name mut nr ss prev rtv) (es,t) Q R
Proof
  strip_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    (drule gas_invoke_entry_readings >> simp[]) >>
  qspec_then `ee` strip_assume_tac
    (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_transport) >>
  gvs[Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  fs[gas_marked_exec_def, gas_marked_path_def,
     Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  `!tail. intcall_rest cx name mut nr ss prev rtv
      (es with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
      (INL (Value v),eu with <|scopes := prev; gas_obs := tail|>)` by
    (gen_tac >>
     qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
       (qspec_then `tail` assume_tac) >>
     qpat_assum `!gs. unlock_if_nr _ _ _ (ee with gas_obs := gs) = _`
       (qspec_then `tail` assume_tac) >>
     drule_all intcall_nr_return_typed >>
     simp[Excl "unlock_if_nr_def", Excl "is_view_mut_def"]) >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INL (Value v)`,`eu with scopes := prev`,`OK out`] >>
  fs[gas_explicit_append]
QED

Theorem intcall_nr_error_source[local]:
  lock_if_nr cx nr (is_view_mut mut) st = (INL u,el) /\
  intcall_callee_src cx name mut nr ss st = (INR ex,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) (ee with scopes := prev) = (INL (),eu) ==>
  intcall_rest cx name mut nr ss prev rtv st =
    (INR ex,if ex = HaltException then ee with scopes := prev else eu)
Proof
  strip_tac >> dep_rewrite.DEP_REWRITE_TAC[intcall_rest_successful_lock] >>
  conj_tac >- metis_tac[] >>
  Cases_on `ex` >>
  simp[finally_def, finally_unless_halt_def, pop_function_def,
       set_scopes_def, bind_def, return_def, raise_def, ignore_bind_def,
       Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem intcall_nr_failed_lock[local]:
  lock_if_nr cx nr (is_view_mut mut) st = (INR ex,ee) ==>
  intcall_callee_src cx name mut nr ss st = (INR ex,ee) /\
  intcall_rest cx name mut nr ss prev rtv st = (INR ex,ee)
Proof
  strip_tac >>
  asm_simp_tac std_ss [intcall_callee_src_def, intcall_rest_def,
                       ignore_bind_def, bind_def] >> simp[]
QED

Theorem intcall_nr_error_transport[local]:
  (!tail. intcall_callee_src cx name mut nr ss
    (es with gas_obs := gs ++ tail) = (INR ex,ee with gas_obs := tail)) ==>
  ?ep. !tail. intcall_rest cx name mut nr ss prev rtv
    (es with gas_obs := gs ++ tail) = (INR ex,ep with gas_obs := tail)
Proof
  strip_tac >> Cases_on `lock_if_nr cx nr (is_view_mut mut) es` >>
  rename1 `_ = (res,el)` >> Cases_on `res`
  >- (qspec_then `ee with scopes := prev` strip_assume_tac
        (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_transport) >>
      qexists_tac `if ex = HaltException then ee with scopes := prev else eu` >>
      gen_tac >>
      `lock_if_nr cx nr (is_view_mut mut) (es with gas_obs := gs ++ tail) =
        (INL x,el with gas_obs := gs ++ tail)` by
        simp[lock_if_nr_gas_obs, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      qpat_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
        (qspec_then `tail` assume_tac) >>
      qpat_assum `!gs. unlock_if_nr _ _ _ (_ with gas_obs := gs) = _`
        (qspec_then `tail` assume_tac) >>
      qpat_x_assum `lock_if_nr _ _ _ es = _` kall_tac >>
      drule intcall_nr_error_source >>
      disch_then drule >>
      disch_then (qspecl_then [`rtv`,`prev`,`eu with gas_obs := tail`] mp_tac) >>
      Cases_on `ex = HaltException` >>
      gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]) >>
  qexists_tac `ee` >> gen_tac >>
  `lock_if_nr cx nr (is_view_mut mut) (es with gas_obs := gs ++ tail) =
    (INR y,el with gas_obs := gs ++ tail)` by
    simp[lock_if_nr_gas_obs, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  drule intcall_nr_failed_lock >> strip_tac >>
  first_x_assum (qspec_then `tail` assume_tac) >>
  gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem intcall_nr_abort_summary[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_marked_exec F (ctx,callee) (intcall_callee_src cx name mut nr ss)
    (es,entered) marks (INR ex) ee (Abort a cs) /\
  expr_exit (INR ex) (Abort a cs) ==>
  gas_summary_at F (ctx,func) marks
    (intcall_rest cx name mut nr ss prev rtv)
    (es,t) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    (drule gas_invoke_entry_readings >> simp[]) >>
  fs[gas_marked_exec_def, gas_marked_path_def] >>
  `gas_path ctx func t (LENGTH marks) (Abort a cs)` by
    (irule invoke_abort_counted_path >> goal_assum (drule_at Any) >> simp[]) >>
  drule intcall_nr_error_transport >>
  disch_then (qspecl_then [`rtv`,`prev`] strip_assume_tac) >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INR ex`,`ep`,`Abort a cs`] >>
  simp[exit_result_def] >>
  Cases_on `ex` >> gvs[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]
QED

Theorem intcall_nr_exit_summary[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_marked_exec F (ctx,callee) (intcall_callee_src cx name mut nr ss)
    (es,entered) marks res ee r /\ expr_exit res r ==>
  gas_summary_at F (ctx,func) marks
    (intcall_rest cx name mut nr ss prev rtv)
    (es,t) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >> Cases_on `res` >- fs[expr_exit_def] >>
  Cases_on `r` >> fs[expr_exit_def] >>
  irule intcall_nr_abort_summary >> goal_assum (drule_at Any) >> simp[] >>
  Cases_on `y` >> fs[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> fs[expr_exit_def]
QED

Theorem intcall_nr_marked_typed[local]:
  gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es /\
  gas_marked_exec F (ctx,callee) (intcall_callee_src cx name mut nr ss)
    (es,entered) marks (INL v) ee r /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu) ==>
  value_has_type rtv v
Proof
  strip_tac >> fs[gas_marked_exec_def, Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
  qspec_then `ee` strip_assume_tac
    (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_transport) >>
  gvs[Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  qpat_assum `!gs. unlock_if_nr _ _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  drule_all intcall_nr_return_typed >> simp[]
QED

Theorem intcall_nr_cleanup_outcome:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_admissible (intcall_rest cx name mut nr ss prev rtv)
    expr_vv_res_ok es /\
  gas_outcome F tops (ctx,callee) (intcall_callee_src cx name mut nr ss)
    (es,entered) (\res ee r. F) R /\
  (!res ee r. R res ee r ==> expr_exit res r \/
    ?v ir cs. res = INL v /\ r = IntRet ir cs /\ P v ee ir cs) /\
  (!marks v ee ir cs eu.
    gas_marked_exec F (ctx,callee) (intcall_callee_src cx name mut nr ss)
      (es,entered) marks (INL v) ee (IntRet ir cs) /\
    P v (ee with gas_obs := []) ir cs /\
    unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu) /\
    value_has_type rtv v ==>
    ?k out. gas_path ctx func t (LENGTH marks + k) (OK out) /\
      Q (INL (Value v)) (eu with <|scopes := prev; gas_obs := []|>) out) ==>
  gas_outcome F tops (ctx,func) (intcall_rest cx name mut nr ss prev rtv)
    (es,t) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> reverse strip_tac
  >- (qexists_tac `marks` >> disj2_tac >>
      drule_all intcall_cleanup_exempt_cert >> metis_tac[]) >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [gas_summary_at_def]) >>
  first_x_assum drule >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule intcall_nr_exit_summary >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qpat_x_assum `r = IntRet ir cs` SUBST_ALL_TAC >>
  rename1 `gas_marked_exec _ _ _ _ _ _ ee _` >>
  qspec_then `ee` strip_assume_tac
    (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_transport) >>
  `value_has_type rtv v` by
    (irule intcall_nr_marked_typed >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `marks ++ REPLICATE k F` >> disj1_tac >>
  drule_all intcall_nr_return_summary >> simp[]
QED
