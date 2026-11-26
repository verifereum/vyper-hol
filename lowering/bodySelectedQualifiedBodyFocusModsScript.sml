(* Carry the native body focus through the reached, gas-silent lock prefix. *)
Theory bodySelectedQualifiedBodyFocusMods
Ancestors
  gasOutcomeFullMods gasExemptCertMods gasStorage fragGasOriginPtr
  fragGasOrigin fragGasPathMem gasSummary vyperStorageTrace
  vyperStorageFootprint vyperFiniteStoragePreservation vyperInterpreter vyperState
  list pair sum

val body_source = ``eval_stmts (cx with stk updated_by CONS (src,name)) ss``;
val handled_body = ``try (ignore_bind ^body_source (return NoneV)) handle_function``;
val lock = ``lock_if_nr cx nr (is_view_mut mut)``;
val callee_source = ``ignore_bind ^lock ^handled_body``;

Theorem selected_focus_horizon[local]:
  lock_if_nr cx nr view (es with gas_obs := []) =
    (INL (),locked with gas_obs := []) /\
  valid_horizon (cx with stk updated_by CONS key) st0 H locked.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  `valid_horizon cx st0 H (locked with gas_obs := []).storage_trace` by
    fs[valid_horizon_def, storage_well_formed_on_stk, storage_observations_ok_stk] >>
  `storage_trace_frame (lock_if_nr cx nr view)` by simp[storage_trace_frame_optional_locks] >>
  drule_all valid_horizon_frame >> simp[]
QED

Theorem selected_focus_bad_handler[local]:
  gas_bad_storage_at (cx with stk updated_by CONS key) st0
    (eval_stmts (cx with stk updated_by CONS key) ss) locked at_body marks ==>
  gas_bad_storage_at cx st0
    (try (ignore_bind (eval_stmts (cx with stk updated_by CONS key) ss)
            (return NoneV)) handle_function)
    locked at_body marks
Proof
  simp_tac bool_ss [gas_bad_storage_at_def] >> strip_tac >> gen_tac >>
  qpat_x_assum `!tail. _` (qspec_then `tail` mp_tac) >>
  Cases_on `eval_stmts (cx with stk updated_by CONS key) ss
    (locked with gas_obs := gas_explicit marks at_body.vs_gas_readings ++ tail)` >>
  simp_tac bool_ss [storage_trace_domain_def, valid_horizon_def,
    storage_well_formed_on_stk, storage_observations_ok_stk] >>
  Cases_on `q` >- simp[ignore_bind_def, bind_def, try_def, return_def] >>
  Cases_on `y` >> simp[ignore_bind_def, bind_def, try_def, handle_function_def,
    return_def, raise_def]
QED

Theorem selected_focus_exempt_handler[local]:
  gas_exempt_cert_mods T mods (ctx,callee) (ignore_bind ^body_source (return ()))
    (locked,at_body) marks (err,ee) (leaf,endpoint) ==>
  gas_exempt_cert_mods T mods (ctx,callee) (ignore_bind ^handled_body (return ()))
    (locked,at_body) marks (err,ee) (leaf,endpoint)
Proof
  strip_tac >> rewrite_tac[ignore_bind_try_unit, ignore_bind_return_twice] >>
  irule gas_exempt_cert_mods_handler >> qexists_tac `ee` >>
  simp[handle_function_def, ignore_bind_def, bind_def, raise_def]
QED

Theorem selected_qualified_body_focus_mods:
  (!tail. (^lock) (es1 with gas_obs := tail) = (INL (),locked with gas_obs := tail)) /\
  (storage_trace_domain cx st0 es1.storage_trace ==>
   storage_trace_domain (cx with stk updated_by CONS (src,name)) st0 locked.storage_trace) /\
  (!H. gas_origin_ptr_path (DF H,lo,X,ctx,callee,PGc)
    (entered,G,tn) [] (OK at_body,Gl,tnl)) /\
  (storage_trace_domain (cx with stk updated_by CONS (src,name)) st0 locked.storage_trace ==>
   valid_horizon (cx with stk updated_by CONS (src,name)) st0 H locked.storage_trace) /\
  gas_origin_ptr_focus (DF H,lo,X,ctx,callee,PGc)
    (at_body,Gl,tnl) marks (leaf,leaf_pg,leaf_g,leaf_tn,endpoint) /\
  (gas_bad_storage_at (cx with stk updated_by CONS (src,name)) st0
      ^body_source locked at_body marks \/
   ?err ee. gas_exempt_cert_mods T mods (ctx,callee) (ignore_bind ^body_source (return ()))
       (locked,at_body) marks (err,ee) (leaf,endpoint)) ==>
  gas_outcome_full_mods (DF,lo,X,ctx,callee,PGc) mods cx st0
    ^callee_source (es1,entered,G,tn) Q R
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_marked_exec T (ctx,callee) ^lock (es1,entered) [] (INL ()) locked (OK at_body)` by
    (qpat_assum `!H. gas_origin_ptr_path _ _ [] _` (qspec_then `H` assume_tac) >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >>
     simp_tac bool_ss [gas_marked_exec_def, gas_explicit_def, LENGTH_NIL, APPEND] >>
     simp[]) >>
  `storage_trace_domain cx st0 es1.storage_trace ==> valid_horizon cx st0 H es1.storage_trace` by
    (strip_tac >> irule selected_focus_horizon >>
     qexistsl_tac [`(src,name)`,`locked`,`nr`,`is_view_mut mut`] >> simp[]) >>
  `gas_origin_ptr_focus (DF H,lo,X,ctx,callee,PGc)
     (entered,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,endpoint)` by
    (qpat_assum `!H. gas_origin_ptr_path _ _ [] _` (qspec_then `H` assume_tac) >>
     drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
  qpat_x_assum `gas_bad_storage_at _ _ _ _ _ _ \/ _` strip_assume_tac
  >- (disj1_tac >> conj_tac
      >- (drule_then assume_tac selected_focus_bad_handler >>
          `at_body.vs_gas_readings = entered.vs_gas_readings` by
            (fs[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
             drule gas_path_mem_ok_suffix >> simp[]) >>
          fs[gas_bad_storage_at_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
          qx_gen_tac `tail` >>
          qpat_assum `!tail. (^lock) _ = _`
            (qspec_then `gas_explicit marks entered.vs_gas_readings ++ tail` assume_tac) >>
          asm_simp_tac bool_ss [Once ignore_bind_def, Once bind_def, pair_case_thm, sum_case_def] >>
          first_assum (qspecl_then [`tail`] ACCEPT_TAC)) >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`endpoint`] >> simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`endpoint`] >>
  reverse conj_tac >- (qexists_tac `H` >> simp[]) >>
  `gas_exempt_cert_mods T mods (ctx,callee) (ignore_bind ^handled_body (return ()))
     (locked with gas_obs := [],at_body) marks (err,ee) (leaf,endpoint)` by
    (`gas_exempt_cert_mods T mods (ctx,callee) (ignore_bind ^handled_body (return ()))
        (locked,at_body) marks (err,ee) (leaf,endpoint)` by
       (irule selected_focus_exempt_handler >> first_assum ACCEPT_TAC) >>
     drule gas_exempt_cert_start_gas_obs_mods >> simp[]) >>
  simp_tac bool_ss [ignore_bind_def, vyperStateTheory.bind_assoc] >>
  drule gas_exempt_cert_mods_bind_unit >>
  disch_then (irule o SIMP_RULE bool_ss [APPEND]) >>
  fs[ignore_bind_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED
