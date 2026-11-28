(* Source wrapper transport for noncompleted internal calls. *)
Theory bodyFullIntCallReturnSource
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams gasOutcomeFull gasExemptCert
  fragGasOriginPtr gasSummary fragGasMode vyperInterpreter vyperState vyperAST
  gasShadowCompileBase[qualified,ignore_grammar]
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]
Libs
  monadsyntax

Theorem unlock_if_nr_total[local]:
  !cx nr view st.
    ?ee. (!gs. unlock_if_nr cx nr view (st with gas_obs := gs) =
                 (INL (), ee with gas_obs := gs))
Proof
  rpt gen_tac >>
  simp[unlock_if_nr_def] >>
  Cases_on `nr /\ ~view` >> simp[]
  >- (Cases_on `cx.nonreentrant_slot`
      >- (qexists_tac `st` >> simp[return_def]) >>
      rename1 `cx.nonreentrant_slot = SOME slot` >>
      qexists_tac `SND (release_nonreentrant_lock cx.txn.target slot st)` >>
      simp[release_nonreentrant_lock_def,
           record_storage_event_def, get_transient_storage_def,
           update_transient_def, bind_def, ignore_bind_def, return_def]) >>
  qexists_tac `st` >> simp[return_def]
QED

Theorem pop_function_total[local]:
  !prev st. !gs. pop_function prev (st with gas_obs := gs) =
    (INL (), (st with scopes := prev) with gas_obs := gs)
Proof
  simp[pop_function_def, set_scopes_def, return_def]
QED

Theorem intcall_exempt_pop[local]:
  !memory tops ctx func a es s marks err ee leaf fin prev.
    gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (a : evaluation_state -> value evaluation_result) (return ()))
      (es,s) marks (err,ee) (leaf,fin) ==>
    gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (finally a (pop_function prev)) (return ()))
      (es,s) marks (err,ee with scopes := prev) (leaf,fin)
Proof
  rpt strip_tac >> rewrite_tac[ignore_bind_finally_unit] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
  simp[pop_function_total]
QED

Theorem finally_unless_halt_bind_handler[local]:
  !a u k.
    (!st. ?ee. u st = (INL (),ee)) ==>
    bind (finally_unless_halt a u) k =
    bind (try a (\ex. if ex = HaltException then raise ex
                         else ignore_bind u (raise ex)))
      (\v. ignore_bind u (k v))
Proof
  rpt strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `a x` >> Cases_on `q` >>
  simp[finally_unless_halt_def, try_def, bind_def, ignore_bind_def,
       raise_def, return_def] >>
  first_x_assum (qspec_then `r` strip_assume_tac) >>
  simp[bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `y` >> simp[bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem intcall_exempt_unlock[local]:
  !memory tops ctx func a es s marks err ee leaf fin cx nr view k.
    gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (a : evaluation_state -> value evaluation_result) (return ()))
      (es,s) marks (err,ee) (leaf,fin) ==>
    ?ee'. gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (bind (finally_unless_halt a (unlock_if_nr cx nr view))
         (k : value -> evaluation_state -> eval_result evaluation_result))
                   (return ()))
      (es,s) marks (err,ee') (leaf,fin)
Proof
  rpt strip_tac >>
  qspec_then `ee` strip_assume_tac
    (Q.SPECL [`cx`, `nr`, `view`] unlock_if_nr_total) >>
  rename1 `!gs. unlock_if_nr cx nr view (ee with gas_obs := gs) =
                  (INL (),out with gas_obs := gs)` >>
  qexists_tac `out` >>
  `!st. ?ee. unlock_if_nr cx nr view st = (INL (),ee)` by
    (gen_tac >> qspec_then `st` strip_assume_tac
       (Q.SPECL [`cx`, `nr`, `view`] unlock_if_nr_total) >>
     first_x_assum (qspec_then `st.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  simp[finally_unless_halt_bind_handler] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  rewrite_tac[ignore_bind_try_unit] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[ignore_bind_def] >>
  simp[raise_def, ignore_bind_def, bind_def] >> gvs[]
QED

Theorem intcall_exempt_lock_success[local]:
  !cx name mut nr ss st gs ee tops err.
    unspecified_behaviour_exempt tops err /\
    intcall_callee_src cx name mut nr ss (st with gas_obs := gs) =
      (INR (Error err),ee) ==>
    ?locked. !tail. lock_if_nr cx nr (is_view_mut mut)
      (st with gas_obs := tail) = (INL (),locked with gas_obs := tail)
Proof
  rpt gen_tac >>
  disch_tac >>
  qexists_tac `SND (lock_if_nr cx nr (is_view_mut mut) st)` >>
  pop_assum mp_tac >>
  reverse (Cases_on `nr`) >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[intcall_callee_src_def, lock_if_nr_def, ignore_bind_def,
       bind_def, raise_def] >>
  simp[acquire_nonreentrant_lock_def, record_storage_event_def,
       get_transient_storage_def, update_transient_def,
       ignore_bind_def, bind_def, return_def, raise_def,
       check_not_static_def] >>
  rpt IF_CASES_TAC >> simp[raise_def, return_def, bind_def] >>
  strip_tac >> simp[update_transient_def, assert_def, bind_def,
                    return_def, raise_def, check_def] >>
  gvs[check_def, assert_def, bind_def, return_def, raise_def,
      e2eDefsTheory.unspecified_behaviour_exempt_def]
QED

Theorem intcall_rest_locked[local]:
  !cx name mut nr ss prev rtv st locked.
    lock_if_nr cx nr (is_view_mut mut) st = (INL (),locked) ==>
    intcall_rest cx name mut nr ss prev rtv st =
    bind (finally_unless_halt
      (finally (intcall_callee_src cx name mut nr ss) (pop_function prev))
      (unlock_if_nr cx nr (is_view_mut mut)))
      (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                  (\crv. return (Value crv))) st
Proof
  rpt strip_tac >>
  asm_simp_tac bool_ss
    [intcall_rest_def, intcall_callee_src_def, ignore_bind_def,
     bind_def, finally_def, finally_unless_halt_def,
     pairTheory.pair_case_thm, sumTheory.sum_case_def]
QED

Theorem intcall_return_source_exit:
  !cx name mut nr ss st gs ex ee r prev rtv.
    expr_exit (INR ex : value + exception) r /\
    (!tail. intcall_callee_src cx name mut nr ss
       (st with gas_obs := gs ++ tail) = (INR ex,ee with gas_obs := tail)) ==>
    ?out.
      (!tail. intcall_rest cx name mut nr ss prev rtv
        (st with gas_obs := gs ++ tail) = (INR ex,out with gas_obs := tail)) /\
      (!st0 H. valid_horizon cx st0 H out.storage_trace ==>
                valid_horizon cx st0 H ee.storage_trace) /\
      (ex = HaltException ==> out = ee with scopes := prev) /\
      (!st0. storage_trace_domain cx st0 ee.storage_trace ==>
                storage_trace_domain cx st0 out.storage_trace)
Proof
  rpt gen_tac >> strip_tac >>
  `!tail. lock_if_nr cx nr (is_view_mut mut) (st with gas_obs := gs ++ tail) =
     (FST (lock_if_nr cx nr (is_view_mut mut) st),
      SND (lock_if_nr cx nr (is_view_mut mut) st) with gas_obs := gs ++ tail)` by
    (Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
     simp[lock_if_nr_def, return_def, raise_def,
       acquire_nonreentrant_lock_def, record_storage_event_def,
       get_transient_storage_def, update_transient_def,
       ignore_bind_def, bind_def, check_not_static_def,
       assert_def, check_def, AllCaseEqs()] >>
     rpt IF_CASES_TAC >> simp[return_def, raise_def, bind_def,
       assert_def, check_def] >> rpt IF_CASES_TAC >>
     gvs[return_def, raise_def, bind_def, ignore_bind_def, update_transient_def]) >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >> Cases_on `q`
  >- suspend "locked" >>
  suspend "lock_failed"
QED
Resume intcall_return_source_exit[locked]:
  Cases_on `x` >>
  Cases_on `ex = HaltException` >-
    (qexists_tac `ee with scopes := prev` >> simp[] >> gen_tac >>
     `lock_if_nr cx nr (is_view_mut mut) (st with gas_obs := gs ++ tail) =
       (INL (),r' with gas_obs := gs ++ tail)` by gvs[] >>
     drule intcall_rest_locked >>
     disch_then (qspecl_then [`name`,`ss`,`prev`,`rtv`] SUBST1_TAC) >>
     gvs[finally_unless_halt_def, finally_def, bind_def, pop_function_def,
         set_scopes_def, return_def, ignore_bind_def, raise_def]) >>
  qspec_then `ee with scopes := prev` strip_assume_tac
    (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_total) >>
  qexists_tac `ee'` >> conj_tac
  >- (gen_tac >>
      `lock_if_nr cx nr (is_view_mut mut) (st with gas_obs := gs ++ tail) =
        (INL (),r' with gas_obs := gs ++ tail)` by gvs[] >>
      drule intcall_rest_locked >>
      disch_then (qspecl_then [`name`,`ss`,`prev`,`rtv`] SUBST1_TAC) >>
      qpat_assum `!gs. unlock_if_nr _ _ _ _ = _`
        (qspec_then `tail` assume_tac) >>
      rule_assum_tac (REWRITE_RULE [unlock_if_nr_def]) >>
      Cases_on `ex` >>
      gvs[finally_unless_halt_def, finally_def, bind_def,
           pop_function_def, set_scopes_def, return_def, ignore_bind_def,
           raise_def]) >>
  conj_tac >- (
  rpt strip_tac >>
  qpat_x_assum `!gs. unlock_if_nr _ _ _ _ = _`
    (qspec_then `ee.gas_obs` mp_tac) >>
  simp[] >> strip_tac >>
  drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
  disch_then (qspecl_then [`st0`,`cx`,`H`] mp_tac) >>
  mp_tac (Q.INST [`view` |-> `is_view_mut mut`]
    vyperStorageTraceTheory.storage_trace_frame_optional_locks) >>
  simp[unlock_if_nr_def] >> metis_tac[]) >>
  simp[] >> suspend "domain"
QED
Resume intcall_return_source_exit[domain]:
  rpt strip_tac >>
  qpat_x_assum `!gs. unlock_if_nr _ _ _ _ = _`
    (qspec_then `[]` mp_tac) >>
  simp[unlock_if_nr_def] >>
  Cases_on `nr /\ mut <> View /\ mut <> Pure` >> simp[return_def]
  >- (Cases_on `cx.nonreentrant_slot` >> simp[return_def]
      >- (disch_then (mp_tac o Q.AP_TERM `\s. s.storage_trace`) >> simp[] >> metis_tac[]) >>
      rename1 `cx.nonreentrant_slot = SOME slot` >>
      simp[vyperTypeEvalStoragePreservationTheory.release_nonreentrant_lock_eq] >>
      disch_then (mp_tac o Q.AP_TERM `\s. s.storage_trace`) >>
      simp[] >> disch_then (SUBST1_TAC o SYM) >>
      `MEM (StorageLock slot) r'.storage_trace` by
        (qpat_x_assum `lock_if_nr _ _ _ st = _` mp_tac >>
         simp[lock_if_nr_def, ignore_bind_def, bind_def,
              vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq] >>
         rpt IF_CASES_TAC >>
         simp[check_not_static_def, bind_def, return_def, raise_def] >>
         rpt IF_CASES_TAC >> simp[return_def, raise_def] >>
         strip_tac >> gvs[]) >>
      `?obs. ee.storage_trace = r'.storage_trace ++ obs` by
        (qpat_x_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `!tail. lock_if_nr _ _ _ _ = _`
           (qspec_then `[]` assume_tac) >>
         pure_rewrite_tac[intcall_callee_src_def, ignore_bind_def, bind_def] >>
         asm_simp_tac bool_ss [pairTheory.FST, pairTheory.SND,
           pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
         strip_tac >>
         qpat_x_assum `try _ _ _ = _`
           (mp_then Any mp_tac vyperStorageTraceTheory.storage_trace_frame_prefix) >>
         impl_tac >- (
           irule vyperStorageTraceTheory.storage_trace_frame_try >> conj_tac
           >- simp[vyperStorageTraceTheory.storage_trace_frame_function_handler] >>
           irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
           simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
                vyperStorageTraceTheory.storage_trace_frame_return]) >>
         simp[]) >>
      `MEM (StorageLock slot) ee.storage_trace` by simp[] >>
      `MEM slot (vyperStorageFootprint$storage_trace_locks ee.storage_trace)` by
        (simp[NoAsms, vyperStorageFootprintTheory.storage_trace_locks_def,
              listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
         qexists_tac `[slot]` >> simp[] >>
         qexists_tac `StorageLock slot` >> simp[]) >>
      qpat_x_assum `ee.storage_trace = _` kall_tac >>
      qpat_x_assum `storage_trace_domain _ _ _` mp_tac >>
      simp[NoAsms, vyperStorageFootprintTheory.storage_trace_domain_def,
           vyperStorageFootprintTheory.valid_horizon_def,
           vyperStorageFootprintTheory.storage_trace_horizon_def,
           vyperStorageFootprintTheory.storage_observations_ok_def,
           vyperStorageFootprintTheory.storage_trace_regions_def,
           vyperStorageFootprintTheory.storage_trace_locks_def,
           vyperStorageFootprintTheory.storage_locks_separated_def,
           vyperStorageFootprintTheory.storage_roots_fit_def,
           vyperStorageFootprintTheory.storage_trace_backends_well_formed_def,
           listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
           listTheory.EVERY_MEM] >>
      strip_tac >>
      qpat_x_assum `MEM slot (vyperStorageFootprint$storage_trace_locks _)`
        (assume_tac o REWRITE_RULE
          [vyperStorageFootprintTheory.storage_trace_locks_def]) >>
      qpat_assum `!observation. MEM observation _ ==> case observation of StorageRoot b offset tv => offset + type_slot_size tv <= _ | StorageLock lk => lk + 1 <= _ | StorageOutcome a b => T | StorageBackend a b => T`
        (qspec_then `StorageLock slot` mp_tac) >>
      simp[] >> metis_tac[]) >>
  disch_then (mp_tac o Q.AP_TERM `\s. s.storage_trace`) >> simp[] >> metis_tac[]
QED
Resume intcall_return_source_exit[lock_failed]:
  gvs[] >>
  `ex <> HaltException` by
    (`ex = y` by
       (qpat_x_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
          (qspec_then `[]` mp_tac) >>
        qpat_assum `!tail. _ (st with gas_obs := gs ++ tail) = (INR y,_)`
          (qspec_then `[]` (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
        rule_assum_tac (REWRITE_RULE [ignore_bind_def]) >>
        simp[intcall_callee_src_def, lock_if_nr_def, ignore_bind_def, bind_def] >>
        strip_tac >> gvs[]) >>
     qpat_x_assum `(if nr then _ else _) st = (INR y,_)` mp_tac >>
     pop_assum (fn th => SUBST1_TAC (SYM th)) >>
     Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
     simp[AllCaseEqs(), acquire_nonreentrant_lock_def, record_storage_event_def,
          get_transient_storage_def, update_transient_def, ignore_bind_def,
          bind_def, check_not_static_def, assert_def, check_def,
          return_def, raise_def] >>
     rpt (IF_CASES_TAC >> simp[return_def, raise_def, bind_def]) >>
     gvs[update_transient_def, assert_def, check_def, return_def, raise_def]) >>
  qexists_tac `ee` >> simp[] >> gen_tac >>
  qpat_x_assum `!tail. intcall_callee_src _ _ _ _ _ _ = _`
    (qspec_then `tail` mp_tac) >>
  qpat_assum `!tail. _ (st with gas_obs := gs ++ tail) = (INR _,_)`
    (qspec_then `tail` assume_tac) >>
  rule_assum_tac (REWRITE_RULE [ignore_bind_def]) >>
  simp[intcall_callee_src_def, intcall_rest_def, lock_if_nr_def,
       ignore_bind_def, bind_def] >>
  strip_tac >> gvs[]
QED
Finalise intcall_return_source_exit

(* Transport the certificate along source equality on the initial gas orbit. *)
Theorem gas_exempt_cert_source_orbit_cong[local]:
  !memory tops ctx func f g es s marks err ee leaf finish.
    ~s.vs_halted /\
    gas_exempt_cert memory tops (ctx,func) f (es,s)
      marks (err,ee) (leaf,finish) /\
    (!gs. f (es with gas_obs := gs) = g (es with gas_obs := gs)) ==>
    gas_exempt_cert memory tops (ctx,func) g (es,s)
      marks (err,ee) (leaf,finish)
Proof
  rpt strip_tac >>
  qabbrev_tac `a = \st:evaluation_state.
    ((INL ((st with gas_obs := []) = (es with gas_obs := [])), st)
      : bool evaluation_result)` >>
  qabbrev_tac `k = \b:bool. if b then f else g` >>
  `bind a k = g` by
    (simp[FUN_EQ_THM, bind_def, Abbr `a`, Abbr `k`] >>
     gen_tac >> IF_CASES_TAC >> simp[] >>
     `x = es with gas_obs := x.gas_obs` by
       gvs[evaluation_state_component_equality] >>
     metis_tac[]) >>
  `gas_marked_exec memory (ctx,func) a (es,s) [] (INL T) es (OK s)` by
    (simp[gas_marked_exec_def, Abbr `a`] >>
     irule gas_marked_path_from_mem >>
     simp[fragGasPathMemTheory.gas_path_mem_rules]) >>
  `gas_exempt_cert memory tops (ctx,func) (k T)
     (es with gas_obs := [],s) marks (err,ee) (leaf,finish')` by
    (simp[Abbr `k`] >>
     drule gas_exempt_cert_start_gas_obs >> simp[]) >>
  drule_all gas_exempt_cert_bind_bool >> simp[]
QED

Theorem intcall_exempt_rest[local]:
  !memory tops ctx func cx name mut nr ss prev rtv es s marks err ee leaf fin.
    ~s.vs_halted /\
    gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (intcall_callee_src cx name mut nr ss) (return ()))
      (es,s) marks (err,ee) (leaf,fin) ==>
    ?out. gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (intcall_rest cx name mut nr ss prev rtv) (return ()))
      (es,s) marks (err,out) (leaf,fin)
Proof
  rpt strip_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  `?locked. !gs. lock_if_nr cx nr (is_view_mut mut)
       (es with gas_obs := gs) = (INL (),locked with gas_obs := gs)` by
    (irule intcall_exempt_lock_success >>
     first_assum (irule_at Any) >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
     metis_tac[]) >>
  drule intcall_exempt_pop >>
  disch_then (qspec_then `prev` assume_tac) >>
  drule intcall_exempt_unlock >>
  disch_then (qspecl_then [`cx`,`nr`,`is_view_mut mut`] mp_tac) >>
  disch_then (qspec_then
    `\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                (\crv. return (Value crv))` mp_tac) >> strip_tac >>
  qexists_tac `ee'` >> gvs[] >>
  irule gas_exempt_cert_source_orbit_cong >>
  first_assum (irule_at Any) >> simp[] >> gen_tac >>
  `intcall_rest cx name mut nr ss prev rtv (es with gas_obs := gs) =
    bind (finally_unless_halt
      (finally (intcall_callee_src cx name mut nr ss) (pop_function prev))
      (unlock_if_nr cx nr (is_view_mut mut)))
      (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                  (\crv. return (Value crv))) (es with gas_obs := gs)` by
    (irule intcall_rest_locked >>
     qexists_tac `locked with gas_obs := gs` >> simp[lock_if_nr_def]) >>
  simp[ignore_bind_def, bind_def]
QED

Theorem intcall_bad_rest[local]:
  !cx name mut nr ss prev rtv st st0.
    ~storage_trace_domain cx st0
      (SND (intcall_callee_src cx name mut nr ss st)).storage_trace ==>
    ~storage_trace_domain cx st0
      (SND (intcall_rest cx name mut nr ss prev rtv st)).storage_trace
Proof
  rpt gen_tac >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
  Cases_on `q`
  >- (rename1 `lock_if_nr _ _ _ _ = (INL v,locked)` >>
      Cases_on `v` >>
      `intcall_rest cx name mut nr ss prev rtv st =
       bind (finally_unless_halt
         (finally (intcall_callee_src cx name mut nr ss) (pop_function prev))
         (unlock_if_nr cx nr (is_view_mut mut)))
         (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                     (\crv. return (Value crv))) st` by
        (irule intcall_rest_locked >> metis_tac[]) >>
      pop_assum SUBST1_TAC >>
      Cases_on `intcall_callee_src cx name mut nr ss st` >>
      rename1 `intcall_callee_src _ _ _ _ _ st = (res,ee)` >>
      simp[] >> strip_tac >>
      `?out. unlock_if_nr cx nr (is_view_mut mut) (ee with scopes := prev) =
                (INL (),out)` by
        (qspec_then `ee with scopes := prev` strip_assume_tac
           (Q.SPECL [`cx`,`nr`,`is_view_mut mut`] unlock_if_nr_total) >>
         first_x_assum (qspec_then `ee.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
      `~storage_trace_domain cx st0 out.storage_trace` by
        (qpat_assum `unlock_if_nr _ _ _ _ = _`
           (mp_then Any mp_tac gasStorageTheory.storage_trace_frame_preserves_bad_domain) >>
         simp[vyperStorageTraceTheory.storage_trace_frame_optional_locks]) >>
      Cases_on `res`
      >- (rename1 `intcall_callee_src _ _ _ _ _ _ = (INL v,_)` >>
          Cases_on `safe_cast rtv v` >>
          gvs[finally_unless_halt_def, finally_def, pop_function_def, set_scopes_def,
              unlock_if_nr_def, ignore_bind_def, bind_def, return_def,
              raise_def, lift_option_type_def, lift_option_def]) >>
      rename1 `intcall_callee_src _ _ _ _ _ _ = (INR ex,_)` >>
      Cases_on `ex` >>
      gvs[finally_unless_halt_def, finally_def, pop_function_def, set_scopes_def,
          unlock_if_nr_def, ignore_bind_def, bind_def, return_def, raise_def]) >>
  asm_simp_tac bool_ss
    [intcall_callee_src_def, intcall_rest_def,
     ignore_bind_def, bind_def, pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  simp[]
QED

Theorem intcall_entry_invoke_ptr:
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
    sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv ==>
  ptr_inst_ok (DF H) lo 0 ctx func G tn inst t
Proof
  strip_tac >>
  qhdtm_x_assum `intcall_entry_full`
    (strip_assume_tac o PURE_REWRITE_RULE [intcall_entry_full_def]) >>
  qhdtm_x_assum `ghost_inv_at`
    (assume_tac o cj 7 o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `EVERY (\op. op_taint tn op = {}) arg_ops` by
    (qpat_assum `!bb inst lbl arg_ops argv. _`
       (qspecl_then [`bb`,`inst`,`lbl`,`arg_ops`,`argv`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`EVERY _ arg_ops`, `decode_invoke inst = _`, `inst.inst_opcode = INVOKE`,
     `allocas_from lo t`, `ctx_has_dalloca ctx ==> allocas_below_fmp t`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def,
       ptrDisciplineTheory.access_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >>
  qpat_x_assum `decode_invoke inst = _` mp_tac >>
  simp[venomExecSemanticsTheory.decode_invoke_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[ptrDisciplineTheory.taint_ok_def, listTheory.EVERY_MEM,
      ptrDisciplineTheory.op_taint_def,
      contextCodegenRelTheory.source_memory_read_ranges_def] >>
  gen_tac >> Cases_on `op = Label lbl` >> simp[] >>
  Cases_on `MEM op arg_ops` >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[fragGasFocusTheory.gas_invoke_entry_readings] >>
  `~t.vs_halted /\ inst.inst_opcode = INVOKE` by
    gvs[fragGasFocusTheory.gas_invoke_entry_def] >>
  `!H. ptr_inst_ok (DF H) lo 0 ctx func G tn inst t` by
    (`ptr_inst_ok (DF H) lo 0 ctx func G tn inst t` by
       (qpat_assum `!h. valid_horizon _ _ h es1.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        strip_tac >> drule_all intcall_entry_invoke_ptr >>
        disch_then ACCEPT_TAC) >>
     pop_assum mp_tac >> asm_simp_tac bool_ss [ptrSafeRunTheory.ptr_inst_ok_def]) >>
  simp[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (gvs[gasStorageTheory.gas_bad_storage_at_def] >>
          metis_tac[intcall_bad_rest]) >>
      qexistsl_tac [`H'`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      simp[] >> irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_focus_rules) >>
      first_assum (irule_at Any) >> metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  `gas_exempt_cert T (cx_tops cx) (ctx,func)
     (ignore_bind (intcall_callee_src cx name mut nr ss) (return ()))
     (es1,t) marks (err,ee) (leaf,finish')` by
    metis_tac[gas_exempt_cert_invoke] >>
  drule_all intcall_exempt_rest >>
  disch_then (qspecl_then [`prev`,`rtv`] strip_assume_tac) >>
  qexistsl_tac [`err`,`out`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  simp[] >> qexists_tac `H'` >> simp[] >>
  irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_focus_rules) >>
  first_assum (irule_at Any) >> metis_tac[]
QED
*)
Theorem intcall_return_noncompleted:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 st0 sa sm shadow_sa shadow_sm vv s0 G0 tn0 mut nr args ret ss
   rr prev penv rtv es1 t G tn rc rbs pvs callee entered bb inst lbl arg_ops argv dflts Q.
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sm) /\
    compile_expr (gasShadowCompileBase$gas_shadow_env T cenv) ty
      (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa =
      (vv,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
         sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
    (?marks.
      (gas_bad_storage_at cx st0 (intcall_callee_src cx name mut nr ss) es1 entered marks /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         (storage_trace_domain cx st0 es1.storage_trace ==> valid_horizon cx st0 H es1.storage_trace) /\
         gas_origin_ptr_focus (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
           (entered,FEMPTY,tn with t_var := FEMPTY) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish)) \/
      (?err ee leaf leaf_pg leaf_g leaf_tn finish.
         gas_exempt_cert T (cx_tops cx) (ctx,callee)
           (ignore_bind (intcall_callee_src cx name mut nr ss) (return ()))
           (es1,entered) marks (err,ee) (leaf,finish) /\
         ?H. (storage_trace_domain cx st0 es1.storage_trace ==> valid_horizon cx st0 H es1.storage_trace) /\
           gas_origin_ptr_focus (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,MAP (op_prov G) arg_ops)
             (entered,FEMPTY,tn with t_var := FEMPTY) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish))) ==>
    (fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
       Q
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)))
Proof
  cheat
QED
