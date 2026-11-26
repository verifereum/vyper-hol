(* Noncompleted outcomes at the selected INVOKE, with the same focus in
   the caller and in the child.  The source run_body below is parameterised by
   the already-pushed evaluation context. *)
Theory bodySelectedReturnFocusMods
Ancestors
  gasOutcomeFullMods gasExemptCertMods gasStorage fragGasOriginPtr fragGasFocus
  sourceExemptMods externalCallSelected nonreentrantEquiv vyperStorageTrace
  vyperInterpreter vyperState pair sum

Theorem lock_success_for_exempt[local]:
  unspecified_behaviour_exempt_mods mods err /\
  ignore_bind (lock_if_nr cx nr view) run_body (es with gas_obs := gs) =
    (INR (Error err),ee) ==>
  ?locked. lock_if_nr cx nr view es = (INL (),locked)
Proof
  strip_tac >> Cases_on `lock_if_nr cx nr view es` >> Cases_on `q`
  >- (Cases_on `x` >> simp[]) >>
  drule lock_if_nr_with_gas_obs >> disch_then (qspec_then `gs` assume_tac) >>
  gvs[ignore_bind_def, bind_def] >>
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  gvs[lock_if_nr_def, acquire_nonreentrant_lock_execution,
      check_not_static_def, check_def, assert_def, ignore_bind_def, bind_def,
      return_def, raise_def, AllCaseEqs(), unspecified_behaviour_exempt_mods_def]
QED

Theorem unlock_success[local]:
  !es. ?out. unlock_if_nr cx nr view es = (INL (),out)
Proof
  Cases_on `nr` >> Cases_on `view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_execution, return_def]
QED

Theorem unlock_handler[local]:
  (!st. ?out. u st = (INL (),out)) ==>
  bind (finally_unless_halt a u) k =
  bind (try a (\ex. if ex = HaltException then raise ex
                     else ignore_bind u (raise ex)))
       (\v. ignore_bind u (k v))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `a x` >> Cases_on `q` >>
  first_x_assum (qspec_then `r` strip_assume_tac) >>
  simp[finally_unless_halt_def, try_def, bind_def, ignore_bind_def,
       return_def, raise_def] >>
  Cases_on `y` >> simp[bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem cleanup_locked_call[local]:
  lock_if_nr cx nr view es = (INL (),locked) ==>
  ignore_bind (lock_if_nr cx nr view)
    (bind (finally_unless_halt (finally run_body (pop_function prev))
              (unlock_if_nr cx nr view)) k) es =
  bind (finally_unless_halt
          (finally (ignore_bind (lock_if_nr cx nr view) run_body) (pop_function prev))
          (unlock_if_nr cx nr view)) k es
Proof
  simp[ignore_bind_def, bind_def, finally_def, finally_unless_halt_def]
QED

Theorem ignore_bind_apply_cong[local]:
  a st = b st ==> ignore_bind a c st = ignore_bind b c st
Proof
  simp[ignore_bind_def, bind_def]
QED

Theorem ignore_bind_bind[local]:
  ignore_bind (bind a k) f = bind a (\v. ignore_bind (k v) f)
Proof
  simp[ignore_bind_def, bind_assoc]
QED

Theorem ignore_return_error[local]:
  ignore_bind a (return ()) st = (INR err,out) ==> a st = (INR err,out)
Proof
  Cases_on `a st` >> Cases_on `q` >> simp[ignore_bind_def, bind_def, return_def]
QED

Theorem selected_exempt_cleanup[local]:
  gas_exempt_cert_mods T mods (ctx,func)
    (ignore_bind (ignore_bind (lock_if_nr cx nr view)
      (run_body : evaluation_state -> value evaluation_result)) (return ()))
    (es,s) marks (err,ee) (leaf,endpoint) ==>
  ?out. gas_exempt_cert_mods T mods (ctx,func)
    (ignore_bind
      (ignore_bind (lock_if_nr cx nr view)
         (bind (finally_unless_halt (finally run_body (pop_function prev))
                   (unlock_if_nr cx nr view))
                (k : value -> evaluation_state -> eval_result evaluation_result)))
      (return ()))
    (es,s) marks (err,out) (leaf,endpoint)
Proof
  strip_tac >>
  drule gas_exempt_cert_execution_mods >> strip_tac >>
  `?locked. lock_if_nr cx nr view es = (INL (),locked)` by
    (qpat_assum `!tail. ignore_bind _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     drule ignore_return_error >>
     simp_tac bool_ss [listTheory.APPEND_NIL] >> strip_tac >>
     drule_all lock_success_for_exempt >> simp[]) >>
  qabbrev_tac `a = ignore_bind (lock_if_nr cx nr view) run_body` >>
  `gas_exempt_cert_mods T mods (ctx,func)
     (ignore_bind (finally a (pop_function prev)) (return ()))
     (es,s) marks (err,ee with scopes := prev) (leaf,endpoint)` by
    (rewrite_tac[ignore_bind_finally_unit] >>
     irule gas_exempt_cert_mods_cleanup >> qexists_tac `ee` >>
     simp[pop_function_def, set_scopes_def, return_def]) >>
  qspec_then `ee with scopes := prev` strip_assume_tac unlock_success >>
  rename1 `unlock_if_nr cx nr view (ee with scopes := prev) = (INL (),out)` >>
  qexists_tac `out` >>
  irule gas_exempt_cert_mods_source_cong >>
  qexists_tac `ignore_bind (bind (finally_unless_halt
       (finally a (pop_function prev)) (unlock_if_nr cx nr view)) k) (return ())` >>
  conj_tac
  >- (qx_gen_tac `gs` >> simp_tac bool_ss [Abbr `a`] >>
      `lock_if_nr cx nr view (es with gas_obs := gs) =
         (INL (),locked with gas_obs := gs)` by
        (irule lock_if_nr_with_gas_obs >> first_assum ACCEPT_TAC) >>
      irule ignore_bind_apply_cong >>
      irule cleanup_locked_call >> first_assum (irule_at Any)) >>
  simp_tac bool_ss [unlock_handler, unlock_success, Once ignore_bind_bind] >>
  irule gas_exempt_cert_mods_error_value >>
  rewrite_tac[ignore_bind_try_unit] >>
  irule gas_exempt_cert_mods_handler >> qexists_tac `ee with scopes := prev` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `tail` >>
  `unlock_if_nr cx nr view ((ee with scopes := prev) with gas_obs := tail) =
     (INL (),out with gas_obs := tail)` by
    (irule unlock_if_nr_with_gas_obs >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `unlock_if_nr _ _ _ _ = (INL (),out with gas_obs := tail)` mp_tac >>
  simp[Excl "unlock_if_nr_def", ignore_bind_def, bind_def, raise_def]
QED

Theorem selected_bad_cleanup[local]:
  (!v. storage_trace_frame (k v)) /\
  ~storage_trace_domain cx st0
    (SND (ignore_bind (lock_if_nr cx nr view) run_body es)).storage_trace ==>
  ~storage_trace_domain cx st0
    (SND (ignore_bind (lock_if_nr cx nr view)
       (bind (finally_unless_halt (finally run_body (pop_function prev))
                 (unlock_if_nr cx nr view)) k) es)).storage_trace
Proof
  strip_tac >> Cases_on `lock_if_nr cx nr view es` >> Cases_on `q`
  >- (Cases_on `x` >> rename1 `lock_if_nr _ _ _ es = (INL (),locked)` >>
      Cases_on `run_body locked` >> rename1 `run_body locked = (res,ee)` >>
      qpat_x_assum `~storage_trace_domain _ _ _` mp_tac >>
      asm_simp_tac bool_ss [ignore_bind_def, bind_def, pair_case_thm, sum_case_def, SND] >>
      strip_tac >>
      `?out. unlock_if_nr cx nr view (ee with scopes := prev) = (INL (),out)` by
        simp_tac bool_ss [unlock_success] >>
      `~storage_trace_domain cx st0 out.storage_trace` by
        (qpat_assum `unlock_if_nr _ _ _ _ = _`
           (mp_then Any mp_tac storage_trace_frame_preserves_bad_domain) >>
         simp[storage_trace_frame_optional_locks] >> fs[]) >>
      Cases_on `res`
      >- (rename1 `_ = (INL v,ee)` >>
          `~storage_trace_domain cx st0 (SND (k v out)).storage_trace` by
            (Cases_on `k v out` >> simp[] >>
             qpat_assum `k v out = _`
               (mp_then Any mp_tac storage_trace_frame_preserves_bad_domain) >>
             simp[]) >>
          asm_simp_tac bool_ss [finally_unless_halt_def, finally_def,
            pop_function_def, set_scopes_def, ignore_bind_def, bind_def,
            return_def, pair_case_thm, sum_case_def, FST, SND]) >>
      rename1 `_ = (INR ex,ee)` >> Cases_on `ex` >>
      asm_simp_tac bool_ss [finally_unless_halt_def, finally_def,
        pop_function_def, set_scopes_def, ignore_bind_def, bind_def,
        return_def, raise_def, pair_case_thm, sum_case_def, FST, SND] >>
      gvs[]) >>
  full_simp_tac bool_ss [ignore_bind_def, bind_def, pair_case_thm,
    sum_case_def, SND]
QED

Theorem selected_return_focus_mods:
  let run_body = try (ignore_bind
        (eval_stmts (cx with stk updated_by CONS key) ss) (return NoneV))
        handle_function in
  let source = ignore_bind (lock_if_nr cx nr (is_view_mut mut)) run_body in
  let rest = ignore_bind (lock_if_nr cx nr (is_view_mut mut))
    (bind (finally_unless_halt (finally run_body (pop_function prev))
              (unlock_if_nr cx nr (is_view_mut mut)))
       (\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
                  (\crv. return (Value crv)))) in
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  (!H. (storage_trace_domain cx st0 es.storage_trace ==>
        valid_horizon cx st0 H es.storage_trace) ==>
       ptr_inst_ok (DF H) lo 0 ctx func G tn inst t) /\
  (?marks H leaf leaf_pg leaf_g leaf_tn endpoint.
     (storage_trace_domain cx st0 es.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace) /\
     gas_origin_ptr_focus (DF H,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) marks
       (leaf,leaf_pg,leaf_g,leaf_tn,endpoint) /\
     (gas_bad_storage_at cx st0 source es entered marks \/
      ?err ee. gas_exempt_cert_mods T mods (ctx,callee)
        (ignore_bind source (return ())) (es,entered) marks (err,ee)
        (leaf,endpoint))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 rest
    (es,t,G,tn) Q R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn inst t` by metis_tac[] >>
  `gas_origin_ptr_focus (DF H,lo,explicit,ctx,func,PG) (t,G,tn) marks
       (leaf,leaf_pg,leaf_g,leaf_tn,endpoint)` by
    (irule (cj 3 gas_origin_ptr_focus_rules) >>
     qpat_assum `gas_origin_ptr_focus _ (entered,_,_) _ _` (irule_at Any) >>
     qpat_assum `get_instruction bb _ = SOME inst` (irule_at Any) >>
     qpat_assum `decode_invoke inst = SOME (lbl,arg_ops)` (irule_at Any) >>
     simp[]) >>
  simp_tac bool_ss [gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (drule gas_invoke_entry_readings >> strip_tac >>
          full_simp_tac bool_ss [gas_bad_storage_at_def] >> gen_tac >>
          irule selected_bad_cleanup >>
          simp[storage_trace_frame_bind_all, storage_trace_frame_lifts,
               storage_trace_frame_return]) >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`endpoint`] >> simp[]) >>
  disj2_tac >> disj2_tac >>
  drule selected_exempt_cleanup >>
  disch_then (qspecl_then [`prev`,
    `\rv. bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
               (\crv. return (Value crv))`] strip_assume_tac) >>
  qexistsl_tac [`err`,`out`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`endpoint`] >>
  reverse conj_tac >- (qexists_tac `H` >> simp[]) >>
  irule gas_exempt_cert_mods_invoke >>
  qpat_assum `gas_invoke_entry _ t callee entered` (irule_at Any) >>
  first_assum ACCEPT_TAC
QED
