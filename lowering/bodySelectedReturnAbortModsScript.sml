(* Exceptional exits of the selected INVOKE retain the callee's actual run. *)
Theory bodySelectedReturnAbortMods
Ancestors
  gasOutcomeFullMods fragGasOriginPtrInvoke fragGasOriginPtr fragGasFocus
  bodyFullIntCallReturnHalt exprSimDefs
  bodyFullForControl externalCallSelected vyperTypeExternalCallMachine
  vyperStorageFootprint vyperStorageTrace vyperInterpreter vyperState list
Libs
  monadsyntax

Theorem selected_lock_failed_not_halt[local]:
  lock_if_nr cx nr iv es = (INR ex,u) ==> ex <> HaltException
Proof
  disch_then (strip_assume_tac o MATCH_MP
    (REWRITE_RULE [GSYM lock_if_nr_def] call_lock_action_error)) >> simp[]
QED

Theorem selected_observed_unlock[local]:
  storage_trace_frame f /\ lock_if_nr cx nr iv es = (INL (),u) /\
  f u = (res,ee) ==>
  ?out. unlock_if_nr cx nr iv (ee with scopes := prev) = (INL (),out) /\
    (!st0 H. valid_horizon cx st0 H out.storage_trace ==>
             valid_horizon cx st0 H ee.storage_trace) /\
    (!st0. storage_trace_domain cx st0 ee.storage_trace ==>
           storage_trace_domain cx st0 out.storage_trace)
Proof
  strip_tac >> Cases_on `nr /\ ~iv`
  >- (Cases_on `cx.nonreentrant_slot`
      >- (qexists_tac `ee with scopes := prev` >> simp[unlock_if_nr_def, return_def]) >>
      drule_all unlock_if_nr_success_trace >>
      disch_then (qspecl_then [`nr`,`iv`,`ee with scopes := prev`] strip_assume_tac) >>
      qexists_tac `se` >> simp[] >> conj_tac
      >- simp[valid_horizon_def] >>
      gen_tac >> strip_tac >>
      drule_all storage_trace_frame_prefix >> strip_tac >>
      drule_all lock_if_nr_success_trace >> strip_tac >>
      rename1 `cx.nonreentrant_slot = SOME slot` >>
      `MEM (StorageLock slot) ee.storage_trace` by simp[] >>
      `MEM slot (storage_trace_locks ee.storage_trace)` by
        (simp[storage_trace_locks_def, MEM_FLAT, MEM_MAP] >>
         qexists_tac `[slot]` >> simp[] >> qexists_tac `StorageLock slot` >> simp[]) >>
      `slot < dimword (:256)` by
        (qpat_assum `storage_trace_domain _ _ _` mp_tac >>
         pure_rewrite_tac[storage_trace_domain_def, valid_horizon_def,
           storage_observations_ok_def] >> strip_tac >>
         qpat_x_assum `storage_roots_fit _` mp_tac >>
         pure_rewrite_tac[storage_roots_fit_def, EVERY_MEM] >>
         disch_then (qspec_then `StorageLock slot` mp_tac) >> simp[]) >>
      drule_all observed_lock_horizons >>
      disch_then (qspecl_then [`st0`,`cx`] strip_assume_tac) >> gvs[]) >>
  qexists_tac `ee with scopes := prev` >> simp[unlock_if_nr_def, return_def]
QED

Theorem selected_abort_source[local]:
  storage_trace_frame f /\
  (!tail. ignore_bind (lock_if_nr cx nr iv) f (es with gas_obs := gs ++ tail) =
     (INR ex : value + exception,ee with gas_obs := tail)) ==>
  ?out.
    (!tail. (do lock_if_nr cx nr iv;
       rv <- finally_unless_halt (finally f (pop_function prev))
                                   (unlock_if_nr cx nr iv);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv) od) (es with gas_obs := gs ++ tail) =
       (INR ex,out with gas_obs := tail)) /\
    (!st0 H. valid_horizon cx st0 H out.storage_trace ==>
             valid_horizon cx st0 H ee.storage_trace) /\
    (ex = HaltException ==> out = ee with scopes := prev) /\
    (!st0. storage_trace_domain cx st0 ee.storage_trace ==>
           storage_trace_domain cx st0 out.storage_trace)
Proof
  strip_tac >> Cases_on `lock_if_nr cx nr iv es` >>
  drule lock_if_nr_with_gas_obs >> strip_tac >>
  Cases_on `q` >> gvs[ignore_bind_def, bind_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def"]
  >- (rename1 `lock_if_nr cx nr iv es = (INL _,u)` >>
      Cases_on `ex = HaltException`
      >- (qexists_tac `ee with scopes := prev` >>
          gvs[finally_unless_halt_def, finally_def, bind_def, pop_function_def,
              set_scopes_def, return_def, ignore_bind_def, raise_def,
              Excl "unlock_if_nr_def", vyperStateTheory.evaluation_state_fupdcanon]) >>
      `f (u with gas_obs := gs) = (INR ex,ee with gas_obs := [])` by
        (qpat_assum `!tail. f _ = _`
           (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
      `lock_if_nr cx nr iv (es with gas_obs := gs) = (INL (),u with gas_obs := gs)` by
        simp[Excl "lock_if_nr_def"] >>
      qpat_x_assum `lock_if_nr _ _ _ es = _` kall_tac >>
      drule_all selected_observed_unlock >>
      disch_then (qspec_then `prev` strip_assume_tac) >>
      rename1 `unlock_if_nr _ _ _ _ = (INL (),out)` >>
      qexists_tac `out` >> fs[Excl "unlock_if_nr_def"] >> gen_tac >>
      drule unlock_if_nr_with_gas_obs >> disch_then (qspec_then `tail` assume_tac) >>
      Cases_on `ex` >> gvs[finally_unless_halt_def, finally_def, bind_def,
        pop_function_def, set_scopes_def, return_def, ignore_bind_def, raise_def,
        Excl "unlock_if_nr_def", vyperStateTheory.evaluation_state_fupdcanon]) >>
  drule selected_lock_failed_not_halt >> strip_tac >>
  qexists_tac `ee` >> simp[]
QED

Theorem selected_expr_exit_exception[local]:
  expr_exit (INR ex : value + exception) r ==>
  expr_exit (INR ex : eval_result + exception) r /\
  (!ir cs. r <> IntRet ir cs)
Proof
  Cases_on `r` >> Cases_on `ex` >> simp[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >>
  Cases_on `err` >> simp[expr_exit_def]
QED

(* The completed exceptional branch does not bind results or run a suffix. *)
Theorem selected_return_abort_mods:
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  (!tail. (do lock_if_nr cx nr (is_view_mut mut);
             try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
                     return NoneV od) handle_function od)
       (es with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
       (INR ex,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  expr_exit (INR ex : value + exception) r /\
  create_size_exit_ok ctx (INR ex : eval_result + exception) r /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     ptr_inst_ok (DF H) lo 0 ctx func G tn inst t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) marks (r,Gc,tc) /\
     exit_result r /\ halt_exit H cx (ee with gas_obs := [])
       (INR ex : value + exception) r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (do lock_if_nr cx nr (is_view_mut mut);
        rv <- finally_unless_halt
          (finally (try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
                            return NoneV od) handle_function) (pop_function prev))
          (unlock_if_nr cx nr (is_view_mut mut));
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od)
    (es,t,G,tn) Q
    (\H res out gt r. expr_exit res r /\ halt_exit H cx out res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule selected_expr_exit_exception >> strip_tac >>
  drule gas_invoke_entry_readings >> strip_tac >>
  qabbrev_tac `f = try (ignore_bind (eval_stmts (cx with stk updated_by CONS (src,name)) ss)
                         (return NoneV)) handle_function` >>
  `storage_trace_frame f` by
    (simp[Abbr `f`] >> irule storage_trace_frame_try >>
     simp[storage_trace_frame_function_handler] >>
     irule storage_trace_frame_ignore_bind >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  drule_all selected_abort_source >>
  disch_then (qspecl_then [`rtv`,`prev`] strip_assume_tac) >>
  `?obs. ee.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `!tail. ignore_bind _ f _ = _` (qspec_then `[]` assume_tac) >>
     `storage_trace_frame (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) f)` by
       simp[storage_trace_frame_ignore_bind, storage_trace_frame_optional_locks,
            Excl "lock_if_nr_def"] >>
     drule_all storage_trace_frame_prefix >> simp[]) >>
  pure_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INR ex`,`out`,`r`,`G`,`tn`] >>
  conj_tac >- (qpat_x_assum `entered.vs_gas_readings = _` (SUBST_ALL_TAC o SYM) >>
                first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `!st0. storage_trace_domain _ _ _ ==> _` irule >> simp[]) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `!st0 H. valid_horizon _ _ _ _ ==> _` irule >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_x_assum `valid_horizon cx st0 H ee.storage_trace` mp_tac >>
     qpat_assum `ee.storage_trace = _` (once_rewrite_tac o single) >>
     pure_rewrite_tac[valid_horizon_def, storage_observations_ok_append] >>
     strip_tac >> asm_rewrite_tac[]) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn inst t` by simp[] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (t,G,tn) marks (r,G,tn)` by
    (drule_all gas_origin_ptr_invoke_exit >>
     disch_then (qspec_then `PG` ACCEPT_TAC)) >>
  conj_tac >- simp[gas_origin_ptr_path_rules] >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[] >> conj_tac
  >- (Cases_on `ex = HaltException`
      >- (drule halt_exit_scopes_gas_obs >>
          disch_then (qspecl_then [`prev`,`[]`] mp_tac) >>
          gvs[evaluation_state_fupdcanon, halt_exit_def]) >>
      simp[halt_exit_def]) >>
  rpt strip_tac >> gvs[] >> drule_all gas_origin_ptr_edge_halt_fmp >> simp[]
QED
