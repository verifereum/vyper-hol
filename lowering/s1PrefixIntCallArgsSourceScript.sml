(* Source-side facts for composing the two argument stages. *)
Theory s1PrefixIntCallArgsSource
Ancestors
  s1PrefixDefs s1PrefixFrame vyperFiniteStoragePreservation
  vyperStorageFootprint vyperInterpreter vyperState
  vyperStorageTrace bodyFullIntCallArgs exprBodyPreProps

Theorem intcall_args_aggregate_physical_type:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx tenv e ee /\
  compile_expr cenv (expr_type e) e ci = (vv,cm) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_widens_to (get_tenv cx) (expr_type e) dty ==>
  vv_type vv = lowered_value_type cenv e
Proof
  strip_tac >> drule_all body_inv_expr_body_pre_mods >> strip_tac >>
  drule_all intcall_args_aggregate_physical_type_mods >> simp[]
QED

Theorem intcall_args_prefix_stack:
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) (cx with stk updated_by f) st0
    source (es,s,G,tn) =
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn)
Proof
  simp[gas_prefix_full_def, request_site_def, storage_trace_domain_def,
       valid_horizon_def, storage_well_formed_on_stk, storage_observations_ok_stk]
QED

Theorem intcall_args_prefix_source_replay:
  (!tail. source (es with gas_obs := tail) = source' (es' with gas_obs := tail)) /\
  es.storage_trace = es'.storage_trace /\ es.requests = es'.requests ==>
  (gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn) =
   gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source' (es',s,G,tn))
Proof
  strip_tac >> simp[gas_prefix_full_def]
QED

Theorem intcall_args_failed_lock_prefix:
  ~s.vs_halted /\ storage_trace_frame source /\
  lock_if_nr cx nr view es = (INR err,failed) /\
  (!tail. source (es with gas_obs := tail) =
    (INR err,failed with <|scopes := es.scopes; gas_obs := tail|>)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn)
Proof
  strip_tac >>
  `?tr. failed.storage_trace = es.storage_trace ++ tr /\
        EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq) tr` by
    (qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
     Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
     simp[acquire_nonreentrant_lock_def, ignore_bind_def, bind_def,
          record_storage_event_def, get_transient_storage_def,
          update_transient_def, return_def, raise_def, check_not_static_def,
          check_def, assert_def, COND_RATOR] >>
     rpt IF_CASES_TAC >>
     rw[bind_def, return_def, raise_def, update_transient_def, assert_def] >> simp[]) >>
  irule gas_prefix_full_no_outcome >> simp[listTheory.DROP_APPEND1]
QED
