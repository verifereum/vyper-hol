(* A local-memory suffix consumes the full RHS's own source run. *)
Theory bodyFullAssignMemoryCompose
Ancestors
  gasOutcomeFullCompose gasOutcomeFull gasExemptCert gasSummaryCompose gasSummary
  stmtSimAssignSource stmtSimDefs exprSimDefs bodyPtrDefs
  fragGasOriginPtr fragExec gasContext vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState vyperLookup venomState
  stmtSimProps
Libs monadsyntax

Theorem assign_local_memory_full_outcome:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    Q (\H res ee gt r. expr_exit res r) /\
  (!H res ee Gi ti u. Q H res ee Gi ti u ==> ?v. res = INL v) /\
  (!marks v mid Gi ti u.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> Q H (INL v) mid Gi ti u) ==>
    ?ff t Gf tf.
      (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
        (INL (),ff with gas_obs := tail)) /\
      ff.storage_trace = mid.storage_trace /\
      (!H. valid_horizon cx st0 H ff.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (u,Gi,ti) [] (OK t,Gf,tf) /\
        P H (INL ()) (ff with gas_obs := []) Gf tf t)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s,G,tn)
    P (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_target_place cx (NameTarget id)) (\p. write_place cx p v))` by
    simp[Once evaluate_def,bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >>
      RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame (bind (eval_target_place _ _) _)`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_write_place]) >>
  qexists_tac `Q` >> conj_tac >- suspend "continue" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `res` >- fs[expr_exit_def] >>
  simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume assign_local_memory_full_outcome[continue]:
  qx_genl_tac [`marks`,`res`,`mid`,`Gi`,`ti`,`u`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
  `?v. res = INL v` by metis_tac[] >> gvs[] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id mid.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `!tail. eval_target_place cx (NameTarget id) (mid with gas_obs := tail) =
    (INL (MemoryPlace id []),mid with gas_obs := tail)` by
    (gen_tac >> simp[Once evaluate_def,bind_def] >>
     simp[Once evaluate_def,bind_def,ignore_bind_def,get_scopes_def,
       type_check_def,assert_def,return_def,get_place_def]) >>
  qpat_x_assum `!marks v mid Gi ti u. _`
    (qspecl_then [`marks`,`v`,`mid`,`Gi`,`ti`,`u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL ()`,`ff`,`OK t`,`Gf`,`tf`] >>
  simp[bind_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise assign_local_memory_full_outcome
