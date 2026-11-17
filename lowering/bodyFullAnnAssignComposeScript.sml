(* AnnAssign source sequencing retains the complete joint exit predicate. *)
Theory bodyFullAnnAssignCompose
Ancestors
  gasOutcomeFullCompose stmtSimDeclSource gasOutcomeFull
  fragGasOriginPtr gasExemptCert gasStorage gasSummary gasSummaryCompose
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  stmtSimDefs venomState list
Libs monadsyntax

Theorem annassign_full_outcome:
  !DF lo explicit ctx func PG tops cx st0 id typ tyv e es s G tn Q R P S lctx.
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es, s, G, tn) Q R /\
    (!H res ee G1 tn1 t. Q H res ee G1 tn1 t ==> ?v. res = INL v) /\
    (!H res ee gt r. R H res ee gt r ==>
       ?exc. res = INR exc /\ S H (INR exc) ee gt r) /\
    (!marks v mid G1 tn1 t.
       (!tail. bind (eval_expr cx e) (read_result cx)
           (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
           (INL v, mid with gas_obs := tail)) /\
       storage_trace_domain cx st0 mid.storage_trace /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
            Q H (INL v) mid G1 tn1 t) ==>
       ?ff u G2 tn2.
         (!tail. new_variable id tyv v (mid with gas_obs := tail) =
                 (INL (), ff with gas_obs := tail)) /\
         ff.storage_trace = mid.storage_trace /\
         (!H. valid_horizon cx st0 H ff.storage_trace ==>
            gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
              (t, G1, tn1) [] (OK u, G2, tn2) /\
            P H (INL ()) (ff with gas_obs := []) G2 tn2 u)) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (eval_stmt cx (AnnAssign id typ e)) (es, s, G, tn) P S
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[storage_trace_frame_new_variable] >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  conj_tac
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result] >>
  qexists_tac `Q` >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `?v. res = INL v` by metis_tac[storage_trace_domain_def] >> gvs[] >>
      qpat_x_assum `!marks v mid G1 tn1 t. _` drule_all >> strip_tac >>
      irule gas_outcome_full_intro >>
      qexistsl_tac [`G2`, `ff`, `[]`, `OK u`, `INL ()`, `tn2`] >>
      simp[] >> metis_tac[]) >>
  irule gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
