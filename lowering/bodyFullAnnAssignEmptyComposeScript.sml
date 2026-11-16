(* Empty declaration RHS conversion preserves the raw exceptional post. *)
Theory bodyFullAnnAssignEmptyCompose
Ancestors
  gasOutcomeFullCompose gasOutcomeFull memoryLocalRhsProps stmtSimDeclSource
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  gasExemptCert gasSummary venomState
Libs monadsyntax

Theorem annassign_empty_full_rhs_bind:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  env.type_defs = get_tenv cx /\ well_typed_expr env e /\
  is_empty_value_expr e /\ has_length_word typ /\
  type_widens_to env.type_defs (expr_type e) typ /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_expr cx e) (es,s,G,tn) P Rraw /\
  (!H res ee gt r. Rraw H res ee gt r ==>
    ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks tv mid G1 tn1 u.
    (!tail. eval_expr cx e
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL tv,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INL tv) mid G1 tn1 u /\ ~u.vs_halted /\ mid.gas_obs = []) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (new_variable id tyv (default_value tyv)) (mid,u,G1,tn1) Q R) /\
  (!marks exc mid G1 tn1 u.
    (!tail. eval_expr cx e
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INR exc,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INR exc) mid G1 tn1 u /\ ~u.vs_halted /\ mid.gas_obs = []) ==>
    !H. valid_horizon cx st0 H mid.storage_trace ==> Q H (INR exc) mid G1 tn1 u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (AnnAssign id typ e)) (es,s,G,tn) Q R
Proof
  strip_tac >> drule eval_annassign_action >>
  disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
  rewrite_tac[bind_assoc] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >- simp[storage_trace_frame_bind_all, storage_trace_frame_read_result,
          storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[]) >>
  qexists_tac `\H res ee G tn u. P H res ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `res` >> simp[]
  >- (rename1 `INL tv` >>
      `tv = Value (default_value tyv)` by
        (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
         drule_all memory_rhs_empty_eval_destination >> simp[]) >>
      `bind (read_result cx tv) (new_variable id tyv) =
       new_variable id tyv (default_value tyv)` by
        simp[FUN_EQ_THM, read_result_def, bind_def, return_def] >>
      gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

