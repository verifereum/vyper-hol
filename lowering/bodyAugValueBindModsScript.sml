(* The reached AugAssign value and its continuation use the same source
   and machine endpoints. *)
Theory bodyAugValueBindMods
Ancestors
  augAssignFullSourceReplay augAssignFullRhsSaved
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  vyperStorageTrace vyperExprNoControl vyperState exprSimDefs stmtSimDefs
  haltExitProj bodyPtrDefs gasContext vyperStorageFootprint

Theorem augassign_reached_rhs_admissible_mods:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL p,mid with gas_obs := tail)) /\
  read_place cx p mid = (INL cur,mid) /\
  place_type_value cx p mid = (INL ptv,mid) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid
Proof
  strip_tac >>
  `read_result cx (PlaceR p) mid = (INL cur,mid)` by simp[read_result_def] >>
  drule exprSimMemorySourceTheory.read_result_gas_obs >>
  pure_rewrite_tac[read_result_def] >> strip_tac >>
  drule_then assume_tac exprSimIfExpWidenedAdapterTheory.place_type_value_gas_obs >>
  rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR exc` >>
  `no_control_exc exc` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def, AllCaseEqs()] >>
     strip_tac >> gvs[]
     >- metis_tac[read_result_no_control] >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR exc)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ee`,`prefix ++ gs`] >> rewrite_tac[augassign_source_bind] >>
     ntac 4 (once_rewrite_tac[bind_def] >> simp[])) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem augassign_typed_value_bind_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (mid,u,Gu,tu)
    (\H res ee G tn q. ?v. res = INL v /\ P H v ee G tn q)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!marks v ee G tn q.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
        (INL v,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~q.vs_halted /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee G tn q) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (bind (lift_sum (evaluate_binop bound ptv bop cur v)) (write_place cx p))
      (ee,q,G,tn) Q
      (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
          allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) (\v.
      bind (lift_sum (evaluate_binop bound ptv bop cur v)) (write_place cx p)))
    (mid,u,Gu,tu) Q
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
        allocas_below_fmp s))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx e) (read_result cx)) _ ChildQ ChildR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) (read_result _))`]
  >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`!v. storage_trace_frame (bind (lift_sum (evaluate_binop _ _ _ _ v)) (write_place _ _))`]
  >- simp[storage_trace_frame_bind, storage_trace_frame_lifts, storage_trace_frame_write_place] >>
  qexists `\H res ee G tn q. ChildQ H res ee G tn q /\ ee.gas_obs = [] /\ ~q.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `ChildR`, Excl "AND_IMP_INTRO"] >>
      rpt gen_tac >> Cases_on `res` >- simp[] >>
      strip_tac >> rename1 `expr_exit (INR exc) r` >>
      qexists `exc` >> conj_tac >- simp[] >>
      drule_all augassign_expr_exit_to_stmt_exit >> disch_then irule) >>
  suspend "rhs_reached"
QED

Resume augassign_typed_value_bind_mods[rhs_reached]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`q`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ChildQ (storage_trace_horizon ee.storage_trace) res ee G tn q /\
    ee.gas_obs = [] /\ ~q.vs_halted` by (first_x_assum drule >> simp[]) >>
  qpat_x_assum `ChildQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
  simp[Abbr `ChildQ`, NoAsms] >>
  disch_then (qx_choose_then `v` (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  disj1_tac >> qexists `v` >> simp[] >>
  first_x_assum irule >> conj_tac
  >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED

Finalise augassign_typed_value_bind_mods
