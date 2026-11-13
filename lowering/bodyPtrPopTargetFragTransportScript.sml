(* Source-only get_place transport: no target instruction or ghost changes. *)
Theory bodyPtrPopTargetFragTransport
Ancestors
  fragGasPathPtr targetPlaceSimCases targetPlaceSimDefs exprSimDefs
  gasContext gasSummary gasExemptCert stmtSimProps vyperInterpreter vyperState
  gasStorage vyperStorageTrace

Theorem eval_target_place_as_bind:
  eval_target_place cx bt = bind (eval_base_place cx bt) get_place
Proof
  simp[Once evaluate_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem get_place_base_admissible:
  gas_admissible (bind source get_place) target_place_res_ok es ==>
  gas_admissible source target_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  Cases_on `res` >> simp[bind_def, target_res_ok_def] >>
  simp[target_place_res_ok_def]
QED

Theorem gas_outcome_ptr_get_place:
  gas_admissible (bind source get_place) target_place_res_ok es /\
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0)
    (\H res ee G tn t. ?pv. res = INL pv /\ P H pv ee G tn t)
    (\H res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0 (bind source get_place)
    (es,s0,G0,tn0)
    (\H res ee G tn t. ?p. res = INL p /\ P H (PlaceR p) ee G tn t)
    (\H res ee gt r. expr_exit res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_get_place])
  >- (disj2_tac >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_ptr_at_def] >>
      disch_then (qx_choosel_then [`res`, `fin`, `G`, `tn`, `rr`]
        strip_assume_tac) >>
      Cases_on `res`
      >- (rename1 `INL pv` >>
          `?p. pv = PlaceR p` by (
            qpat_x_assum `gas_admissible _ _ _` mp_tac >>
            rewrite_tac[gas_admissible_def] >>
            disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings`
              mp_tac) >>
            qpat_x_assum `!tail. source _ = _` (qspec_then `[]` mp_tac) >>
            simp[bind_def] >> strip_tac >>
            Cases_on `pv` >>
            simp[get_place_def, raise_def, target_place_res_ok_def]) >>
          gvs[] >> qexistsl_tac [`INL p`, `fin`, `G`, `tn`, `rr`] >>
          simp[bind_def, get_place_def, return_def] >>
          rpt strip_tac >> first_x_assum drule >> strip_tac >>
          gvs[expr_exit_def]) >>
      rename1 `INR exc` >>
      qexistsl_tac [`INR exc`, `fin`, `G`, `tn`, `rr`] >>
      simp[bind_def] >> rpt strip_tac >> first_x_assum drule >>
      strip_tac >> gvs[] >> metis_tac[expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_result)
QED
