(* Compose the reached field-selection step with the raw child outcome. *)
Theory bodyAttributeGasBindMods
Ancestors
  bodyPtrAttributeObservation gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods haltExitProj exprSimAttribute exprSimDefs ptrDiscipline
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState vyperAST

Theorem attribute_vv_outcome_bind_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx obj) (es,s0,G0,tn0)
    (\H res ee G tn t. ?raw. res = INL raw /\ Child H raw ee G tn t)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!xs raw ee s G tn.
    eval_expr cx obj (es with gas_obs := xs) = (INL raw,ee) /\
    ee.gas_obs = [] /\ ~s.vs_halted /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Child H raw ee G tn s) ==>
    ?raw' t G' tn'.
      select_result cx (expr_type obj) raw (AttrSubscript fld) ee = (INL raw',ee) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
        Field H raw' ee G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx (Attribute ann obj fld)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?raw. res = INL raw /\ Field H raw ee G tn t)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  BETA_TAC >> strip_tac >>
  `eval_expr cx (Attribute ann obj fld) =
   bind (eval_expr cx obj) (\raw. select_result cx (expr_type obj) raw (AttrSubscript fld))` by
    simp[FUN_EQ_THM, eval_expr_attribute] >>
  asm_rewrite_tac[] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (select_result _ _ v _)`]
  >- simp[storage_trace_frame_select] >>
  qexists_tac `\H res ee G tn s. (?raw. res = INL raw /\ Child H raw ee G tn s) /\
                               ee.gas_obs = [] /\ ~s.vs_halted` >>
  BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `res = INL raw` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL raw,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> Child H raw ee G tn s` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` mp_tac >>
     simp[NoAsms]) >>
  qpat_x_assum `!xs raw ee s G tn. _ ==> ?raw' t G' tn'. _`
    (drule_all_then (qx_choosel_then [`raw'`,`t`,`G'`,`tn'`] strip_assume_tac)) >>
  disj1_tac >> qexists_tac `raw` >> simp[] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL raw'`,`t`,`tn'`] >>
  simp[select_attr_gas_update]
QED
