(* A source prefix that only changes observations shares its zero-reading
   target prefix with the suffix's joint witness. *)
Theory gasOutcomeFullSourcePrefix
Ancestors
  gasOutcomeFull gasOutcomeFullCompose gasOutcomeFullGuarded
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathMem
  gasStorage gasSummary gasExemptCert vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomState list

Theorem gas_outcome_full_source_prefix:
  (!gs. source (es with gas_obs := gs) = source' (mid with gas_obs := gs)) /\
  mid.storage_trace = es.storage_trace ++ obs /\
  storage_trace_domain cx st0 mid.storage_trace /\
  storage_trace_frame source' /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s0,G0,tn0) [] (OK s1,G1,tn1)) /\
  (!marks err ee leaf fin.
     gas_exempt_cert T tops (ctx,func) (ignore_bind source' (return ()))
       (mid,s1) marks (err,ee) (leaf,fin) ==>
     gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
       (es,s0) marks (err,ee) (leaf,fin)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source'
    (mid,s1,G1,tn1) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  `gas_path_mem ctx func s0 0 (OK s1)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (fs[gas_bad_storage_at_def] >> metis_tac[]) >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
      conj_tac >- metis_tac[valid_horizon_append] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- (gen_tac >> metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `H` >> strip_tac >>
      `valid_horizon cx st0 H mid.storage_trace` by
        (qpat_assum `!tail. source' _ = _`
           (qspec_then `[]` assume_tac) >>
         drule_all storage_trace_frame_prefix >> strip_tac >>
         gvs[] >> metis_tac[valid_horizon_append]) >>
      res_tac >> simp[] >>
      qspecl_then [`(DF H,lo,explicit,ctx,func,PG)`, `(s0,G0,tn0)`,
                    `[]`, `(OK s1,G1,tn1)`] mp_tac gas_origin_ptr_path_append >>
      impl_tac >- first_assum ACCEPT_TAC >>
      simp[] >> disch_then drule >> simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `H` >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
  conj_tac >- metis_tac[valid_horizon_append] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]
QED
