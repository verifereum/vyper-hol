(* A zero-reading load or operator interval need only run on valid horizons. *)
Theory bodyAugGuardedPrefixMods
Ancestors
  gasOutcomeFullMods gasOutcomeFull gasExemptCertMods gasSummary fragGasMode
  fragGasOrigin fragGasOriginPtr fragGasPathMem gasStorage vyperStorageTrace
  vyperStorageFootprint vyperState vyperInterpreter

Theorem aug_exempt_zero_prefix[local]:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_exempt_cert_mods T mods (ctx,func) source (es,s1) marks (err,ee)
    (leaf,terminal) ==>
  gas_exempt_cert_mods T mods (ctx,func) source (es,s0) marks (err,ee)
    (leaf,terminal)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s0) [] (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def, return_def, gas_marked_path_def] >>
  drule gas_exempt_cert_start_gas_obs_mods >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_mods_bind_unit >>
  disch_then (qspecl_then [`mods`, `\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

Theorem aug_origin_ptr_zero_prefix[local]:
  gas_origin_ptr_path env start [] (OK s1, G1, tn1) /\
  gas_origin_ptr_path env (s1, G1, tn1) marks out ==>
  gas_origin_ptr_path env start marks out
Proof
  PairCases_on `out` >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem aug_trace_prefix[local]:
  storage_trace_frame source /\ source (es with gas_obs := g) = (res, ee) ==>
  ?xs. ee.storage_trace = es.storage_trace ++ xs
Proof
  strip_tac >>
  qpat_x_assum `storage_trace_frame _`
    (mp_tac o Q.SPECL [`es with gas_obs := g`, `es.storage_trace`] o
     REWRITE_RULE [storage_trace_frame_def]) >>
  Cases_on `source ((es with gas_obs := g) with storage_trace := [])` >>
  simp[evaluation_state_component_equality] >> strip_tac >> gvs[]
QED

Theorem augassign_zero_prefix_guarded_mods:
  storage_trace_frame source /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s0, G0, tn0) [] (OK s1, G1, tn1)) /\
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s1, G1, tn1) Q R ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[storage_trace_domain_def] >>
  `gas_path_mem ctx func s0 0 (OK s1)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
       (drule_then assume_tac) >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- gvs[gas_bad_storage_at_def] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_x_assum `storage_trace_domain _ _ _ ==> _` irule >>
         first_assum ACCEPT_TAC) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
        (drule_then assume_tac) >>
      drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- gvs[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `H` >> strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
         drule_all aug_trace_prefix >> strip_tac >>
         gvs[] >> drule valid_horizon_append >> simp[]) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
        (drule_then assume_tac) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
        (drule_then (CONJUNCTS_THEN assume_tac)) >>
      conj_tac
      >- (irule aug_origin_ptr_zero_prefix >>
          qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[]) >>
      simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac >- (irule aug_exempt_zero_prefix >> qexists_tac `s1` >> simp[]) >>
  qexists_tac `H` >> conj_tac >- first_assum ACCEPT_TAC >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_x_assum `storage_trace_domain _ _ _ ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
    (drule_then assume_tac) >>
  drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]
QED
