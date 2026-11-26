(* Prepend an allocation or other machine prefix that reads no gas. *)
Theory gasOutcomeFullZeroPrefixMods
Ancestors
  gasOutcomeFullMods gasExemptCertMods gasSummary fragGasMode fragGasOrigin
  fragGasOriginPtr fragGasPathMem gasStorage vyperState vyperInterpreter

Theorem gas_exempt_cert_zero_prefix_mem_mods[local]:
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

Theorem origin_ptr_path_zero_prefix[local]:
  gas_origin_ptr_path env start [] (OK s1, G1, tn1) /\
  gas_origin_ptr_path env (s1, G1, tn1) marks out ==>
  gas_origin_ptr_path env start marks out
Proof
  PairCases_on `out` >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem gas_outcome_full_mods_zero_prefix:
  (!H. gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s0, G0, tn0) [] (OK s1, G1, tn1)) /\
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s1, G1, tn1) Q R ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  `gas_path_mem ctx func s0 0 (OK s1)` by
    (qpat_assum `!H. gas_origin_ptr_path _ _ [] _`
       (qspec_then `ARB` assume_tac) >>
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
      qpat_assum `!H. gas_origin_ptr_path _ _ [] _` (qspec_then `H` assume_tac) >>
      drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- gvs[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then assume_tac) >>
      conj_tac
      >- (irule origin_ptr_path_zero_prefix >>
          qexistsl_tac [`G1`, `s1`, `tn1`] >> fs[]) >>
      fs[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac >- (irule gas_exempt_cert_zero_prefix_mem_mods >> qexists_tac `s1` >> simp[]) >>
  qexists_tac `H` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!H. gas_origin_ptr_path _ _ [] _` (qspec_then `H` assume_tac) >>
  drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]
QED
