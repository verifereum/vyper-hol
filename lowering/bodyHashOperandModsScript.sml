(* Join the paired operand cut and the two reached hash routes. *)
Theory bodyHashOperandMods
Ancestors
  bodyHashOperandCutMods bodyHashBindShaMods bodyKeccakReachedPostMods
  bodyKeccakFixedEndpointMods bodyKeccakBufferEndpointMods bodyFullPredsMods
  bodyFullPostsMods vyperAST

Theorem hash_route_from_suffixes_mods:
  (b = Keccak256 \/ b = Sha256) /\
  (builtin_args_length_ok b (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann b args) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann b args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qspec_then `PG` strip_assume_tac) hash_operand_cut_mods >>
  qpat_x_assum `args = [_]` SUBST_ALL_TAC >>
  qpat_x_assum `ann = BaseT _` SUBST_ALL_TAC >>
  qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  irule hash_bind_sha_or_reached_keccak_mods >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexistsl_tac [`shadow_func`,`shadow_sa`,`shadow_sb`,`ty`] >> asm_rewrite_tac[])
  >- (qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`sm`,`x`] >> asm_rewrite_tac[] >> BETA_TAC >>
  disch_then SUBST_ALL_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (BETA_RULE keccak_reached_from_endpoints_mods) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`sm`,`x`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          irule keccak_buffer_endpoint_mods >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
          qpat_assum `lower_value _ _ _ _ sa = _` (irule_at Any) >>
          qexistsl_tac [`v`,`tn0`,`gas_explicit marks s0.vs_gas_readings`,`bty`,`G0`] >>
          rpt conj_tac >> first_assum ACCEPT_TAC)
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          qpat_x_assum `v = vyperValue$BytesV _` SUBST_ALL_TAC >>
          irule keccak_fixed_endpoint_mods >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
          qexistsl_tac [`m`,`x`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qexists_tac `ty` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC
QED
