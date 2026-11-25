(* Checked linked default expressions preserve the source state apart from gas observations. *)
Theory linkedDefaultSourceFrame
Ancestors groupedDefaultHorizon vyperTypeContractStaticMaps vyperTypeContract
  constSubst vyperInterpreter vyperState alist list

Theorem grouped_checked_default_source_frame_mods:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  EVERY (runtime_constant_expr mods) es /\ no_sha256_exprs es /\
  eval_exprs cx es st = (r,ee) ==>
  ee with gas_obs := [] = st with gas_obs := []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac check_contract_runtime_namespaces >>
  mp_tac (Q.INST [`mods` |-> `mods`] (SPEC_ALL grouped_default_eval_source_frame)) >>
  impl_tac >-
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
     `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
       metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
     qpat_x_assum `declared_constant _ _ _ \/ declared_immutable _ _ _`
       (DISJ_CASES_THEN2
          (strip_assume_tac o REWRITE_RULE [declared_constant_def])
          (strip_assume_tac o REWRITE_RULE [declared_immutable_def])) >>
     `ALOOKUP mods src = SOME tls` by
       (irule ALOOKUP_ALL_DISTINCT_MEM >> asm_rewrite_tac[]) >>
     `ts = tls` by fs[] >>
     qpat_x_assum `ts = tls` SUBST_ALL_TAC >>
     metis_tac[find_var_decl_by_name_NONE_Immutable, find_var_decl_by_name_NONE_Constant]) >>
  disch_then (qspecl_then [`cx`,`es`,`st`,`r`,`ee`] mp_tac o CONJUNCT2) >>
  asm_rewrite_tac[]
QED
