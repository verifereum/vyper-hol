(* The linked checker supplies parameter types before ABI registration. *)
Theory linkedExternalParameterTypes
Ancestors
  defaultDispatchModsGetter e2eModsDefs vyperTypeContractContext
  vyperTypeContractGetter vyperTypeContract alist list

Theorem checked_external_parameter_types_mods:
  source_typing_ok_mods mods exps am tx /\
  ALOOKUP mods (ALOOKUP exps name) = SOME tops /\ MEM top tops /\
  (top = FunctionDecl External mut nr rr name args dflts ret fbody \/
   public_getter_src (ALOOKUP exps name) top =
     SOME (mut,nr,rr,name,args,dflts,ret,fbody)) ==>
  params_ok (type_env_all_modules mods) args
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `source_typing_ok_mods _ _ _ _`
    (qx_choose_then `art` strip_assume_tac o REWRITE_RULE [source_typing_ok_mods_def]) >>
  `module_allocated am.layouts tx.target (ALOOKUP exps name) tops` by
    (Cases_on `ALOOKUP exps name`
     >- (irule check_contract_main_module_allocated >>
         goal_assum (drule_at Any) >> fs[]) >>
     rename1 `ALOOKUP exps name = SOME sid` >>
     drule_then assume_tac ALOOKUP_MEM >>
     qpat_x_assum `exports_ok _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC [exports_ok_def] >>
     disch_then (CONJUNCTS_THEN2 mp_tac (K ALL_TAC)) >>
     simp[EVERY_MEM] >>
     disch_then (qspec_then `(name,sid)` mp_tac) >> simp[]) >>
  qpat_x_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _ \/ _`
    (DISJ_CASES_THEN assume_tac)
  >- (qpat_x_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _` SUBST_ALL_TAC >>
      drule_all (SIMP_RULE (srw_ss()) []
        (Q.INST [`vis` |-> `External`] check_contract_runtime_function_body_MEM)) >>
      simp[check_function_body_def]) >>
  qpat_x_assum `public_getter_src _ _ = _`
    (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]) >>
  drule_all_then ACCEPT_TAC checked_public_getter_params_ok
QED
