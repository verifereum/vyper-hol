(* Parameter admissibility for an arbitrary externally selected name. *)
Theory entryExternalParameterAdmissibility
Ancestors
  entryStateRel e2eDefs supportedProgram supportedDecls
  vyperTypeContract vyperTypeContractContext vyperTypeContractGetter
  vyperTypeSystem vyperContext vyperState list finite_map

Theorem source_typing_ok_external_params_ok:
  !tops am tx name mut nr args ret fbody.
    supported_declaration_headers tops /\ source_typing_ok tops am tx /\
    lookup_function NONE name External tops =
      SOME (mut,nr,args,[],ret,fbody) ==>
    params_ok (type_env tops) args
Proof
  rpt strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (fs[source_typing_ok_def] >>
      drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
      drule check_contract_runtime_function_body_MEM >>
      disch_then (qspecl_then [`External`, `tops`, `NONE`, `ret`, `raw`, `nr`,
        `mut`, `name`, `[]`, `fbody`, `args`] mp_tac) >>
      simp[check_function_body_def, type_env_all_modules_def, type_env_def,
           FUNION_FEMPTY_2]) >>
  fs[source_typing_ok_def] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all checked_public_getter_params_ok >>
  simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED
