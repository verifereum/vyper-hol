(* A successful load_contract records each immutable of the target at its
 * declared type.
 *)
Theory ctorDeployDeadImmTypes
Ancestors
  ctorDeployDeadLoad ctorDeployDefs e2eDeployDefs e2eDefs vyperInterpreter
  vyperTypeContractSoundness vyperTypeInitialState vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeInvariants vyperContext

Theorem checked_singleton_immutable_lookup:
  check_contract F layouts tx.target [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  FLOOKUP art.cta_bare_globals (NONE,name) = SOME ty
Proof
  strip_tac >>
  `bare_globals_complete art.cta_bare_globals
    (initial_evaluation_context [(tx.target,[(NONE,tops)])] layouts tx NONE)` by
    (irule check_contract_bare_globals_complete_initial >> simp[]) >>
  gvs[bare_globals_complete_def, get_module_code_def,
      initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem load_contract_singleton_tenv:
  load_contract NONE gobs am tx [(NONE,tops)] [] = INL (am',rqs) /\
  supported_program tops ==>
  get_tenv (initial_evaluation_context am'.sources am'.layouts tx NONE) =
    type_env tops
Proof
  strip_tac >> drule_all load_contract_sources_layouts >> strip_tac >>
  simp[get_tenv_def, initial_evaluation_context_def,
       type_env_all_modules_def, type_env_def,
       finite_mapTheory.FUNION_FEMPTY_2]
QED

Theorem load_contract_immutables_typed:
  !tops am tx gobs am' rqs pre vis name ty slot post tv v.
    deploy_source_ok tops am tx /\
    load_contract NONE gobs am tx [(NONE, tops)] [] = INL (am', rqs) /\
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
    FLOOKUP (get_source_immutables NONE (account_immutables am' tx.target))
      name = SOME (tv,v) ==>
    evaluate_type (type_env tops) ty = SOME tv
Proof
  rpt strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  qpat_x_assum `tops = _` kall_tac >>
  `supported_program tops` by
    (qpat_x_assum `deploy_source_ok _ _ _` mp_tac >>
     simp[deploy_source_ok_def]) >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    metis_tac[deploy_source_ok_def, deploy_typing_ok_def] >>
  drule_all load_contract_sources_layouts >> strip_tac >>
  `FLOOKUP art.cta_bare_globals (NONE,name) = SOME ty` by
    (irule checked_singleton_immutable_lookup >>
     qexistsl [`am.layouts`, `slot`, `tops`, `tx`, `vis`] >> simp[]) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am'.sources am'.layouts tx NONE)
    am'.immutables` by
    (irule load_contract_establishes_immutables_ready >>
     qexistsl [`am`, `tx`, `[]`, `gobs`, `[(NONE,tops)]`, `NONE`, `rqs`] >>
     gvs[]) >>
  drule_all load_contract_singleton_tenv >> strip_tac >>
  qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
  simp[immutables_ready_def] >> strip_tac >>
  qpat_x_assum `!src id ty tv v. _` mp_tac >>
  disch_then (qspecl_then [`NONE`, `name`, `ty`, `tv`, `v`] mp_tac) >>
  gvs[initial_evaluation_context_def, account_immutables_def,
      vyperStateTheory.empty_immutables_def]
QED
