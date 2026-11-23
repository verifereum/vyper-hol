Theory whitelistLinkedConstProps
Ancestors
  alist list pair finite_map constSubst supportedExprs vyperTypeContract
  vyperTypeContractContext whitelistLinkedConstMain whitelistLinkedConstImport
  whitelistLinkedConstPlace whitelistLinkedConstFragment
  whitelistLinkedBodyTypes whitelistLinkedBodyEnv

Theorem check_contract_linked_supported_consts:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops ==>
  EVERY (supported_pure_expr tops o SND) (module_consts_env tops [])
Proof
  strip_tac >> simp[EVERY_MEM, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM (id,r) (module_consts_env tops [])` >>
  drule_all linked_checked_body_type_facts >>
  disch_then (strip_assume_tac o REWRITE_RULE [linked_body_type_facts_def]) >>
  `!b. constant_expr mods b /\ const_local_refs b = [] ==>
       (qualified_place_root b \/ supported_place_info tops b = ValPT (expr_type b)) /\
       (supported_pure_expr tops b ==> supported_place_expr tops b)` by
    MATCH_ACCEPT_TAC closed_const_place_facts >>
  `constant_expr mods r /\ const_local_refs r = [] /\
   well_typed_expr (artifact_env art mods src) r /\
   (src <> NONE ==> imported_expr_refs_ok r)` by
    (Cases_on `src` >> gvs[]
     >- (drule_all main_const_replacement_facts >> simp[]) >>
     drule_all imported_const_replacement_facts >> simp[]) >>
  `supported_pure_expr tops r /\ checker_agg_ok tops (expr_type r)` by
    (irule closed_typed_const_supported >> conj_tac >- simp[] >>
     map_every qexists_tac [`addr`, `art`, `layouts`, `mods`, `src`] >>
     asm_rewrite_tac [] >> rpt strip_tac >> res_tac >>
     Cases_on `src` >> gvs[]) >>
  simp[]
QED
