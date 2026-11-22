(* Prepare the linked call premises for source checking and dispatch. *)
Theory linkedCallPremises
Ancestors
  e2eModsDefs e2eDefs loweringStateRelDefs vyperContext vyperInterpreter vyperState
  vyperTypeContractSoundness vyperTypeInitialState vyperTypeInvariants
  alist finite_map

Theorem source_typing_ok_runtime_ready_mods:
  source_typing_ok_mods mods exps am tx /\ source_deployment_rel_mods mods exps am tx ==>
  ?art. check_contract F am.layouts tx.target mods = SOME art /\
        checked_contract_runtime_ready art mods am tx /\
        machine_well_typed am /\ call_tx_well_typed tx
Proof
  strip_tac >>
  fs[source_typing_ok_mods_def, global_cells_typed_mods_def] >>
  `ALOOKUP am.sources tx.target = SOME mods /\
   (case ALOOKUP am.exports tx.target of NONE => [] | SOME xs => xs) = exps` by
    (fs[source_deployment_rel_mods_def] >>
     Cases_on `ALOOKUP am.exports tx.target` >> gvs[]) >>
  simp[checked_contract_runtime_ready_def] >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`addr` |-> `tx.target`]
    vyperTypeContractStaticMapsTheory.check_contract_toplevel_vtypes_consistent_initial)) >>
  simp[get_module_code_def, initial_evaluation_context_def] >> strip_tac >>
  drule vyperTypeContractStaticMapsTheory.check_contract_bare_globals_consistent_initial >>
  disch_then (qspecl_then [`tx`, `am.sources`] mp_tac) >>
  simp[get_module_code_def, initial_evaluation_context_def] >> strip_tac >>
  fs[account_immutables_def, empty_immutables_def] >>
  simp[immutables_ready_def, get_tenv_def, get_module_code_def,
       initial_evaluation_context_def] >>
  conj_tac >- metis_tac[optionTheory.IS_SOME_EXISTS] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!src id ty. FLOOKUP art.cta_bare_globals (src,id) = SOME ty ==> ?tv v. _` drule >>
      strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty)` >>
  Cases_on `FLOOKUP art.cta_bare_globals (src,id)`
  >- (qpat_x_assum `!src id ty. _ /\ FLOOKUP art.cta_bare_globals (src,id) = NONE ==> _`
        (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
      simp[] >> strip_tac >> gvs[]) >>
  rename1 `FLOOKUP art.cta_bare_globals (src,id) = SOME bare_ty` >>
  qpat_x_assum `!src id ty. _ ==> ?ts. _ /\ FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ _`
    (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `!src id ty. FLOOKUP art.cta_bare_globals (src,id) = SOME ty ==> ?tv v. _`
    (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
  simp[]
QED

Theorem call_premises_dispatch_invariant_mods:
  !mods exps runtime_bc am tx es f vals.
    (source_typing_ok_mods mods exps am (tx with <| function_name := f; args := vals |>)
       <=> source_typing_ok_mods mods exps am tx) /\
    (call_state_rel_mods mods exps runtime_bc am
       (tx with <| function_name := f; args := vals |>) es
       <=> call_state_rel_mods mods exps runtime_bc am tx es)
Proof
  simp[source_typing_ok_mods_def, call_state_rel_mods_def,
       source_deployment_rel_mods_def, layouts_agree_mods_def,
       call_tx_well_typed_def, frame_tx_rel_def, world_rel_def,
       tx_block_fields_rel_def, value_transfer_ok_def, accounts_after_transfer_def,
       tx_env_ok_def]
QED
