(* Immutable-aware body-state boundary at a fixed actual entry endpoint.
   The analogous entryStateRel helpers are local to that theory. *)
Theory entryRuntimeStateBoundary
Ancestors
  entryStateRel entryDecoderStateFrame immutableLocationProps loweringStateRelDefs
  immutableSectionRel immutableRelation vyperLoweringCorrect compileVyper
  vyperInterpreter vyperState vyperContext vyperAST vyperValue
  venomState vyperTypeContract vyperTypeContractStaticMaps
  vyperTypeContractContext moduleLowering compileEnv fragExec e2eDefs

Theorem runtime_module_lookup_immutable_frame[local]:
  !tops sft off key loc.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME loc ==>
    FLOOKUP (add_immutable_locations sft tops off
      (add_module_var_locations tops FEMPTY)) key = SOME loc
Proof
  rpt gen_tac >> strip_tac >>
  `!vis name ty slot.
     MEM (VariableDecl vis Immutable name ty slot) tops ==>
     (NONE, name) <> key` by
    (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule_then (qspecl_then
       [`FEMPTY`, `VariableDecl vis Immutable name ty slot`, `name`] mp_tac)
       add_module_var_locations_mem >>
     simp[toplevel_vtype_keys_toplevel_def] >>
     Cases_on `slot` >> simp[add_module_var_locations_def]) >>
  drule add_immutable_locations_lookup_unchanged >> simp[]
QED

Theorem runtime_entry_storage_vars_rel:
  !tops am tx cenv cx.
    supported_declaration_headers tops /\
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    source_deployment_rel tops am tx /\
    cx.sources = am.sources /\ cx.layouts = am.layouts /\
    cx.txn.target = tx.target /\ cenv.ce_module = NONE /\
    (!name. FLOOKUP cenv.ce_module_vars (NONE, name) =
      FLOOKUP (add_immutable_locations
        (get_struct_fields (make_struct_fields_map tops)) tops 0
        (add_module_var_locations tops FEMPTY)) ((NONE, name))) ==>
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
  rpt gen_tac >> strip_tac >>
  `storage_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx /\
   transient_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx` by
    (irule entry_storage_vars_rel >> simp[] >>
     qexistsl_tac [`am`, `tops`, `tx`] >> simp[]) >>
  `!key slot.
    (FLOOKUP (add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY)) key = SOME (StorageLoc slot) <=>
     FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (StorageLoc slot)) /\
    (FLOOKUP (add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY)) key = SOME (TransientLoc slot) <=>
     FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (TransientLoc slot))` by
    (rpt gen_tac >> conj_tac >> eq_tac >> strip_tac
     >- (drule add_immutable_locations_FLOOKUP >> simp[])
     >- (irule runtime_module_lookup_immutable_frame >> simp[])
     >- (drule add_immutable_locations_FLOOKUP >> simp[])
     >- (irule runtime_module_lookup_immutable_frame >> simp[])) >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops` by
    (gvs[source_deployment_rel_def, get_module_code_def] >> Cases >> simp[]) >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  first_assum drule_all >> simp[]
QED

Theorem runtime_entry_state_rel:
  !tops func cenv cx am tx vs out mut env es.
    initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
    send_call_value mut cx
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INL (), es) /\
    entry_decoder_obs vs out /\
    local_ptrs_rel func cenv [env] out /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    cenv.ce_module = NONE /\ ~cenv.ce_is_ctor /\
    immutable_section_layout cenv tops ==>
    state_rel func cenv cx es out
Proof
  rpt gen_tac >> strip_tac >>
  fs[entry_decoder_obs_def] >>
  drule send_call_value_accounts >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es out` by
    (gvs[] >> irule immutables_section_rel_runtime_fallback >>
     gvs[initial_venom_state_rel_def, initial_state_def, account_immutables_def] >>
     qexists_tac `tops` >> simp[]) >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, state_rel_def,
      initial_state_def] >>
  `out.vs_call_ctx.cc_address = cx.txn.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, accounts_rel_def]
QED
