(* Runtime frame metadata, independent of the registered argument values. *)
Theory runtimeRegisteredFrameMetadata
Ancestors
  loweringStateRelDefs entryStateRel externalBodyFrame immutableLocationProps immutableRelation
  intCallCallee compileVyper compileEnv e2eDefs supportedProgram vyperInterpreter
  vyperContext vyperState vyperTypeContract finite_map list

Theorem module_location_immutable_frame[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME loc ==>
  FLOOKUP (add_immutable_locations sft tops off
    (add_module_var_locations tops FEMPTY)) key = SOME loc
Proof
  strip_tac >>
  `!vis name ty slot. MEM (VariableDecl vis Immutable name ty slot) tops ==>
    (NONE,name) <> key` by
    (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule_then (qspecl_then
       [`FEMPTY`, `VariableDecl vis Immutable name ty slot`, `name`] mp_tac)
       add_module_var_locations_mem >>
     simp[toplevel_vtype_keys_toplevel_def] >>
     Cases_on `slot` >> simp[add_module_var_locations_def]) >>
  drule add_immutable_locations_lookup_unchanged >> simp[]
QED

Theorem runtime_module_storage_rel[local]:
  supported_declaration_headers tops /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  source_deployment_rel tops am tx /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target /\ cenv.ce_module = NONE /\
  cenv.ce_module_vars = add_immutable_locations
    (get_struct_fields (make_struct_fields_map tops)) tops 0
    (add_module_var_locations tops FEMPTY) ==>
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
  strip_tac >>
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
     >- (irule module_location_immutable_frame >> simp[])
     >- (drule add_immutable_locations_FLOOKUP >> simp[])
     >- (irule module_location_immutable_frame >> simp[])) >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops` by
    (gvs[source_deployment_rel_def, get_module_code_def] >> Cases >> simp[]) >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  first_assum drule_all >> simp[]
QED

Theorem external_registered_frame_metadata:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ ALL_DISTINCT (MAP FST args) /\
  set_external_package_target target
    (package_external_fn tops T nkeys
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce pos 4 start = (cef,registered) ==>
  storage_vars_rel cef (initial_evaluation_context am.sources am.layouts tx NONE) /\
  transient_vars_rel cef (initial_evaluation_context am.sources am.layouts tx NONE) /\
  cef.ce_module = NONE /\ immutable_section_layout cef tops /\
  ~cef.ce_is_ctor /\ immutable_base_zero cef t
Proof
  strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cef = _` SUBST1_TAC >>
  Cases_on `package_external_fn tops T nkeys
    (mut,F,rr,tx.function_name,args,[],ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def] >>
  drule_all package_external_fn_vars >> strip_tac >>
  `~r0.ce_is_ctor /\ r0.ce_imm_alloca = NONE` by
    (`~(build_compile_env tops External mut tx.function_name args ret fbody
         F).ce_is_ctor` by simp[build_compile_env_def, pairTheory.UNCURRY] >>
     gvs[package_external_fn_def, update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def, build_compile_env_imm_alloca] >> gvs[]) >>
  `storage_vars_rel r0 (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel r0 (initial_evaluation_context am.sources am.layouts tx NONE)` by
    (irule runtime_module_storage_rel >> simp[] >>
     qexistsl_tac [`am`, `tops`, `tx`] >>
     simp[initial_evaluation_context_def] >>
     metis_tac[source_typing_ok_vtype_keys_distinct, supported_program_def]) >>
  gvs[storage_vars_rel_def, transient_vars_rel_def, immutable_base_zero_def,
       immutable_section_layout_def] >> rpt strip_tac >>
  drule immutable_locations_origin >> strip_tac
  >- (drule immutable_module_vars_origin >> simp[FLOOKUP_DEF]) >>
  gvs[] >> qexistsl_tac [`pre`, `post`, `vis`, `ty`, `slot`] >> simp[]
QED
