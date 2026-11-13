(* Return-metadata facts the external frame-return proof needs beyond
   returnMetadataPtr: harvested from the pre-train-16
   frame-ret branch, where they lived in those theories. *)
Theory extRetReturnMetadataPtr
Ancestors
  returnMetadataPtr
  allocLimitsProps sourceEntryCode entryStateRel bodySim retAbiPlanProps structFieldsProps compileVyper compileEnv
  supportedPlaceAssignable supportedDecls supportedProgram e2eDefs
  vyperTypeContractStaticMaps vyperTypeContract
  vyperInterpreter vyperTypeSystem
  list option finite_map entryDecodePlanProps abiEncoderProps
  representationCleanPtr words arithmetic
  supportedGetterProps vyperTypeContractGetter vyperGetter

val _ = Parse.hide "body";

Theorem checked_supported_external_return[local]:
  !decls tops mods art src name mut nr args defaults ret fbody.
  EVERY (supported_declaration_header tops) decls /\
  EVERY (check_toplevel_decl mods art src) decls /\
  lookup_function NONE name External decls =
    SOME (mut, nr, args, defaults, ret, fbody) ==>
  well_formed_type (type_env_all_modules mods) ret /\
  supported_function_return tops External ret
Proof
  rpt gen_tac >> strip_tac >>
  drule lookup_function_External_cases >> strip_tac
  >- (gvs[EVERY_MEM] >>
      qpat_x_assum `!x. MEM x decls ==> check_toplevel_decl _ _ _ x` drule >>
      qpat_x_assum `!x. MEM x decls ==> supported_declaration_header _ x` drule >>
      simp[supported_declaration_header_def, check_toplevel_decl_def] >>
      rpt strip_tac
      >- simp[well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
      drule assignable_type_well_formed >> simp[]) >>
  `supported_declaration_header tops decl` by fs[EVERY_MEM] >>
  `check_toplevel_decl mods art src decl` by fs[EVERY_MEM] >>
  `supported_place_type tops ret` by
    metis_tac[supportedGetterPropsTheory.supported_public_getter_return] >>
  simp[supported_function_return_def] >>
  Cases_on `decl` >>
  gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >~ [`check_toplevel_decl _ _ _ (VariableDecl vis vmut id typ slot)`]
  >- (Cases_on `vis` >> gvs[external_getter_tuple_def] >>
      Cases_on `is_ArrayT typ` >> gvs[getter_def]
      >- (rpt (pairarg_tac >> gvs[]) >>
          `check_value_type (type_env_all_modules mods) (Type typ)` by
            (Cases_on `vmut` >>
             gvs[check_toplevel_decl_def, check_value_type_def]) >>
          metis_tac[check_value_type_ArrayT_type, build_getter_ret_checked,
                    check_value_type_def, assignable_type_well_formed]) >>
      Cases_on `vmut` >>
      gvs[check_toplevel_decl_def, assignable_type_well_formed]) >>
  rename1 `check_toplevel_decl _ _ _ (HashMapDecl vis tr id kt vt slot)` >>
  Cases_on `vis` >> gvs[external_getter_tuple_def, getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `check_value_type (type_env_all_modules mods) vt` by
    gvs[check_toplevel_decl_def] >>
  metis_tac[build_getter_ret_checked, check_value_type_def,
            assignable_type_well_formed]
QED

Theorem source_external_return_contract:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, defaults, ret, fbody) ==>
  well_formed_type (type_env tops) ret /\
  supported_function_return tops External ret
Proof
  strip_tac >> gvs[source_typing_ok_def, supported_program_def,
                  supported_declaration_headers_def] >>
  `EVERY (check_toplevel_decl [(NONE,tops)] art NONE) tops` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule check_contract_toplevel_decl_MEM >>
     disch_then irule >> simp[]) >>
  drule_all checked_supported_external_return >>
  simp[vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_def, FUNION_FEMPTY_2]
QED

Theorem source_external_frame_struct_metadata_acyclic:
  supported_program tops /\ source_typing_ok tops am tx /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next ==>
  acyclic_struct_metadata next.ce_struct_fields
Proof
  strip_tac >> drule_all external_frame_struct_fields >> strip_tac >>
  gvs[source_typing_ok_def] >>
  drule_all typedCopyProducerTheory.supported_checked_struct_metadata_acyclic >>
  simp[]
QED

(* Copy plans expose the exact static size, not a machine-size bound. *)
