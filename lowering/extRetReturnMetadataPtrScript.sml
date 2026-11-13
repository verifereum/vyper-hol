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
  Induct >> simp[lookup_function_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h` >>
  gvs[supported_declaration_header_def, check_toplevel_decl_def,
      lookup_function_def]
  >~ [`if s = name /\ f = External then _ else _`]
  >- (Cases_on `s = name /\ f = External` >> gvs[]
      >~ [`well_formed_type _ NoneT`]
      >- simp[well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >~ [`lookup_function _ _ _ (VariableDecl vis _ _ _ _ :: _)`]
  >- (Cases_on `vis` >> gvs[lookup_function_def] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >~ [`lookup_function _ _ _ (HashMapDecl vis _ _ _ _ _ :: _)`]
  >- (Cases_on `vis` >> gvs[lookup_function_def] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  first_x_assum irule >> simp[] >> metis_tac[]
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
