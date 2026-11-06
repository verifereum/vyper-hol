(* Return metadata for the function selected by an external call. *)
Theory externalReturnSelectedMetadata
Ancestors
  externalReturnAbiMetadata supportedProgram supportedDecls entryStateRel
  vyperInterpreter vyperLookup vyperTyping vyperTypeContract vyperTypeContractStaticMaps e2eDefs

Theorem supported_external_lookup_return:
  !xs tops name mut nr args defaults ret body.
    EVERY (supported_declaration_header tops) xs /\
    lookup_function NONE name External xs =
      SOME (mut,nr,args,defaults,ret,body) ==>
    ret = NoneT \/ supported_place_type tops ret
Proof
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h` >>
  gvs[supported_declaration_header_def, supported_function_return_def,
      lookup_function_def] >>
  BasicProvers.every_case_tac >>
  gvs[lookup_function_def, supported_function_return_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem selected_external_frame_source_abi_metadata:
  !tops am tx name mut nr args defaults ret fbody tv target use_trans keys
   rr pkg_defaults lbl cenv0 pos_args min_cds payable nr' key ut iv fbody' rt
   off st cenv sa c.
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE name External tops =
    SOME (mut,nr,args,defaults,ret,fbody) /\ ret <> NoneT /\
  evaluate_type
    (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)) ret = SOME tv /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,pkg_defaults,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,payable,nr',key,ut,iv,fbody',rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv c /\ source_deployment_rel tops am tx ==>
  abi_enc_plan (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type
          (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)) ret)
     then TupleT [ret] else ret) c.ce_ret_enc_info /\
  vyper_abi_size_bound
    (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type
          (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)) ret)
     then TupleT [ret] else ret) = c.ce_max_return_size
Proof
  rpt gen_tac >> strip_tac >>
  `supported_place_type tops ret` by
    (drule_at (Pos last) supported_external_lookup_return >>
     disch_then (qspec_then `tops` mp_tac) >>
     impl_tac >- fs[supported_program_def, supported_declaration_headers_def] >>
     simp[]) >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    (qpat_x_assum `source_typing_ok _ _ _` mp_tac >>
     rw[source_typing_ok_def, check_contract_def] >>
     drule contract_namespaces_ok_module_type_def_keys >> simp[]) >>
  drule source_deployment_return_tenv >> strip_tac >>
  `evaluate_type (type_env tops) ret = SOME tv` by metis_tac[] >>
  drule_all external_package_frame_source_abi_metadata >> simp[]
QED
