(* Descriptor projection in original source parameter order. *)
Theory entryPackageDescriptorFacts
Ancestors compileVyper compileEnv list pair

Theorem build_positional_args_source_relation:
  LIST_REL (\(name,ty) (name',prim,dyn,sz,info).
    name' = name /\ prim = is_word_type ty /\
    dyn = is_abi_dynamic ce.ce_struct_fields ty /\
    sz = abi_embedded_static_size ce.ce_struct_fields ty /\
    info = type_to_abi_dec_info ce.ce_struct_fields ce ty)
    args (build_positional_args ce args)
Proof
  Induct_on `args` >> simp[build_positional_args_def] >>
  gen_tac >> PairCases_on `h` >> gvs[build_positional_arg_def, build_positional_args_def]
QED

(* SOURCE METADATA LEDGER -- audit only, not additional theorem premises.

   Consumer: entrySourceRegistrationFold.entry_registration_source_endpoint,
   lines 511-527. Index values by ORIGINAL args, never by descriptor equality.
   The intended tuple at index i is (ty,tv,v,at,av), with ty=SND(EL i args),
   v=EL i tx.args, at=vyper_to_abi_type (type_env tops) ty.

   Actual package:
   compileVyper.package_external_fn builds descriptors from cenv_final;
   set_external_package_target changes ONLY ce_target (1268-1274).
   Thus sf is the packaged ce_struct_fields and the conversion environment is
   type_env tops, NOT the bound local scope. Descriptor transport still needs
   type_to_abi_dec_info_layout_cong when changing environment record fields.

   511-518, first LIST_REL:
   - abi_caller_coherent (abiCallerBuiltinInput:180) consumes namespace validity,
     assignable_type and evaluate_type success at build_compile_env. A package
     update/congruence bridge is still needed for this exact ce.
   - source_typing_ok_params_ok (entryStateRel:538) proves params_ok from the
     selected lookup and supported headers; it is LOCAL, not importable.
     params_ok gives distinct names and assignable types, not original-value
     typing. An exported selected-parameter metadata boundary is missing.
   - build_compile_env_type_memory_bytes (structFieldsProps:153) consumes
     distinct type-def keys and evaluate_type success. Package layout transport
     remains required. ctor_coherent_head_size supplies embedded=head size
     AFTER coherence, not before it.
   - The descriptor theorem above supplies name/prim/dyn/embedded-size/info.
     The prim-to-DecPrimWord and dyn-to-is_dynamic clauses still need the
     coherent descriptor boundary (do not assume dyn excludes word by fiat).
   - bind_arguments evaluates types but stores safe_cast RESULTS, not the
     original values (vyperInterpreter:139-147). Its success alone does not
     export value_has_type tv (EL i tx.args) or identity of the cast.
     bind_arguments_scope_well_typed_from_success types the resulting scope.
     safe_cast_well_typed proves identity GIVEN original typing. Original-value
     typing/cast identity must therefore be validated separately.
   - valid_vyper_call/calldata_encodes export vyper_to_abi_list success and
     exact encoding. They do NOT explicitly require has_types or value typing.
     vyper_to_abi_list_EL can project conversion; a typed-conversion producer
     from the actual frozen hypotheses remains unvalidated.
   - type_memory_size tv < dimword needs a quantitative producer (e.g. actual
     compiled allocation charge plus budget), not just evaluated layout equality.

   519-521, second LIST_REL: package_external_fn_vars (entryStateRel:404)
   supplies MemLocs of type_memory_bytes for distinct source names. Combine
   with evaluated-size equality and target-update preservation; no runtime
   endpoint is involved.
   522: params_ok distinct names plus descriptor projection.
   523: has_types is NOT a conjunct of calldata_encodes. A semantic typing
   bridge is missing; vyper_to_abi_total has typing as INPUT, not output.
   source_typing_ok unfolds to checked contract readiness, machine typing and
   call_tx_well_typed. checked_contract_runtime_ready has no provided_args_typed
   conjunct; do not import checked_external_call_inputs_ready as an assumption.
   524-526: valid_vyper_call, equal argument lengths and calldata_encodes give
   selector ++ encoded tuple. Need the fixed four-byte selector and initial
   call-context/calldata observation to establish the window at offset 4.
   527: call_tx_well_typed bounds tx.calldata; transport to machine calldata
   uses initial_venom_state_rel/call_ctx_rel before subtracting selector length.

   Terminal backing/literal sizes are SEPARATE from all the above:
   entryRegistrationFoldBoundary:136-172 records exact consumers.
   registration_singleton_owned_backing can attach compile-only provenance to
   ANY matching allocation at the SAME out, but the fold must retain singleton
   compiler intervals and output ids. register_singleton_alloca_output does not
   export literal operands. alloca_history does not imply abi_alloca_history;
   a same-state literal-size preservation boundary is still missing.
*)
