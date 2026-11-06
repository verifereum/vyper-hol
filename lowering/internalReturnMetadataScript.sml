(* Internal-call metadata retained in an external function's frame. *)
Theory internalReturnMetadata
Ancestors
  externalReturnPrefix compileVyper moduleLowering entryStateRel bodySim
  externalNormalizePremises supportedNames vyperInterpreter compileEnv loweringShapeProps
  memoryLocalRhsProps supportedProgram

Theorem external_package_frame_internal_maps:
  set_external_package_target tgt
    (package_external_fn tops ut0 nkm
       (mut, nr0, rr, fname, fargs, dflts, fret, fbody)) =
    (lbl, cenv0, pos_args, min_cds, payable, nr, nkey, ut, iv, fbody', rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv, sa) /\
  same_frame cenv c ==>
  c.ce_func_info =
    build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
  c.ce_func_return_type = build_func_return_type tops /\
  c.ce_struct_fields = make_struct_fields_map tops
Proof
  strip_tac >>
  `cenv0.ce_func_info =
     build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
   cenv0.ce_func_return_type = build_func_return_type tops /\
   cenv0.ce_struct_fields = make_struct_fields_map tops` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def] >>
     strip_tac >> Cases_on `fret = NoneT` >>
     gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
     simp[build_compile_env_ce_func_info, build_compile_env_ce_func_return_type,
          build_compile_env_ce_struct_fields]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST_ALL_TAC >>
  fs[same_frame_def, compile_env_component_equality]
QED

Theorem positive_compute_func_info:
  0 < sz /\ declared <> NoneT /\
  compute_func_info sft declared sz ats = (ret_count,rbs,pvs) ==>
  0 < ret_count \/ 0 < rbs
Proof
  Cases_on `declared` >>
  simp[compute_func_info_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem build_func_info_distinct:
  !tops sft vis mut nr rr name args dflts ret stmts.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n))
        ret (type_mem_bytes sft ret) (MAP SND args)
Proof
  Induct >> simp[] >> Cases_on `h` >>
  simp[build_func_info_def, supported_function_names_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `MEM name (supported_function_names tops)` by
    (simp[MEM_supported_function_names] >> metis_tac[]) >>
  `name <> s` by (strip_tac >> gvs[]) >> rw[]
QED

Theorem supported_internal_call_info:
  supported_program tops /\
  supported_function_decl tops id Internal =
    SOME (mut,nr,rr,args,dflts,ret,stmts) /\
  c.ce_func_info = build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
  c.ce_struct_fields = make_struct_fields_map tops ==>
  c.ce_func_info (nsid_to_string id) =
    compute_func_info (\n. MAP (FST o SND) (get_struct_fields c.ce_struct_fields n))
      ret (type_memory_bytes c ret) (MAP SND args)
Proof
  strip_tac >> drule supported_internal_function_lookup >> strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    metis_tac[supported_program_names, supported_declaration_names_unique] >>
  drule_at (Pos last) build_func_info_distinct >> simp[] >>
  Cases_on `id` >>
  gvs[nsid_to_string_def, GSYM type_mem_bytes_type_memory_bytes]
QED
