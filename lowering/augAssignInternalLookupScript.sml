(* Mode-general labels and constructor-present deployment packaging. *)
Theory augAssignInternalLookup
Ancestors
  intCallLookup list rich_list vyperCompiler compileVyper compileEnv
  loweringShapeProps supportedProgram supportedNames venomInst

Theorem augassign_intcall_label:
  !tops cenv mut nr rr name args dflts ret stmts.
    supported_program tops /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret stmts) tops /\
    cenv.ce_func_ids = build_func_ids 0 tops /\
    cenv.ce_func_param_types = build_func_param_types tops ==>
    internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
      (nsid_to_string (NONE,name))
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor =
    internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) cenv.ce_is_ctor
Proof
  `!tops vis mut nr rr name args dflts ret stmts.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_param_types tops name = MAP SND args` by
    (Induct >> simp[] >> Cases >>
     simp[build_func_param_types_def, supported_function_names_def] >>
     rpt strip_tac >> gvs[] >> first_x_assum drule_all >> strip_tac >>
     `MEM name (supported_function_names tops)` by
       (simp[MEM_supported_function_names] >> metis_tac[]) >>
     `name <> s` by (strip_tac >> gvs[]) >> rw[]) >>
  rpt strip_tac >> simp[nsid_to_string_def] >>
  `ALL_DISTINCT (supported_function_names tops)` by
    metis_tac[supported_program_names, supported_declaration_names_unique] >>
  first_x_assum (drule_at (Pos (el 3))) >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem deploy_internal_package_lookup[local]:
  run_deploy_lowering has rpolicy bytes imm args data_size ints cenv stmts
    pay nr key tr entry = SOME unit /\
  MEM (name,buf,ret_count) (internal_fn_descriptors ints) ==>
  ?fbs. lookup_function name unit.cu_context.ctx_functions =
    SOME (mk_internal_function name fbs buf ret_count) /\
    fbs <> [] /\ (HD fbs).bb_label = name
Proof
  simp[run_deploy_lowering_def, extract_context_with_internals_def,
    AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), lowering_context_ok_def, ctx_fn_names_def,
      mk_venom_context_def, install_immutable_reservation_def] >>
  `!ds fs. LIST_REL internal_fn_matches_descriptor ds fs ==>
    MAP FST ds = MAP (\f. f.fn_name) fs` by
    (Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
     rw[internal_fn_matches_descriptor_def] >>
     gvs[internal_fn_matches_descriptor_def]) >>
  drule package_internal_blocks_metadata >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ints))` by gvs[] >>
  drule_all package_internal_blocks_mem >> strip_tac >>
  qexists_tac `fbs` >> simp[] >>
  qspecl_then [`mk_raw_function entry entry_blocks :: functions`,
    `mk_internal_function name fbs buf ret_count`]
    mp_tac lookup_function_distinct_mem >>
  simp[mk_internal_function_metadata]
QED
