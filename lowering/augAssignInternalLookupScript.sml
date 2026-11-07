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

Theorem lower_vyper_deploy_unit_internal_lookup:
  !tops rpolicy bytes unit exts ints fb ctor mut nr rr name args dflts ret stmts.
    lower_vyper_deploy_unit tops rpolicy bytes = SOME unit /\
    classify_functions tops = (exts,ints,fb,SOME ctor) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret stmts) tops ==>
    ?fbs.
      lookup_function
        (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) T)
        unit.cu_context.ctx_functions =
      SOME (mk_internal_function
        (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) T)
        fbs
        (FST (SND (source_internal_fn_descriptor tops T
          (mut,nr,rr,name,args,dflts,ret,stmts))))
        (SND (SND (source_internal_fn_descriptor tops T
          (mut,nr,rr,name,args,dflts,ret,stmts))))) /\
      fbs <> [] /\ (HD fbs).bb_label =
        internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) T
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (mut,nr,rr,name,args,dflts,ret,stmts) ints` by
    metis_tac[MEM_classify_internal, pairTheory.FST, pairTheory.SND] >>
  gvs[lower_vyper_deploy_unit_def, bool_case_eq] >>
  rpt (pairarg_tac >> gvs[]) >>
  `MEM (source_internal_fn_descriptor tops T
          (mut,nr,rr,name,args,dflts,ret,stmts))
       (internal_fn_descriptors
          (MAP (set_internal_package_target rpolicy.rpol_target o
                package_internal_fn tops F (assign_nkeys tops 0) T
                  (compute_immutables_len
                    (get_struct_fields (make_struct_fields_map tops)) tops)) ints))`
    by (simp[GSYM MAP_MAP_o,
            internal_fn_descriptors_set_internal_package_target,
            internal_fn_descriptors_MAP_package_internal_fn, MEM_MAP] >>
        qexists_tac `(mut,nr,rr,name,args,dflts,ret,stmts)` >> simp[]) >>
  Cases_on `source_internal_fn_descriptor tops T
              (mut,nr,rr,name,args,dflts,ret,stmts)` >>
  rename1 `_ = (lbl, rest)` >> PairCases_on `rest` >>
  `lbl = internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) T`
    by metis_tac[source_internal_fn_descriptor_label, pairTheory.FST] >>
  gvs[] >> drule_all deploy_internal_package_lookup >> simp[]
QED
