(* Package metadata at the source/target internal-call boundary. *)
Theory bodyIntCallPackageBoundary
Ancestors
  compileEnv entryStateRel structFieldsProps vyperAST fragGasFocus fragExec
  venomExecSemantics venomState compileVyper supportedProgram supportedNames
  loweringShapeProps list intCallLookup vyperCompiler venomInst pair
  unitShapeDefs venomExecProps bodySim ctorDeployShape loweringShapeSource

Theorem internal_return_buffer_memory_size:
  compute_func_info
    (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ret
    (type_mem_bytes (get_struct_fields ce.ce_struct_fields) ret) argtys =
      (0,rbs,pvs) /\
  ret <> NoneT /\ struct_args_unique tops /\
  ce.ce_struct_fields = make_struct_fields_map tops /\
  evaluate_type (type_env tops) ret = SOME tv ==>
  rbs = type_memory_size tv
Proof
  strip_tac >>
  `type_mem_bytes (get_struct_fields ce.ce_struct_fields) ret =
     type_memory_size tv` by
    (rewrite_tac[type_mem_bytes_type_memory_bytes] >>
     irule make_struct_fields_map_memory_size >> metis_tac[]) >>
  Cases_on `ret` >> gvs[compute_func_info_def]
QED

Theorem gas_invoke_entry_no_phi:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name,ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME argv /\
  setup_callee callee argv s = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  phi_prefix_length first.bb_instructions = 0 /\ ~setup.vs_halted ==>
  gas_invoke_entry (ctx,func) s callee (setup with vs_inst_idx := 0)
Proof
  strip_tac >> simp[gas_invoke_entry_def] >>
  qexists_tac `setup` >>
  simp[eval_phis_no_phi]
QED

Theorem supported_function_names_append[local]:
  !pre post. supported_function_names (pre ++ post) =
    supported_function_names pre ++ supported_function_names post
Proof
  Induct >> simp[supported_function_names_def] >>
  Cases_on `h` >> simp[supported_function_names_def]
QED

Theorem internal_call_package_label:
  !tops mut nr rr name args dflts ret ss ce use_trans nkeys imm_len.
  supported_program tops /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  ce.ce_func_ids = build_func_ids 0 tops /\
  ce.ce_func_param_types = build_func_param_types tops ==>
  internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,name)))
    (nsid_to_string (NONE,name))
    (ce.ce_func_param_types (nsid_to_string (NONE,name))) ce.ce_is_ctor =
  FST (package_internal_fn tops use_trans nkeys ce.ce_is_ctor imm_len
         (mut,nr,rr,name,args,dflts,ret,ss))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    metis_tac[supported_program_names, supported_declaration_names_unique] >>
  qpat_x_assum `MEM _ tops` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  rename1 `tops = pre ++ _ :: post` >> gvs[] >>
  `~MEM name (supported_function_names pre)` by
    (gvs[supported_function_names_append, supported_function_names_def,
         ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `EVERY (\top. !v fm' nr' rr' args' dflts' ret' body'.
      top = FunctionDecl v fm' nr' rr' name args' dflts' ret' body' ==>
      v = External) pre` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     fs[MEM_supported_function_names] >> metis_tac[]) >>
  `build_func_param_types
     (pre ++ FunctionDecl Internal mut nr rr name args dflts ret ss :: post)
     name = MAP SND args` by
    (irule build_func_param_types_first_decl >> simp[]) >>
  simp[package_internal_fn_call_label, nsid_to_string_def] >> gvs[]
QED

Theorem run_deploy_lowering_internal_lookup:
  !has rp bytes imm args data_size ints ce stmts pay nr key trans entry unit
   name has_rb rc.
  run_deploy_lowering has rp bytes imm args data_size ints ce stmts pay nr key trans
    entry = SOME unit /\
  MEM (name,has_rb,rc) (internal_fn_descriptors ints) ==>
  ?fbs. lookup_function name unit.cu_context.ctx_functions =
          SOME (mk_internal_function name fbs has_rb rc) /\
        fbs <> [] /\ (HD fbs).bb_label = name
Proof
  rpt gen_tac >>
  simp[run_deploy_lowering_def, extract_context_with_internals_def,
       AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), install_immutable_reservation_def,
      lowering_context_ok_def, ctx_fn_names_def, mk_venom_context_def] >>
  drule package_internal_blocks_metadata >> strip_tac >>
  `MAP FST (internal_fn_descriptors ints) = MAP (\f. f.fn_name) functions` by
    (rewrite_tac[MAP_EQ_LIST_REL] >>
     conj_tac >- metis_tac[LIST_REL_LENGTH] >>
     irule LIST_REL_mono >>
     qexists_tac `internal_fn_matches_descriptor` >> simp[] >>
     simp[FORALL_PROD, internal_fn_matches_descriptor_def]) >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ints))` by gvs[] >>
  drule_all package_internal_blocks_mem >> strip_tac >>
  qexists_tac `fbs` >> simp[] >>
  rename1 `lookup_function name _ = SOME (mk_internal_function name fbs has_rb retcount)` >>
  qspecl_then
    [`mk_raw_function entry entry_blocks :: functions`,
     `mk_internal_function name fbs has_rb retcount`]
    mp_tac lookup_function_distinct_mem >>
  simp[mk_internal_function_metadata]
QED

Theorem lower_vyper_deploy_unit_internal_lookup:
  !tops rp bytes unit mut nr rr name args dflts ret stmts.
    lower_vyper_deploy_unit tops rp bytes = SOME unit /\
    IS_SOME (SND (SND (SND (classify_functions tops)))) /\
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
      fbs <> [] /\
      (HD fbs).bb_label =
        internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) T
Proof
  rpt gen_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  Cases_on `ctor` >> simp[lower_vyper_deploy_unit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  `MEM (mut,nr,rr,name,args,dflts,ret,stmts) ints` by
    metis_tac[MEM_classify_internal, FST, SND] >>
  `MEM (source_internal_fn_descriptor tops T
          (mut,nr,rr,name,args,dflts,ret,stmts))
    (internal_fn_descriptors
      (MAP (set_internal_package_target rp.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) T
          (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops))
        ints))` by
    (simp[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
          internal_fn_descriptors_MAP_package_internal_fn, MEM_MAP] >>
     qexists_tac `(mut,nr,rr,name,args,dflts,ret,stmts)` >> simp[]) >>
  Cases_on `source_internal_fn_descriptor tops T
    (mut,nr,rr,name,args,dflts,ret,stmts)` >>
  rename1 `_ = (lbl,rest)` >> PairCases_on `rest` >>
  `lbl = internal_fn_label (build_func_ids 0 tops name) name (MAP SND args) T`
    by metis_tac[source_internal_fn_descriptor_label, FST] >>
  gvs[] >> drule_all run_deploy_lowering_internal_lookup >> simp[]
QED

(* Raw lowering excludes PHIs, so setup enters the actual head block without
   an additional PHI execution step. No block-label uniqueness is needed for
   FIND at the head itself. *)
Theorem gas_invoke_entry_raw_function:
  !ctx func s bb inst name ops callee argv setup.
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME argv /\
  setup_callee callee argv s = SOME setup /\
  EVERY (\i. raw_opcode_ok i.inst_opcode) (fn_insts callee) ==>
  gas_invoke_entry (ctx,func) s callee (setup with vs_inst_idx := 0)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_invoke_entry_no_phi >>
  simp[] >>
  Cases_on `callee.fn_blocks` >>
  gvs[setup_callee_def] >>
  qexists_tac `h` >> simp[lookup_block_def, FIND_thm] >>
  qpat_x_assum `EVERY _ (fn_insts _)` mp_tac >>
  simp[fn_insts_def, fn_insts_blocks_def] >> strip_tac >>
  Cases_on `h.bb_instructions` >> gvs[phi_prefix_length_def, raw_opcode_ok_def]
QED

Theorem gas_invoke_entry_source_unit:
  !unit func s bb inst name ops callee argv setup.
  o1_source_unit_ok unit /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
  lookup_function name unit.cu_context.ctx_functions = SOME callee /\
  eval_operands ops s = SOME argv /\
  setup_callee callee argv s = SOME setup ==>
  gas_invoke_entry (unit.cu_context,func) s callee
    (setup with vs_inst_idx := 0)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_invoke_entry_raw_function >> simp[] >>
  qpat_x_assum `o1_source_unit_ok _` mp_tac >>
  simp[o1_source_unit_ok_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `lookup_function _ _ = _` mp_tac >>
  simp[lookup_function_def] >> strip_tac >>
  drule FIND_MEM >> metis_tac[]
QED

Theorem body_inv_gas_invoke_entry:
  !tops ctx cenv cx func s bb inst name ops callee argv setup.
  body_inv tops ctx cenv cx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME argv /\
  setup_callee callee argv s = SOME setup ==>
  gas_invoke_entry (ctx,func) s callee (setup with vs_inst_idx := 0)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `body_inv _ _ _ _` mp_tac >>
  simp[body_inv_def] >> strip_tac >> gvs[] >>
  `o1_source_unit_ok unit` by
    (Cases_on `cx.in_deploy` >> gvs[]
     >- (irule lower_vyper_deploy_unit_source_unit_ok >> metis_tac[]) >>
     drule lower_vyper_runtime_unit_source_unit_ok_shape >>
     disch_then irule >> conj_tac
     >- (irule supported_names_internal_names_distinct >>
         metis_tac[supported_program_names, supported_declaration_names_unique]) >>
     metis_tac[supported_program_runtime_bodies_shape_ok]) >>
  irule gas_invoke_entry_source_unit >> simp[]
QED
