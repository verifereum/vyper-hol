(* Package metadata at the source/target internal-call boundary. *)
Theory bodyIntCallPackageBoundary
Ancestors
  compileEnv entryStateRel structFieldsProps vyperAST fragGasFocus fragExec
  venomExecSemantics venomState compileVyper supportedProgram supportedNames
  loweringShapeProps list

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
  strip_tac >>
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
