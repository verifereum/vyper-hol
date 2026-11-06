(* Complete-entry probes for the actual padding witness. *)
Theory bodyPtrTypeBuiltinsPaddingFrame
Ancestors
  bodyPtrTypeBuiltinsPaddingWitness fcgDefs relation exprLoweringProps
  venomInst venomWf list words compileEnv finite_map compileVyper vyperCompiler venomCompilerTypes

Theorem padding_actual_no_calls:
  ~fn_directly_calls padding_runtime.cu_context padding_runtime_function.fn_name g
Proof
  simp[fn_directly_calls_def, padding_runtime_function_member] >>
  simp[padding_runtime_function_equation, fn_insts_def, mk_raw_function_def] >>
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[dimword_def]
QED

Theorem padding_actual_no_reach:
  ~TC (fn_directly_calls padding_runtime.cu_context)
    padding_runtime_function.fn_name g
Proof
  simp[Once TC_CASES1, padding_actual_no_calls]
QED

Theorem padding_actual_stmt_state_rel:
  stmt_state_rel padding_runtime.cu_context padding_runtime_function
    padding_actual_cenv padding_actual_context padding_source padding_actual_machine
Proof
  simp[stmt_state_rel_def, padding_actual_machine_state_rel,
       alloca_room_def, fmp_room_def, padding_actual_no_reach,
       padding_runtime_function_member] >>
  simp[padding_runtime_function_equation] >> EVAL_TAC >> simp[dimword_def] >>
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[dimword_def]
QED

Theorem padding_actual_context_well_typed:
  context_well_typed padding_actual_context
Proof
  EVAL_TAC >> simp[]
QED

Theorem padding_actual_functions_well_typed:
  functions_well_typed padding_actual_context
Proof
  EVAL_TAC >> simp[] >>
  simp[vyperInterpreterTheory.lookup_function_def,
       vyperStateTheory.lookup_flag_def,
       vyperStateTheory.find_var_decl_by_name_def] >>
  rpt gen_tac >> strip_tac >>
  qexists_tac `padding_env with
    <| fn_sigs := fn_sigs; bare_globals := bare_globals;
       toplevel_vtypes := toplevel_vtypes; flag_members := flag_members |>` >>
  EVAL_TAC >> simp[]
QED

Theorem padding_actual_cenv_static:
  padding_actual_cenv.ce_imm_alloca = NONE /\
  padding_actual_cenv.ce_return_buf = NONE /\
  ~padding_actual_cenv.ce_is_ctor
Proof
  EVAL_TAC
QED

Theorem padding_actual_reserved_names:
  not_fresh_at padding_actual_start "%5" /\
  not_fresh_at padding_actual_start "%6"
Proof
  `"%5" = STRING #"%" (toString (5:num))` by EVAL_TAC >>
  `"%6" = STRING #"%" (toString (6:num))` by EVAL_TAC >>
  asm_rewrite_tac[] >>
  simp[not_fresh_at_def, padding_actual_start_def,
       ASCIInumbersTheory.toString_inj]
QED

Theorem padding_actual_entry_static:
  fn_inst_ids_distinct padding_runtime_function /\
  local_ptrs_reserved padding_actual_cenv padding_actual_start /\
  ~ctx_has_dalloca padding_runtime.cu_context /\
  ~padding_actual_cenv.ce_is_ctor /\
  (!x sz. padding_actual_cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at padding_actual_start x) /\
  (!x sz. padding_actual_cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at padding_actual_start x) /\
  ~padding_actual_machine.vs_halted /\
  padding_actual_machine.vs_current_bb = padding_actual_start.cs_current_bb /\
  padding_actual_machine.vs_inst_idx = LENGTH padding_actual_start.cs_current_insts
Proof
  rpt conj_tac >>
  simp[local_ptrs_reserved_def, padding_actual_cenv_projections,
       padding_actual_cenv_static, padding_actual_reserved_names, FLOOKUP_UPDATE] >>
  simp[padding_actual_start_def, padding_runtime_function_equation,
       fn_inst_ids_distinct_def, mk_raw_function_def, fn_insts_def,
       initial_compile_state_def] >>
  EVAL_TAC >> simp[dimword_def] >> EVAL_TAC >> simp[]
QED

Theorem padding_actual_body_pre:
  expr_body_pre padding_actual_cenv padding_actual_context
    padding_actual_env padding_expr padding_source
Proof
  irule padding_actual_convert_body_pre >>
  simp[padding_actual_context_well_typed, padding_actual_functions_well_typed]
QED
