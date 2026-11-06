Theory bodyPtrPopFrameProbe
Ancestors
  bodyPtrPopTraceProbe bodyPtrPopGlobalLoweringInputs
  bodyPtrPopGlobalSource bodyPtrPopGlobalUnit bodyPtrPopGlobalLegality
  exprLoweringProps exprLowering compileEnv context fragExec venomInst
  vyperValue venomState finite_map list rich_list

Theorem pop_trace_code_contained:
  fn_has_code (initial_compile_state "probe") pop_trace_compiled pop_trace_fn
Proof
  simp[fn_has_code_def, pop_trace_fn_def, mk_raw_function_def] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexists_tac `<|bb_label := pop_trace_compiled.cs_current_bb;
    bb_instructions := pop_trace_compiled.cs_current_insts ++
      [mk_inst 1000 STOP [] []]|>` >>
  simp[IS_PREFIX_APPEND] >>
  EVAL_TAC >> simp[]
QED

Theorem pop_trace_ids_distinct:
  fn_inst_ids_distinct pop_trace_fn
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >> simp[]
QED

(* alloca_room requires the caller itself to belong to the context. *)
Theorem pop_trace_state_unrelated:
  ~stmt_state_rel pop_global_runtime_context pop_trace_fn pop_global_package_env
    pop_global_cx pop_global_es pop_trace_start
Proof
  simp[stmt_state_rel_def, alloca_room_def] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >> simp[]
QED

Theorem pop_stmt_frame_function_lookup:
  stmt_state_rel ctx func cenv cx es s ==>
  venomInst$lookup_function func.fn_name ctx.ctx_functions = SOME func
Proof
  simp[stmt_state_rel_def, alloca_room_def]
QED
