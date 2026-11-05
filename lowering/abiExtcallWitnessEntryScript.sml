(* Concrete compilation and function entry for the extcall witness. *)
Theory abiExtcallWitnessEntry
Ancestors
  abiExtcallWitnessInvariant abiExtcallWitnessRecords abiExtcallWitnessProbe
  abiExtcallWrapReachProbe exprLowering vyperAST compileEnv
  exprLoweringProps fragExec exprCallBounds fcgDefs venomInst relation

Theorem witness_compile:
  compile_expr witness_cenv reach_return witness_expr wrap_probe_start =
    (LocatedValue reach_return (mk_ptr (FST reach_compile) LocMemory),
     SND reach_compile)
Proof
  `expr_child_callback (expr_size witness_expr) compile_expr witness_cenv
     (BaseT AddressT) witness_target =
     (\st. (StackValue (BaseT AddressT) (Lit 256w),st))` by
    simp[FUN_EQ_THM, witness_target_callback] >>
  `expr_child_callback (expr_size witness_expr) compile_expr witness_cenv
     (BaseT (UintT 256)) witness_gas =
     (\st. (StackValue (BaseT (UintT 256)) (Lit 10000w),st))` by
    simp[FUN_EQ_THM, witness_gas_callback] >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[SF ETA_ss, witness_expr_def, compile_expr_body_def, expr_type_def,
       compile_call_def, lower_value_def, compile_multi_vvs_def,
       compile_ext_call_kwargs_def, compile_ext_call_kwarg_def,
       witness_target_callback, witness_gas_callback] >>
  simp[SF ETA_ss, expr_child_callback_def, expr_size_def,
       witness_target_def, witness_gas_def, witness_target_compile,
       witness_gas_compile] >>
  simp[comp_bind_def, comp_return_def, unwrap_value_def,
       reach_compile_def, reach_wrapped_def, reach_return_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[] >> EVAL_TAC
QED

Definition witness_vv_def:
  witness_vv = LocatedValue reach_return (mk_ptr (FST reach_compile) LocMemory)
End
Definition witness_sb_def:
  witness_sb = SND reach_compile
End
Definition witness_func_def:
  witness_func = <|fn_name := "probe";
    fn_blocks := witness_sb.cs_blocks ++
      [<|bb_label := witness_sb.cs_current_bb;
         bb_instructions := witness_sb.cs_current_insts ++
           [mk_inst witness_sb.cs_next_id STOP [] []]|>];
    fn_call_abi := <|ica_has_memory_return_buffer := NONE;
                    ica_user_return_count := NONE|>;
    fn_noinline := F; fn_forced_alloc_positions := FEMPTY; fn_eom := NONE;
    fn_mems_used := []; fn_fmp_signature := NONE|>
End

Theorem witness_code:
  fn_has_code wrap_probe_start witness_sb witness_func
Proof
  rewrite_tac[fn_has_code_def] >> conj_tac
  >- (CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
      rpt strip_tac >> gvs[])
  >> qexists `<|bb_label := witness_sb.cs_current_bb;
       bb_instructions := witness_sb.cs_current_insts ++
         [mk_inst witness_sb.cs_next_id STOP [] []]|>` >>
  reverse conj_tac >- simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_ids:
  fn_inst_ids_distinct witness_func
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >> simp[]
QED

Theorem witness_reserved:
  local_ptrs_reserved witness_cenv wrap_probe_start
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_entry_cursor:
  ~witness_s0.vs_halted /\
  witness_s0.vs_current_bb = wrap_probe_start.cs_current_bb /\
  witness_s0.vs_inst_idx = LENGTH wrap_probe_start.cs_current_insts
Proof
  EVAL_TAC
QED

Theorem witness_call_context:
  call_ctx_rel witness_cx.txn witness_s0.vs_call_ctx
    witness_s0.vs_tx_ctx witness_s0.vs_block_ctx
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_state_relation:
  state_rel witness_func witness_cenv witness_cx witness_es witness_s0
Proof
  simp[state_rel_def, witness_call_context] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[]
QED

Definition witness_ctx_def:
  witness_ctx = mk_venom_context [witness_func] (SOME "probe")
End

Theorem witness_no_invoke:
  ~EXISTS (\inst. inst.inst_opcode = INVOKE) (fn_insts witness_func)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_no_edges:
  ~fn_directly_calls witness_ctx a b
Proof
  `!a. lookup_function a witness_ctx.ctx_functions =
       if a = "probe" then SOME witness_func else NONE` by
    simp[witness_ctx_def, mk_venom_context_def, lookup_function_def,
         witness_func_def, listTheory.FIND_thm] >>
  simp[fn_directly_calls_def] >>
  rpt strip_tac >> gvs[] >>
  mp_tac witness_no_invoke >> rewrite_tac[listTheory.EXISTS_MEM] >>
  qexists `inst` >> simp[]
QED

Theorem witness_no_reachable:
  !a b. TC (fn_directly_calls witness_ctx) a b ==> F
Proof
  ho_match_mp_tac TC_INDUCT >> simp[witness_no_edges]
QED

Theorem witness_alloca_room:
  alloca_room witness_ctx witness_func witness_s0
Proof
  simp[alloca_room_def, witness_no_reachable] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

Theorem witness_fmp_room:
  fmp_room witness_ctx witness_func witness_s0
Proof
  simp[fmp_room_def, witness_no_reachable] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem witness_stmt_relation:
  stmt_state_rel witness_ctx witness_func witness_cenv witness_cx
    witness_es witness_s0
Proof
  simp[stmt_state_rel_def, witness_state_relation, witness_alloca_room,
       witness_fmp_room] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >> simp[]
QED
