(* Equal-layout memory-return diagnostic. Not a target counterexample. *)
Theory bodyIntCallReturnProbe
Ancestors
  bodyIntCallHeadroomProbe stmtSim venomExecSemantics

Definition return_probe_env_def:
  return_probe_env = headroom_probe_callee_env with
    <| ce_return_pc := SOME (PtrVar (Var "pc") 32);
       ce_return_buf := SOME (PtrVar (Var "missing_buf") 32);
       ce_returns_count := 0;
       ce_imm_alloca := NONE;
       ce_vars := FEMPTY |++ [("x",PtrVar (Lit 128w) 32)] |>
End

Definition return_probe_compiled_def:
  return_probe_compiled =
    SND (compile_stmt return_probe_env NoLoop headroom_probe_type
      (Return (SOME (Name headroom_probe_type "x")))
      (initial_compile_state "probe"))
End

Theorem return_probe_instructions:
  MAP (\i. (i.inst_opcode,i.inst_operands))
    return_probe_compiled.cs_current_insts =
    [(MCOPY,[Var "missing_buf"; Lit 128w; Lit 32w]);
     (RET,[Var "pc"])]
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Definition return_probe_state_def:
  return_probe_state = update_var "pc" 0w (init_venom_state "probe")
End

Theorem return_probe_pc_without_buffer:
  ret_pc_ok return_probe_env (initial_compile_state "probe")
    return_probe_state /\
  eval_operand (Var "missing_buf") return_probe_state = NONE
Proof
  simp[loweringPostsTheory.ret_pc_ok_def, return_probe_env_def,
       compileEnvTheory.not_fresh_at_def, return_probe_state_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       venomStateTheory.init_venom_state_def,
       venomStateTheory.eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem return_probe_first_step_error:
  step_inst_base (HD return_probe_compiled.cs_current_insts)
    return_probe_state = Error "undefined operand"
Proof
  EVAL_TAC
QED

Definition return_probe_function_def:
  return_probe_function = mk_raw_function "probe"
    [<| bb_label := return_probe_compiled.cs_current_bb;
        bb_instructions := return_probe_compiled.cs_current_insts |>]
End

Theorem return_probe_local_reservation:
  local_ptrs_reserved return_probe_env (initial_compile_state "probe")
Proof
  simp[compileEnvTheory.local_ptrs_reserved_def, return_probe_env_def,
       finite_mapTheory.FUPDATE_LIST_THM, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem return_probe_code:
  fn_has_code (initial_compile_state "probe") return_probe_compiled
    return_probe_function /\ fn_inst_ids_distinct return_probe_function /\
  ~block_is_terminated (initial_compile_state "probe")
Proof
  EVAL_TAC >> simp[]
QED

Definition return_probe_source_def:
  return_probe_source = empty_state with outcomes := SOME []
End

(* This first entry candidate is NOT admissible. In particular, its
   default transaction does not supply the required call-context relation.
   The execution error above is therefore not yet a stmt_frag counterexample. *)
Theorem return_probe_default_entry_not_admissible:
  ~stmt_state_rel (FST (extract_context "probe" return_probe_compiled))
    return_probe_function return_probe_env empty_evaluation_context
    return_probe_source return_probe_state
Proof
  EVAL_TAC
QED

Theorem return_probe_default_call_context_fails:
  ~call_ctx_rel empty_evaluation_context.txn return_probe_state.vs_call_ctx
    return_probe_state.vs_tx_ctx return_probe_state.vs_block_ctx
Proof
  EVAL_TAC
QED

Definition return_probe_context_def:
  return_probe_context = empty_evaluation_context with txn updated_by
    (\tx. tx with <| block_number := 1; block_hashes := [0w] |>)
End

Definition return_probe_valid_state_def:
  return_probe_valid_state = return_probe_state with vs_block_ctx updated_by
    (\bc. bc with bc_number := 1w)
End

Theorem return_probe_valid_call_context:
  call_ctx_rel return_probe_context.txn return_probe_valid_state.vs_call_ctx
    return_probe_valid_state.vs_tx_ctx return_probe_valid_state.vs_block_ctx
Proof
  EVAL_TAC >> simp[]
QED

Theorem return_probe_no_calls:
  fn_directly_calls (FST (extract_context "probe" return_probe_compiled)) =
    (\a b. F)
Proof
  simp[FUN_EQ_THM, fcgDefsTheory.fn_directly_calls_def,
       vyperCompilerTheory.extract_context_def, return_probe_compiled_def,
       venomInstTheory.mk_venom_context_def]
  >> EVAL_TAC >> simp[venomInstTheory.fn_insts_blocks_def]
  >> rpt strip_tac >> gvs[]
QED

Theorem return_probe_empty_tc[local]:
  !a b. ~TC (\(x:string) (y:string). F) a b
Proof
  simp[Once relationTheory.TC_CASES1]
QED

Theorem return_probe_valid_state_relation:
  stmt_state_rel (FST (extract_context "probe" return_probe_compiled))
    return_probe_function return_probe_env return_probe_context
    return_probe_source return_probe_valid_state
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       exprLoweringPropsTheory.alloca_room_def,
       exprLoweringPropsTheory.fmp_room_def, return_probe_no_calls,
       return_probe_empty_tc]
  >> EVAL_TAC >> simp[]
QED

Theorem return_probe_run:
  !fuel. run_from fuel (FST (extract_context "probe" return_probe_compiled))
    return_probe_function return_probe_valid_state =
    Error "undefined operand"
Proof
  gen_tac >> EVAL_TAC
QED

Theorem return_probe_compilation:
  stmt_env return_probe_env NoLoop headroom_probe_type
    (Return (SOME (Name headroom_probe_type "x")))
    (initial_compile_state "probe") =
    (return_probe_env,return_probe_compiled)
Proof
  simp[loweringPostsTheory.stmt_env_def,
       stmtLoweringTheory.declare_stmt_local_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, return_probe_compiled_def]
  >> pairarg_tac >> simp[]
QED

Theorem return_probe_entry_control:
  ret_pc_ok return_probe_env (initial_compile_state "probe")
    return_probe_valid_state /\
  ~return_probe_valid_state.vs_halted /\
  return_probe_valid_state.vs_current_bb =
    (initial_compile_state "probe").cs_current_bb /\
  return_probe_valid_state.vs_inst_idx =
    LENGTH (initial_compile_state "probe").cs_current_insts
Proof
  simp[loweringPostsTheory.ret_pc_ok_def, return_probe_env_def,
       compileEnvTheory.not_fresh_at_def, return_probe_valid_state_def,
       return_probe_state_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, venomStateTheory.init_venom_state_def,
       vyperCompilerTheory.initial_compile_state_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem return_probe_not_stmt_frag:
  !RetQ v es'.
  ~stmt_frag (FST (extract_context "probe" return_probe_compiled))
    return_probe_function return_probe_context NoLoop RetQ return_probe_env
    (stmt_env return_probe_env NoLoop headroom_probe_type
      (Return (SOME (Name headroom_probe_type "x")) ))
    return_probe_source (INR (ReturnException v)) es'
Proof
  rpt gen_tac >> simp[stmt_frag_def] >>
  qexistsl_tac [`initial_compile_state "probe"`,
    `return_probe_compiled`, `return_probe_valid_state`, `return_probe_env`] >>
  simp[return_probe_compilation, return_probe_code,
       return_probe_local_reservation, return_probe_entry_control,
       return_probe_valid_state_relation, stmt_res_ok_def,
       loweringPostsTheory.stmt_lands_def, return_probe_run,
       fragExecTheory.exit_result_def]
QED
