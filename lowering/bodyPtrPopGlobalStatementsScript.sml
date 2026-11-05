Theory bodyPtrPopGlobalStatements
Ancestors
  bodyPtrPopGlobalFields bodyPtrPopGlobalInternal bodyPtrPopStructLegality
  bodyPtrPopGlobalLegality
  exprLowering stmtLowering compileEnv vyperAST context moduleLowering
Libs monadsyntax

Theorem pop_global_rhs_compiled:
  compile_expr pop_global_body_env pop_struct_ty
    (TopLevelName pop_struct_ty (NONE,"B")) =
    comp_return (LocatedValue pop_struct_ty (mk_ptr (Lit 4w) LocStorage))
Proof
  simp[FUN_EQ_THM, Once compile_expr_def, pop_global_body_global_B,
       expr_type_def, comp_return_def]
QED

Theorem pop_global_target_compiled:
  compile_get_target_ptr compile_expr pop_global_body_env pop_struct_root =
    comp_return (Lit 0w,SOME LocStorage,SOME (ValPT pop_struct_ty))
Proof
  simp[pop_struct_root_def, compile_get_target_ptr_def,
       pop_global_body_global_A, pop_global_body_global_A_hashmap,
       pop_global_body_global_A_type]
QED

Theorem pop_global_rhs_unwrap:
  unwrap_value pop_global_body_env
    (LocatedValue pop_struct_ty (mk_ptr (Lit 4w) LocStorage)) =
  do buf <- compile_alloc_buffer 128;
     compile_storage_to_memory (Lit 4w) buf.buf_operand 4;
     return buf.buf_operand od
Proof
  simp[unwrap_value_def, pop_struct_ty_def, is_word_type_def,
       mk_ptr_def, pop_global_body_struct_bytes,
       contextTheory.compile_ensure_in_memory_def] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  gen_tac >> pairarg_tac >> simp[] >>
  Cases_on `compile_storage_to_memory (Lit 4w) buf_op_alloc.buf_operand 4 cs'` >> simp[]
QED

Theorem pop_global_assignment_boundary:
  compile_stmt pop_global_body_env NoLoop (BaseT (UintT 256))
    (Assign (BaseTarget pop_struct_root) (TopLevelName pop_struct_ty (NONE,"B"))) =
  do buf <- compile_alloc_buffer 128;
     compile_storage_to_memory (Lit 4w) buf.buf_operand 4;
     compile_memory_to_storage buf.buf_operand (Lit 0w) 4;
     return () od
Proof
  simp[Once compile_stmt_def, expr_type_def, has_length_word_def,
       is_empty_value_expr_def, pop_struct_ty_def, is_bytestring_type_def] >>
  rewrite_tac[GSYM pop_struct_ty_def, pop_global_rhs_compiled,
              pop_global_target_compiled] >>
  simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pop_global_rhs_unwrap, vv_location_def, mk_ptr_def,
       lowered_value_type_def] >>
  rewrite_tac[GSYM mk_ptr_def, pop_global_rhs_unwrap,
              pop_global_body_struct_bytes, expr_type_def] >>
  simp[pop_struct_ty_def, is_word_type_def, compile_assign_value_def,
       is_bytestring_type_def, pop_global_body_struct_bytes,
       comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  gen_tac >> Cases_on `compile_alloc_buffer 128 x` >> simp[] >>
  rename1 `compile_storage_to_memory (Lit 4w) buf.buf_operand 4 st` >>
  Cases_on `compile_storage_to_memory (Lit 4w) buf.buf_operand 4 st` >> simp[]
QED

Theorem pop_global_return_boundary:
  compile_stmt pop_global_body_env NoLoop (BaseT (UintT 256))
    (Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))) =
  emit_inst RET [Lit 0w; Var "%5"] []
Proof
  simp[Once compile_stmt_def, pop_global_body_return_pc,
       compile_internal_return_from_env_def, pop_global_body_return_buf,
       pop_global_body_return_count, compile_internal_return_def] >>
  simp[lower_value_def, FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, Once compile_expr_def, expr_type_def,
       compile_literal_vv_def, unwrap_value_def] >>
  EVAL_TAC >> simp[]
QED

(* Closed states name bounded compiler computations, not semantic changes. *)
Definition pop_global_alloc_state_def:
  pop_global_alloc_state = pop_global_prologue_state with
    <| cs_next_var := 8; cs_next_id := 11;
       cs_current_insts := pop_global_prologue_state.cs_current_insts ++
         [mk_inst 10 ALLOCA [Lit 128w] ["%7"]] |>
End

Theorem pop_global_assignment_alloc:
  compile_alloc_buffer 128 pop_global_prologue_state =
    (<| buf_operand := Var "%7"; buf_size := 128 |>,pop_global_alloc_state)
Proof
  EVAL_TAC
QED

Definition pop_global_loaded_state_def:
  pop_global_loaded_state = pop_global_alloc_state with
    <| cs_next_var := 15; cs_next_label := 5; cs_next_id := 23;
       cs_current_bb := "@wcopy_exit_4"; cs_current_insts := [];
       cs_blocks :=
         [<| bb_label := "@wcopy_body_3"; bb_instructions :=
           [mk_inst 15 ADD [Lit 4w; Var "%8"] ["%10"];
            mk_inst 16 SLOAD [Var "%10"] ["%11"];
            mk_inst 17 MUL [Var "%8"; Lit 32w] ["%12"];
            mk_inst 18 ADD [Var "%7"; Var "%12"] ["%13"];
            mk_inst 19 MSTORE [Var "%13"; Var "%11"] [];
            mk_inst 20 ADD [Var "%8"; Lit 1w] ["%14"];
            mk_inst 21 ASSIGN [Var "%14"] ["%8"];
            mk_inst 22 JMP [Label "@wcopy_cond_2"] []] |>;
          <| bb_label := "@wcopy_cond_2"; bb_instructions :=
           [mk_inst 13 EQ [Var "%8"; Lit 4w] ["%9"];
            mk_inst 14 JNZ [Var "%9"; Label "@wcopy_exit_4"; Label "@wcopy_body_3"] []] |>;
          <| bb_label := "internal 0 replace()_runtime"; bb_instructions :=
            pop_global_alloc_state.cs_current_insts ++
             [mk_inst 11 ASSIGN [Lit 0w] ["%8"];
              mk_inst 12 JMP [Label "@wcopy_cond_2"] []] |>] ++
         pop_global_alloc_state.cs_blocks |>
End

Theorem pop_global_storage_copy_computed:
  compile_storage_to_memory (Lit 4w) (Var "%7") 4 pop_global_alloc_state =
    ("@wcopy_body_3",pop_global_loaded_state)
Proof
  EVAL_TAC
QED

Definition pop_global_assigned_state_def:
  pop_global_assigned_state = pop_global_loaded_state with
    <| cs_next_var := 22; cs_next_label := 8; cs_next_id := 35;
       cs_current_bb := "@wcopy_exit_7"; cs_current_insts := [];
       cs_blocks :=
         [<| bb_label := "@wcopy_body_6"; bb_instructions :=
           [mk_inst 27 MUL [Var "%15"; Lit 32w] ["%17"];
            mk_inst 28 ADD [Var "%7"; Var "%17"] ["%18"];
            mk_inst 29 MLOAD [Var "%18"] ["%19"];
            mk_inst 30 ADD [Lit 0w; Var "%15"] ["%20"];
            mk_inst 31 SSTORE [Var "%20"; Var "%19"] [];
            mk_inst 32 ADD [Var "%15"; Lit 1w] ["%21"];
            mk_inst 33 ASSIGN [Var "%21"] ["%15"];
            mk_inst 34 JMP [Label "@wcopy_cond_5"] []] |>;
          <| bb_label := "@wcopy_cond_5"; bb_instructions :=
           [mk_inst 25 EQ [Var "%15"; Lit 4w] ["%16"];
            mk_inst 26 JNZ [Var "%16"; Label "@wcopy_exit_7"; Label "@wcopy_body_6"] []] |>;
          <| bb_label := "@wcopy_exit_4"; bb_instructions :=
           [mk_inst 23 ASSIGN [Lit 0w] ["%15"];
            mk_inst 24 JMP [Label "@wcopy_cond_5"] []] |>] ++
         pop_global_loaded_state.cs_blocks |>
End

Theorem pop_global_memory_copy_computed:
  compile_memory_to_storage (Var "%7") (Lit 0w) 4 pop_global_loaded_state =
    ("@wcopy_body_6",pop_global_assigned_state)
Proof
  EVAL_TAC
QED

Theorem pop_global_assignment_computed:
  compile_stmt pop_global_body_env NoLoop (BaseT (UintT 256))
    (Assign (BaseTarget pop_struct_root) (TopLevelName pop_struct_ty (NONE,"B")))
    pop_global_prologue_state = ((),pop_global_assigned_state)
Proof
  rewrite_tac[pop_global_assignment_boundary] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       pop_global_assignment_alloc, pop_global_storage_copy_computed,
       pop_global_memory_copy_computed]
QED

Definition pop_global_returned_state_def:
  pop_global_returned_state = pop_global_assigned_state with
    <| cs_next_id := 36;
       cs_current_insts := [mk_inst 35 RET [Lit 0w;Var "%5"] []] |>
End

Theorem pop_global_return_computed:
  compile_stmt pop_global_body_env NoLoop (BaseT (UintT 256))
    (Return (SOME (Literal (BaseT (UintT 256)) (IntL 0))))
    pop_global_assigned_state = ((),pop_global_returned_state)
Proof
  rewrite_tac[pop_global_return_boundary] >> EVAL_TAC
QED

Theorem pop_global_body_entry_unterminated:
  ~block_is_terminated pop_global_prologue_state /\
  ~block_is_terminated pop_global_assigned_state /\
  block_is_terminated pop_global_returned_state
Proof
  EVAL_TAC
QED

Theorem pop_global_body_computed:
  compile_stmts pop_global_body_env NoLoop (BaseT (UintT 256)) pop_global_body
    pop_global_prologue_state = ((),pop_global_returned_state)
Proof
  rewrite_tac[pop_global_body_def] >>
  simp[Once compile_stmt_def, comp_get_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, declare_stmt_local_def,
       pop_global_body_entry_unterminated, pop_global_assignment_computed] >>
  simp[Once compile_stmt_def, comp_get_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, declare_stmt_local_def,
       pop_global_body_entry_unterminated, pop_global_return_computed] >>
  simp[Once compile_stmt_def, comp_return_def]
QED

(* Intermediate prologue states avoid expanding the dispatcher in consumers. *)
Definition pop_global_block_state_def:
  pop_global_block_state = pop_global_prologue_state with
    <| cs_next_var := 5; cs_next_id := 8; cs_current_insts := [] |>
End
Definition pop_global_retpc_state_def:
  pop_global_retpc_state = pop_global_prologue_state with
    <| cs_next_var := 6; cs_next_id := 9;
       cs_current_insts := [mk_inst 8 RETPC_PARAM [Lit 0w] ["%5"]] |>
End
Theorem pop_global_prologue_steps:
  new_block "internal 0 replace()_runtime" pop_global_dispatch_state =
    ("@fallback_0",pop_global_block_state) /\
  emit_op RETPC_PARAM [Lit 0w] pop_global_block_state =
    (Var "%5",pop_global_retpc_state) /\
  compile_alloc_buffer 32 pop_global_retpc_state =
    (<| buf_operand := Var "%6"; buf_size := 32 |>,pop_global_prologue_state)
Proof
  EVAL_TAC
QED

Theorem pop_global_body_return_buf_update:
  (pop_global_body_env with ce_return_buf := pop_global_package_env.ce_return_buf) =
  pop_global_body_env
Proof
  simp[pop_global_body_env_def, compile_env_component_equality]
QED

Theorem pop_global_internal_computed:
  (do new_block "internal 0 replace()_runtime";
      compile_internal_function pop_global_package_env [] F F 0 F F F 0
        pop_global_body (SOME (BaseT (UintT 256))) od)
    pop_global_dispatch_state = ((),pop_global_returned_state)
Proof
  simp[compile_internal_function_def, compile_internal_param_decls_def,
       materialize_internal_params_def, pop_global_return_count,
       pop_global_return_bytes, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, pop_global_prologue_steps] >>
  simp[GSYM pop_global_body_env_def, pop_global_body_return_buf_update,
       pop_global_body_computed,
       comp_get_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       pop_global_body_entry_unterminated]
QED
