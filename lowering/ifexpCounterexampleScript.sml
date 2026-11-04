Theory ifexpCounterexample
Ancestors
  finite_map
  exprSimHyps exprSimOps exprSimUnwrap freshWrites exprLoweringProps
  vyperInterpreter vyperContext vyperState vyperAST

Definition witness_type_def:
  witness_type = StructT (NONE,"S")
End

Definition witness_body_def:
  witness_body = [Return (SOME (StructLit witness_type (NONE,"S")
    [("x", Literal (BaseT (UintT 256)) (IntL 1))]))]
End

Definition witness_context_def:
  witness_context = empty_evaluation_context with
    sources := [(0w, [(NONE,
      [StructDecl "S" [("x", BaseT (UintT 256))];
       FunctionDecl Internal Pure F F "f" [] [] witness_type witness_body])])]
End

Definition witness_call_def:
  witness_call = Call witness_type (IntCall (NONE,"f")) [] NONE
End

Theorem witness_source_call:
  eval_expr witness_context witness_call empty_state =
    (INL (Value (StructV [("x", IntV 1)])), empty_state)
Proof
  simp[witness_context_def, witness_call_def, witness_type_def,
       witness_body_def, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
  CONV_TAC EVAL >>
  simp[FLOOKUP_FUNION, FLOOKUP_UPDATE, DRESTRICT_FUPDATE] >>
  CONV_TAC EVAL >>
  simp[wordsTheory.dimword_def] >> CONV_TAC EVAL >> simp[] >>
  CONV_TAC EVAL
QED

Theorem witness_no_write_return:
  step_inst_base (mk_inst id RET [Lit 0w] []) s =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operands_def,
       venomStateTheory.eval_operand_def]
QED

Definition witness_source_state_def:
  witness_source_state = empty_state with outcomes := SOME []
End

Theorem witness_source_call_related_candidate:
  eval_expr witness_context witness_call witness_source_state =
    (INL (Value (StructV [("x", IntV 1)])), witness_source_state)
Proof
  simp[witness_context_def, witness_call_def, witness_type_def,
       witness_body_def, witness_source_state_def] >>
  CONV_TAC EVAL >>
  simp[FLOOKUP_FUNION, FLOOKUP_UPDATE, DRESTRICT_FUPDATE] >>
  CONV_TAC EVAL >>
  simp[wordsTheory.dimword_def] >> CONV_TAC EVAL >> simp[] >>
  CONV_TAC EVAL
QED

Definition witness_callee_def:
  witness_callee = venomInst$mk_raw_function "no_write"
    [<| bb_label := "entry";
        bb_instructions := [mk_inst 0 RET [Lit 0w] []] |>]
End

Theorem witness_callee_setup:
  setup_callee witness_callee args s =
    SOME (s with <|
      vs_vars := FEMPTY; vs_params := args;
      vs_current_bb := "entry"; vs_inst_idx := 0; vs_prev_bb := NONE;
      vs_halted := F; vs_allocas := FEMPTY; vs_fmp := s.vs_fmp;
      vs_call_entry_fmp := s.vs_fmp;
      vs_return_pc_token := if NULL args then 0w else LAST args |> )
Proof
  simp[witness_callee_def, venomInstTheory.mk_raw_function_def,
       venomExecSemanticsTheory.setup_callee_def]
QED

Theorem witness_callee_run:
  run_function 2 ctx witness_callee s =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (s with <| vs_current_bb := "entry"; vs_inst_idx := 0 |> )
Proof
  simp[witness_callee_def, venomInstTheory.mk_raw_function_def,
       venomExecSemanticsTheory.run_function_def,
       venomInstTheory.fn_entry_label_def] >> CONV_TAC EVAL
QED

Definition witness_compile_env_def:
  witness_compile_env ce = ce with <|
    ce_struct_fields := FEMPTY |+ ("S", [("x", BaseT (UintT 256), 32)]);
    ce_func_return_type := K (BaseT (UintT 0));
    ce_func_info := K (0,32,[]);
    ce_func_param_types := K [];
    ce_func_ids := K 0; ce_is_ctor := F |>
End

Theorem witness_physical_layout:
  same_memory_layout (witness_compile_env ce)
    (post_value_type (witness_compile_env ce) witness_call) witness_type /\
  evaluate_type (get_tenv witness_context)
    (post_value_type (witness_compile_env ce) witness_call) = NONE
Proof
  simp[witness_compile_env_def, witness_call_def, witness_type_def,
       exprLoweringTheory.lowered_value_type_def,
       contextTheory.same_memory_layout_def,
       contextTheory.punnable_def,
       compileEnvTheory.type_memory_bytes_def,
       compileEnvTheory.get_struct_fields_def,
       vyperValueTheory.evaluate_type_def,
       compileEnvTheory.is_word_type_def,
       compileEnvTheory.is_bytestring_type_def,
       compileEnvTheory.nsid_to_string_def, FLOOKUP_UPDATE]
QED
