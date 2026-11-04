Theory abiEncodeTupleTraceProbe
Ancestors
  exprLowering compileEnv context vyperAST venomInst words finite_map
Libs
  wordsLib

Definition trace_probe_origin_def:
  trace_probe_origin = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition trace_probe_ce_def:
  trace_probe_ce = (ARB : compile_env) with ce_struct_fields := FEMPTY
End

Definition trace_probe_args_def:
  trace_probe_args =
    [Name (ArrayT (BaseT (UintT 256)) (Fixed 1)) "x";
     Pop (BaseT (UintT 256)) (NameTarget "x")]
End

Definition trace_probe_cfn_def:
  trace_probe_cfn ce ty e st =
    (if is_word_type ty then StackValue ty (Lit 0w)
     else LocatedValue ty (mk_ptr (Lit 0w) LocMemory), st)
End

Definition trace_probe_actual_args_def:
  trace_probe_actual_args = compile_abi_encode_args trace_probe_cfn trace_probe_ce
    trace_probe_args trace_probe_origin
End

Theorem trace_probe_actual_args_counter:
  (SND trace_probe_actual_args).cs_next_var = 1
Proof
  EVAL_TAC
QED

Definition trace_probe_old_args_def:
  trace_probe_old_args = compile_multi_exprs trace_probe_cfn trace_probe_ce
    trace_probe_args trace_probe_origin
End

Definition trace_probe_allocate_def:
  trace_probe_allocate arg_result = compile_alloc_buffer 64 (SND arg_result)
End

Definition trace_probe_stage_def:
  trace_probe_stage arg_result =
    let (buf,st) = trace_probe_allocate arg_result in
    compile_store_abi_tuple trace_probe_ce buf.buf_operand 0
      (ZIP (FST arg_result, MAP expr_type trace_probe_args)) st
End

Definition trace_probe_encode_def:
  trace_probe_encode arg_result =
    lower_abi_encode T NONE (FST (trace_probe_allocate arg_result)).buf_operand
      (AbiCopy 64) 64 (SND (trace_probe_stage arg_result))
End

Theorem trace_probe_old_result_counter:
  (SND (trace_probe_encode trace_probe_old_args)).cs_next_var = 5
Proof
  EVAL_TAC
QED

Theorem trace_probe_actual_result_counter:
  (SND (trace_probe_encode trace_probe_actual_args)).cs_next_var = 6
Proof
  EVAL_TAC
QED

Theorem trace_probe_dispatch_counter:
  (SND (compile_type_builtin_dispatch_body trace_probe_cfn trace_probe_ce
    (BaseT (BytesT (Dynamic 96))) (BaseT (BytesT (Dynamic 96)))
    (AbiEncode T NONE) (BaseT (BytesT (Dynamic 96)))
    trace_probe_args trace_probe_origin)).cs_next_var = 6
Proof
  EVAL_TAC
QED

Theorem trace_probe_shapes:
  type_memory_bytes trace_probe_ce (TupleT (MAP expr_type trace_probe_args)) = 64 /\
  type_to_abi_enc_info trace_probe_ce.ce_struct_fields trace_probe_ce
    (TupleT (MAP expr_type trace_probe_args)) = AbiCopy 64 /\
  abi_size_bound trace_probe_ce.ce_struct_fields
    (TupleT (MAP expr_type trace_probe_args)) = 64
Proof
  EVAL_TAC
QED

(* This is the old trace's existential conclusion, evaluated at its
   actual dispatcher result and its old argument-compiler result. *)
Theorem old_tuple_trace_counterexample:
  let args = trace_probe_args in
  let ce = trace_probe_ce in
  let origin = trace_probe_origin in
  let (ops,arg_st) = compile_multi_exprs trace_probe_cfn ce args origin in
  let (vv,final) = compile_type_builtin_dispatch_body trace_probe_cfn ce
    (BaseT (BytesT (Dynamic 96))) (BaseT (BytesT (Dynamic 96)))
    (AbiEncode T NONE) (BaseT (BytesT (Dynamic 96))) args origin in
  ~(LENGTH args = 1 /\ ~T) /\
  ~(?buf allocated staged out.
    compile_alloc_buffer (type_memory_bytes ce (TupleT (MAP expr_type args))) arg_st = (buf,allocated) /\
    compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (ops,MAP expr_type args)) allocated = ((),staged) /\
    lower_abi_encode T (OPTION_MAP bytes_method_id_word NONE) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)))
      (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged = (out,final) /\
    vv = LocatedValue (BaseT (BytesT (Dynamic 96))) (mk_ptr out LocMemory))
Proof
  simp_tac bool_ss [LET_THM] >>
  pairarg_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF] >>
  pairarg_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF] >>
  rpt gen_tac >> rpt disch_tac >>
  `final.cs_next_var = 6` by
    (mp_tac trace_probe_dispatch_counter >> simp[]) >>
  full_simp_tac bool_ss [trace_probe_shapes, optionTheory.OPTION_MAP_DEF] >>
  `SND (trace_probe_encode trace_probe_old_args) = final` by
    (asm_simp_tac bool_ss [trace_probe_encode_def, trace_probe_stage_def,
          trace_probe_allocate_def, trace_probe_old_args_def, LET_THM,
          pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND]) >>
  mp_tac trace_probe_old_result_counter >> simp[]
QED
