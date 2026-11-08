Theory exprSimAbiEncodeArgsTupleTarget
Ancestors
  exprSimAbiEncodeArgsTupleSource exprSimAbiEncodeArgsTupleProbe
  exprLowering compileEnv

Theorem tuple_return_metadata:
  compute_func_info sft tuple_narrow
    (type_memory_bytes ce tuple_narrow) [] = (0,128,[])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def,
                  vfmConstantsTheory.word_size_def]
QED

Theorem tuple_actual_call_compile:
  ce.ce_func_info (nsid_to_string (NONE,"f")) = (0,128,[]) /\
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow ==>
  compile_expr ce ty tuple_call sa =
    (let (buf,sm) = compile_alloc_buffer 128 sa in
     let (_,sb) = emit_void INVOKE
       [Label (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,"f")))
          (nsid_to_string (NONE,"f"))
          (ce.ce_func_param_types (nsid_to_string (NONE,"f"))) ce.ce_is_ctor);
        buf.buf_operand] sm in
     (LocatedValue tuple_narrow (base_ptr buf),sb))
Proof
  simp[tuple_call_def, Once compile_expr_def, compile_call_def,
       compile_multi_vvs_def, compile_stage_intcall_args_def, comp_return_def] >>
  strip_tac >> Cases_on `compile_alloc_buffer 128 sa` >>
  simp[compile_stage_intcall_args_def, comp_return_def]
QED

Theorem tuple_actual_unwrap:
  lower_value compile_expr ce ty tuple_call sa =
    (case compile_expr ce ty tuple_call sa of (vv,sb) => unwrap_value ce vv sb)
Proof
  Cases_on `compile_expr ce ty tuple_call sa` >>
  simp[lower_value_def, comp_bind_def]
QED

Theorem tuple_actual_singleton_operand:
  compile_expr ce tuple_wide tuple_call sa =
    (LocatedValue tuple_narrow (base_ptr buf),sb) ==>
  compile_abi_encode_args compile_expr ce [tuple_call] sa = ([buf.buf_operand],sb)
Proof
  simp[compile_abi_encode_args_def, tuple_call_def,
       vyperASTTheory.expr_type_def, expr_can_mutate_def,
       unwrap_value_def, tuple_narrow_def, is_word_type_def,
       contextTheory.base_ptr_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED
