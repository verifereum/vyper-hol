Theory exprSimAbiEncodeArgsTraceProbe
Ancestors
  exprLowering builtinAbi compileEnv valueEncoding

Definition trace_ty_def:
  trace_ty = BaseT (BytesT (Dynamic 64))
End
Definition trace_e_def:
  trace_e = Literal trace_ty (BytesL [])
End
Definition trace_st_def:
  trace_st = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
    cs_current_bb := "entry"; cs_current_insts := []; cs_blocks := [];
    cs_data_sections := [] |>
End
Definition trace_ptr_def:
  trace_ptr = mk_ptr (Lit 0w) LocMemory
End
Definition trace_cfn_def:
  trace_cfn ce ty e st = (LocatedValue trace_ty trace_ptr, trace_st)
End
Definition trace_actual_def:
  trace_actual ce = compile_type_builtin_dispatch_body trace_cfn ce trace_ty trace_ty
    (AbiEncode F NONE) trace_ty [trace_e] trace_st
End

Theorem trace_types:
  expr_type trace_e = trace_ty /\
  lowered_value_type ce trace_e = BaseT (BytesT (Dynamic 0)) /\
  ~is_word_type (expr_type trace_e)
Proof
  EVAL_TAC
QED

Theorem trace_state_mismatch:
  SND (lower_abi_encode F NONE trace_ptr.ptr_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce trace_ty)
    (abi_size_bound ce.ce_struct_fields trace_ty) trace_st) <>
  SND (trace_actual ce)
Proof
  EVAL_TAC >> simp[wordsTheory.word_eq_n2w, wordsTheory.dimword_def,
    fcpTheory.index_bit0, wordsTheory.dimindex_128,
    fcpTheory.finite_bit0, wordsTheory.finite_128,
    fcpTheory.index_one, fcpTheory.finite_one,
    bitTheory.MOD_2EXP_EQ_def, bitTheory.MOD_2EXP_def]
QED

(* A complete instance of the premises and negated conclusion of
   abiBuiltinEncodeWord.compile_abi_encode_memory_trace.  No import of that
   broken theorem (or its theory) is used. *)
Theorem compile_abi_encode_memory_trace_counterexample:
  ~is_word_type (expr_type trace_e) /\
  trace_cfn ce (expr_type trace_e) trace_e trace_st =
    (LocatedValue (expr_type trace_e) trace_ptr,trace_st) /\
  trace_ptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body trace_cfn ce trace_ty trace_ty
    (AbiEncode F NONE) trace_ty [trace_e] trace_st =
      (FST (trace_actual ce),SND (trace_actual ce)) /\
  ~(?out. lower_abi_encode F NONE trace_ptr.ptr_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type trace_e))
      (abi_size_bound ce.ce_struct_fields (expr_type trace_e)) trace_st =
        (out,SND (trace_actual ce)) /\
    FST (trace_actual ce) = LocatedValue trace_ty (mk_ptr out LocMemory))
Proof
  `trace_ptr.ptr_location = LocMemory` by EVAL_TAC >>
  simp[trace_types, trace_cfn_def, trace_actual_def,
       GSYM pairTheory.PAIR] >>
  rpt strip_tac >>
  mp_tac trace_state_mismatch >>
  gvs[trace_actual_def, trace_types]
QED
