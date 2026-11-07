(* Extract32 interface probes.  Fixed bytes are accepted by typing, but
   the compiler unconditionally treats the source word as a memory pointer. *)
Theory bodyPtrTypeBuiltinsExtractAudit
Ancestors bodyPtrTypeBuiltinsBounds bodyPtrTypeBuiltinsWordCases
  builtinBytes compileEnv emitHelper exprLowering exprLoweringProps
  ptrDiscipline contextCodegenRel codegenRel venomInst venomState
  venomExecSemantics vyperTypeSystem vyperAST vyperContext finite_map

Theorem extract32_fixed_source_args_accepted:
  well_typed_type_builtin_args Extract32 (BaseT (UintT 256))
    [BaseT (BytesT (Fixed 32)); BaseT (UintT 256)]
Proof
  simp[well_typed_type_builtin_args_def, is_int_type_def,
       extract32_result_base_ok_def]
QED

Theorem extract32_zero_length_bounds_rejected:
  !off:256 word. ~(w2n off + 32 <= w2n (0w:256 word))
Proof
  simp[]
QED

Theorem extract32_fixed_source_zero_load_rejected:
  !s id out.
    ~access_ok 0 FEMPTY (mk_raw_function "extract" [])
      (mk_inst id MLOAD [Lit 0w] [out]) s
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem extract32_empty_fixed_source_is_literal:
  !cenv sa.
    lower_value compile_expr cenv (BaseT (BytesT (Fixed 32)))
      (TypeBuiltin (BaseT (BytesT (Fixed 32))) Empty (BaseT (BytesT (Fixed 32))) []) sa =
      (Lit 0w,sa)
Proof
  rpt gen_tac >>
  simp[lower_value_def, Once compile_expr_def, comp_bind_def,
       compile_type_builtin_dispatch_component_eq,
       exprCallBoundsTheory.expr_child_callback_def,
       compile_type_builtin_dispatch_body_def, unwrap_value_def,
       comp_return_def, lowered_value_type_def, expr_type_def, is_word_type_def]
QED

Theorem extract32_literal_source_prepare_head:
  compile_bytestring_src (Lit 0w) sa = ((len,dp),sb) ==>
  HD (emitted_insts sa sb) =
    mk_inst sa.cs_next_id MLOAD [Lit 0w]
      [STRING #"%" (toString sa.cs_next_var)]
Proof
  simp[compile_bytestring_src_def, comp_bind_def, comp_return_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                   rich_listTheory.DROP_LENGTH_APPEND] >> simp[]
QED
