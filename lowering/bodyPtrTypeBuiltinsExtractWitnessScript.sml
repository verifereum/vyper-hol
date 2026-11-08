(* Concrete actual-program probe for the fixed-bytes Extract32 gate.
   Definitions abbreviate the concrete certificate, not a new semantics. *)
Theory bodyPtrTypeBuiltinsExtractWitness
Ancestors bodyPtrTypeBuiltinsExtractAudit bodyPtrTypeBuiltinsPaddingFrame
  compileVyper vyperCompiler venomCompilerTypes venomPolicyTypes
  vyperInterpreter vyperTypeSystem vyperTyping vyperState compileEnv
  exprLoweringProps exprLowering venomInst venomState finite_map words list
  bodySim supportedExprForms

Definition extract_witness_expr_def:
  extract_witness_expr =
    TypeBuiltin (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
      [TypeBuiltin (BaseT (BytesT (Fixed 32))) Empty
         (BaseT (BytesT (Fixed 32))) [];
       Literal (BaseT (UintT 256)) (IntL 0)]
End

Definition extract_witness_program_def:
  extract_witness_program =
    [FunctionDecl Internal Pure F F "extract_probe" [] [] (BaseT (UintT 256))
       [Return (SOME extract_witness_expr)]]
End

Definition extract_witness_runtime_def:
  extract_witness_runtime = THE
    (lower_vyper_runtime_unit extract_witness_program padding_policy)
End

Definition extract_witness_label_def:
  extract_witness_label = internal_fn_label
    (build_func_ids 0 extract_witness_program "extract_probe") "extract_probe" [] F
End

Definition extract_witness_function_def:
  extract_witness_function = THE (venomInst$lookup_function extract_witness_label
    extract_witness_runtime.cu_context.ctx_functions)
End

Theorem extract_witness_supported:
  ~supported_program extract_witness_program
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Theorem extract_witness_member:
  venomInst$lookup_function extract_witness_function.fn_name
    extract_witness_runtime.cu_context.ctx_functions = SOME extract_witness_function
Proof
  EVAL_TAC >> simp[dimword_def] >> EVAL_TAC >> simp[]
QED

Theorem extract_witness_no_embedded_body_inv:
  !ctx cenv cx. ~body_inv extract_witness_program ctx cenv cx
Proof
  simp[body_inv_def, extract_witness_supported]
QED

Theorem extract_witness_form_unsupported:
  !tops. ~supported_type_builtin_form tops (BaseT (UintT 256))
    Extract32 (BaseT (UintT 256))
      [TypeBuiltin (BaseT (BytesT (Fixed 32))) Empty
         (BaseT (BytesT (Fixed 32))) [];
       Literal (BaseT (UintT 256)) (IntL 0)]
Proof
  simp[supported_type_builtin_form_def]
QED
