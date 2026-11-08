Theory bodyPtrBytestringBuiltinsResultLayoutAudit
Ancestors bodyPtrBytestringBuiltinsAggregateConsumer
          bodyPtrBytestringBuiltinsCompilerAllocationTrace
          supportedProgram supportedExprs supportedExprForms supportedTypes
          supportedDecls supportedNames compileVyper
          exprLowering compileEnv context finite_map list

(* Repeated concrete audit fixtures, not predicates used by the compiler-image
   proof.  They separate source annotation from StructLit constructor name. *)
Definition layout_audit_tops_def:
  layout_audit_tops =
    [StructDecl "E" [];
     StructDecl "A" [("f",StructT (NONE,"E"))];
     StructDecl "B" [("f",BaseT (UintT 256))];
     VariableDecl Private Immutable "z" (StructT (NONE,"E")) NONE]
End

Definition layout_audit_child_def:
  layout_audit_child = TopLevelName (StructT (NONE,"E")) (NONE,"z")
End

Theorem layout_audit_supported_mismatched_constructor:
  supported_pure_expr layout_audit_tops
    (StructLit (StructT (NONE,"A")) (NONE,"B") [("f",layout_audit_child)])
Proof
  EVAL_TAC >> simp[]
QED

Theorem layout_audit_zero_code_child:
  !ce s callty.
  compile_expr
    (ce with ce_module_vars := FEMPTY |+ ((NONE,"z"),ImmutableLoc 0))
    callty layout_audit_child s =
  (LocatedValue (StructT (NONE,"E")) (mk_ptr (Lit 0w) LocCode),s) /\
  lowered_value_type ce layout_audit_child = StructT (NONE,"E")
Proof
  simp[layout_audit_child_def, Once compile_expr_def, lowered_value_type_def] >> EVAL_TAC >> simp[]
QED

Theorem layout_audit_struct_lookup_mismatch:
  !ce.
  type_memory_bytes (ce with ce_struct_fields := make_struct_fields_map layout_audit_tops)
      (StructT (NONE,"E")) = 0 /\
  ALOOKUP (get_struct_fields (make_struct_fields_map layout_audit_tops) "B") "f" =
    SOME (BaseT (UintT 256),32) /\
  BaseT (UintT 256) <> StructT (NONE,"E")
Proof
  EVAL_TAC >> simp[]
QED

Theorem layout_audit_supported_declarations:
  supported_program layout_audit_tops
Proof
  EVAL_TAC
QED
