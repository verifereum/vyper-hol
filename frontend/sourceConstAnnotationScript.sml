Theory sourceConstAnnotation
Ancestors
  sourceConstAST list string

(* Source annotation syntax, reusable by all declaration/bound consumers.
   Names are unresolved paths (including primitive spellings). Bounds are
   original expressions, never inferred lengths or folded replacements.
   Missing annotations belong in an option at the consumer, not this AST. *)
Datatype:
  source_const_qualifier = SCQ_Constant | SCQ_Immutable | SCQ_Public
                         | SCQ_Transient | SCQ_Indexed
End

Datatype:
  source_const_annotation = SCA_Name (string list)
                          | SCA_String source_const_expr
                          | SCA_Bytes source_const_expr
                          | SCA_StaticArray source_const_annotation source_const_expr
                          | SCA_DynArray source_const_annotation source_const_expr
                          | SCA_HashMap source_const_annotation source_const_annotation
                          | SCA_Tuple (source_const_annotation list)
                          | SCA_Qualified source_const_qualifier source_const_annotation
End
