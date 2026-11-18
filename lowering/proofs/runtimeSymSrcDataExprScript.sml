Theory runtimeSymSrcDataExpr
Ancestors
  runtimeSymSrcDataExprHelpers runtimeSymSrcDataExprBodies
  runtimeSymSrcDataFrame exprCallBounds exprLowering

(* The generated induction quantifies recursive calls over every compiler
   state.  Thus its hypotheses discharge the universal frame of callbacks,
   rather than merely a frame at the current state. *)
Theorem runtime_data_frame_expr_mutual:
  (!cenv ty e st.
    (SND (compile_expr cenv ty e st)).cs_data_sections = st.cs_data_sections) /\
  (!cenv rt ty bi args st.
    (SND (compile_builtin_dispatch cenv rt ty bi args st)).cs_data_sections =
      st.cs_data_sections) /\
  (!cenv vt ty tb rt args st.
    (SND (compile_type_builtin_dispatch cenv vt ty tb rt args st)).cs_data_sections =
      st.cs_data_sections)
Proof
  mp_tac (REWRITE_RULE [compiler_preserves_runtime]
    (Q.INST [`R` |-> `\data s t. s = t /\ s.cs_data_sections = data`] compiler_preserves_expr)) >>
  simp[runtime_data_frame_expr_body_assembled,
       runtime_data_frame_builtin_body_assembled,
       runtime_data_frame_type_body_assembled] >>
  simp[runtime_data_frame_def]
QED

Theorem runtime_data_frame_compile_expr[simp]:
  runtime_data_frame (compile_expr cenv ty e)
Proof
  simp[runtime_data_frame_def, runtime_data_frame_expr_mutual]
QED

Theorem runtime_data_frame_compile_builtin_dispatch[simp]:
  runtime_data_frame (compile_builtin_dispatch cenv rt ty bi args)
Proof
  simp[runtime_data_frame_def, runtime_data_frame_expr_mutual]
QED

Theorem runtime_data_frame_compile_type_builtin_dispatch[simp]:
  runtime_data_frame (compile_type_builtin_dispatch cenv vt ty tb rt args)
Proof
  simp[runtime_data_frame_def, runtime_data_frame_expr_mutual]
QED
