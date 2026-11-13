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
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> BETA_TAC
  >~ [`compile_expr_body`]
  >- (irule (REWRITE_RULE [runtime_data_frame_def]
         runtime_data_frame_expr_body_assembled) >>
      rpt conj_tac >> rpt gen_tac >>
      rewrite_tac[expr_child_callback_def, builtin_child_callback_def,
                  type_child_callback_def] >> BETA_TAC >> IF_CASES_TAC >>
      simp[REWRITE_RULE [runtime_data_frame_def]
        runtime_data_frame_invalid_expr_call])
  >~ [`compile_builtin_dispatch_body`]
  >- (irule (REWRITE_RULE [runtime_data_frame_def]
         runtime_data_frame_builtin_body_assembled) >>
      rpt gen_tac >> rewrite_tac[expr_child_callback_def] >>
      BETA_TAC >> IF_CASES_TAC >>
      simp[REWRITE_RULE [runtime_data_frame_def]
        runtime_data_frame_invalid_expr_call])
  >> gvs[] >> irule (REWRITE_RULE [runtime_data_frame_def]
       runtime_data_frame_type_body_assembled) >>
     rpt gen_tac >> rewrite_tac[expr_child_callback_def] >>
     BETA_TAC >> IF_CASES_TAC >>
     simp[REWRITE_RULE [runtime_data_frame_def]
       runtime_data_frame_invalid_expr_call]
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
