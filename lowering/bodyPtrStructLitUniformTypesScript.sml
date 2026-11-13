(* Uniform post typing allows bytestring producers with a narrower buffer.
   Well-typedness is essential: an arbitrary AbiEncode annotation need not
   be a bytestring. No syntactic no-internal-call restriction is imposed. *)
Theory bodyPtrStructLitUniformTypes
Ancestors loweringPosts exprLowering vyperAST vyperTypeSystem
  vyperTypeCallGraph compileEnv

Theorem structlit_uniform_nonword_lowered_type:
  !ce e env.
    well_typed_expr env e /\ post_value_type ce e = expr_type e /\
    ~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, post_value_type_def,
       vyperASTTheory.expr_type_def, is_bytestring_type_def,
       vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.type_builtin_result_ok_def] >>
  rpt strip_tac >> gvs[is_bytestring_type_def] >>
  gvs[vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  rpt (pop_assum mp_tac) >> rw[] >> gvs[is_bytestring_type_def]
QED
