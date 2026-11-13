Theory bodyPtrTypeBuiltinsExtract32Saved
Ancestors
  bodyPtrTypeBuiltinsSavedOperand exprSimProps exprBopSimProps
  bodyPtrDefs loweringPosts venomState ptrDiscipline vyperValue compileEnv

Theorem extract32_saved_source_after_offset:
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  expr_post ctx func cenv cx src es0 sa sb s0 es (BytesV bs) (Var sv) s /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
  expr_sim_inv cenv cx env es /\
  expr_post ctx func cenv cx off es sb sc s ee v offop t /\
  ghost_kept cenv es sb G tn s H th /\
  not_fresh_at sb sv /\ not_fresh_at sb len /\ not_fresh_at sb data /\
  eval_operand (Var sv) s = SOME (n2w p) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  op_taint tn (Var sv) = {} /\ op_taint tn (Var len) = {} /\
  op_prov G (Var len) = NONE /\
  (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G tn data s n) ==>
  ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) H th t /\
  eval_operand (Var sv) t = SOME (n2w p) /\
  eval_operand (Var len) t = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) t = SOME (n2w (p+32)) /\
  op_taint th (Var sv) = {} /\ op_taint th (Var len) = {} /\
  op_prov H (Var len) = NONE /\
  (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers H th data t n)
Proof
  strip_tac >>
  `post_value_type cenv src = expr_type src` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `~is_word_type (expr_type src)` by simp[is_word_type_def] >>
  `expr_val_at cenv cx (expr_type src) sa sb es (BytesV bs) (Var sv) s` by
    gvs[expr_post_def] >>
  `!tv. evaluate_type (get_tenv cx) (expr_type src) = SOME tv ==> dynarray_free tv` by
    simp[evaluate_type_def, dynarray_free_base] >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) H th t` by
    (irule saved_ptr_mem_ok >> simp[] >> metis_tac[]) >>
  `!x w. not_fresh_at sb x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    gvs[expr_post_def] >>
  gvs[eval_operand_def, ghost_kept_def, op_prov_def] >>
  rpt conj_tac >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[ptr_covers_def] >> metis_tac[]
QED
