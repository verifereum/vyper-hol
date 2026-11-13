(* ABI argument pointer interpretation changes only bytestring capacity.
   The physical source remains the one delivered by expr_sim_ptr. *)
Theory abiEncTuplePtrArgLayout
Ancestors
  abiEncodeMaterialize abiEncodeArgsSim bodyPtrIfExpMemoryTransport
  exprSimIfExp exprSimHyps exprSimLayoutTransport bodyPtrDefs
  loweringPosts compileEnv vyperState vyperAST valueCopyBytes

Theorem abi_args_ptr_lowered_transport:
  expr_body_pre ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v) /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s ==>
  ptr_val_ok cx (lowered_value_type ce e) v op G tn s
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  Cases_on `is_word_type (expr_type e)`
  >- (`is_word_type (lowered_value_type ce e)` by
        metis_tac[compatible_word_type] >>
      gvs[ptr_val_ok_def]) >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[compatible_word_type] >>
  drule_all materialize_post_lowered_classify >> strip_tac >- gvs[] >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, expr_type_def] >> IF_CASES_TAC >> simp[]) >>
  gvs[] >>
  `?sv. evaluate_type (get_tenv cx) (expr_type e) = SOME sv /\
        value_has_type sv v` by
    metis_tac[ifexp_body_pre_read_typed] >>
  gvs[ptr_val_ok_def, is_bytestring_word_type] >>
  irule ptr_mem_ok_bytestring_transport >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
