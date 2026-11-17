(* Native child posts converted to resources for actual positive reads. *)
Theory bodyFullAbiEncodeReadResources
Ancestors
  abiEncodeArgsSim abiEncodeMaterialize abiTupleProps abiEncoderWordSource exprSimHyps
  exprSimIfExpWidenedPhysicalType exprSimLayoutTransport bodyPtrDefs
  exprLoweringProps valueCopyBytes valueEncodingTyping loweringPosts
  venomExecSemantics venomState exprSimProps vyperTyping vyperValue compileEnv

Theorem abi_encode_arg_positive_resources:
  expr_body_pre ce cx env e es /\
  expr_post H ctx func ce cx e es0 sa sb s0 ee v op t /\
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  ptr_val_ok cx (post_value_type ce e) v op G tn t /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G t) /\
  (~is_word_type (post_value_type ce e) ==> !w.
    eval_operand op t = SOME w ==>
    type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= t.vs_alloca_next) ==>
  (is_word_type (lowered_value_type ce e) ==>
    abi_tuple_input ce (lowered_value_type ce e) tv v op t /\ op_taint tn op = {}) /\
  (~is_word_type (lowered_value_type ce e) /\
   0 < type_memory_bytes ce (lowered_value_type ce e) ==>
    abi_tuple_input ce (lowered_value_type ce e) tv v op t /\
    ?x w. op = Var x /\ lookup_var x t = SOME w /\
      ptr_covers G tn x t (type_memory_bytes ce (lowered_value_type ce e)) /\
      w2n w + type_memory_bytes ce (lowered_value_type ce e) < dimword(:256) /\
      w2n w + type_memory_bytes ce (lowered_value_type ce e) <= t.vs_alloca_next /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem))
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `is_word_type (lowered_value_type ce e) <=> is_word_type (expr_type e)` by
    metis_tac[compatible_word_type] >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `op_taint tn op = {}` by gvs[ptr_val_ok_def] >>
  conj_tac >- suspend "word" >>
  strip_tac >>
  `~is_word_type (post_value_type ce e)` by metis_tac[post_value_type_nonword] >>
  `?w. eval_operand op t = SOME w` by gvs[expr_val_rel_def] >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory ptv v (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by suspend "layout" >>
  `t.vs_alloca_next < dimword(:256)` by
    metis_tac[expr_post_def, stmt_state_rel_def, alloca_room_next_lt] >>
  `w2n w + type_memory_size tv <= t.vs_alloca_next` by
    gvs[] >>
  `?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + type_memory_size tv <= b+sz` by
    (gvs[ptr_buf_ok_def] >> metis_tac[]) >>
  gvs[abi_tuple_input_def, expr_val_rel_def, ptr_covers_def, eval_operand_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Resume abi_encode_arg_positive_resources[word]:
  strip_tac >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  `abi_tuple_word tv v` by
    (Cases_on `lowered_value_type ce e` >>
     gvs[is_word_type_def] >- 
       (Cases_on `b` >> gvs[is_word_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
        irule abi_encoder_base_word_value >> simp[is_word_type_def]) >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def, abi_tuple_word_def]) >>
  gvs[abi_tuple_input_def, expr_val_rel_def] >> metis_tac[]
QED

Resume abi_encode_arg_positive_resources[layout]:
  `~is_word_type (expr_type e)` by metis_tac[] >>
  drule_all materialize_post_lowered_classify >> strip_tac >- gvs[] >>
  rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
  conj_tac >- simp[] >>
  qexistsl_tac [`post_value_type ce e`, `lowered_value_type ce e`, `get_tenv cx`, `ptv`] >> simp[]
QED

Finalise abi_encode_arg_positive_resources
