(* Argument ownership projected at a registered target site, including empty regions. *)
Theory exprSimAbiEncodeArgsSeparation
Ancestors
  exprSimAbiEncodeTupleProducer exprSimAbiEncodeProducerBoundary
  abiEncodeArgsSim exprSimDefs compileEnv venomMemDefs venomState venomInst
  list rich_list words

Theorem abi_encode_args_value_at:
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s /\
  k < LENGTH args ==>
  expr_val_at ce cx (lowered_value_type ce (EL k args)) sa sb es' (EL k vs) (EL k ops) s
Proof
  strip_tac >> drule abi_args_post_lengths >> strip_tac >>
  fs[abi_args_post_def, LIST_REL_EL_EQN, EL_ZIP] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem abi_encode_args_footprint_site_disjoint:
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s /\
  k < LENGTH args /\
  evaluate_type (get_tenv cx) (lowered_value_type ce (EL k args)) = SOME tv /\
  ~is_word_type (lowered_value_type ce (EL k args)) /\
  eval_operand (EL k ops) s = SOME w /\ alloca_inv s /\
  fn_inst_ids_distinct func /\ local_ptrs_rel func ce es'.scopes s /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce es'.scopes q /\ sb.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (w2n w,val_footprint tv (EL k vs)) (b,sz)
Proof
  strip_tac >> drule_all abi_encode_args_value_at >> strip_tac >>
  drule_all abi_encode_expr_footprint_site_disjoint >> simp[]
QED
