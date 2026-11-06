Theory exprSimAbiEncodeNonwordResources
Ancestors
  exprSimAbiEncodeSiteResources exprSimAbiEncodeProducerBoundary
  loweringPosts exprLoweringProps abiBuiltinAllocation abiBuiltinEncodeCode
  abiEncoderProps compileEnv venomState venomInst finite_map words

Theorem abi_encode_allocate_other_row:
  site <> aid ==>
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas aid =
  FLOOKUP s.vs_allocas aid
Proof
  rw[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_encode_setup_before_body_id:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  aid IN frag_ids ready body_end ==> sa.cs_next_id < aid
Proof
  strip_tac >> drule abi_builtin_encode_setup_shape >>
  Cases_on `mid` >> simp[] >> fs[frag_ids_def]
QED

Theorem abi_encode_nonword_scratch_row:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ eval_operand op s = SOME w /\
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  compile_abi_encode_to_buf dst src ei ready = (out,body_end) /\
  fn_has_code ready body_end obs /\ fn_inst_ids_distinct obs /\
  fn_inst_ids_distinct func /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
       j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  local_ptrs_reserved ce sa /\
  MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id IN frag_ids ready body_end /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id outsz s).vs_allocas inst.inst_id =
    SOME (b,sz) ==>
  sz = 32 /\
  venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz)
Proof
  strip_tac >>
  `sa.cs_next_var <= ready.cs_next_var` by
    (drule abi_builtin_encode_setup_shape >> Cases_on `mid` >> simp[]) >>
  drule_all abi_encode_compiled_scratch_site >>
  disch_then (qspec_then `es'.scopes` strip_assume_tac) >>
  `sa.cs_next_id < inst.inst_id` by metis_tac[abi_encode_setup_before_body_id] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz)` by
    (`sa.cs_next_id <> inst.inst_id` by decide_tac >>
     metis_tac[abi_encode_allocate_other_row]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [expr_post_def] >> strip_tac >>
  `sz = 32` by
    (fs[stmt_state_rel_def] >>
     qpat_x_assum `!inst n base sz. _` drule >> simp[dimword_def]) >>
  simp[] >> irule abi_encode_expr_footprint_site_disjoint >>
  fs[stmt_state_rel_def, state_rel_def] >>
  goal_assum (drule_at Any) >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED
