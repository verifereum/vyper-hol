Theory exprSimAbiEncodeNonwordResources
Ancestors
  loweringStateRelDefs
    exprSimAbiEncodeSiteResources exprSimAbiEncodeProducerBoundary
  loweringPosts exprLoweringProps abiBuiltinAllocation abiBuiltinEncodeCode
  abiEncoderProps exprSimAbiEncodePrefixWindow compileEnv venomMemDefs venomState venomInst finite_map words arithmetic

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
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  ~is_word_type (post_value_type ce e) /\ eval_operand op s = SOME w /\
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

(* The old expression representation is used only at the pre-allocation
   state. A fresh row is above its bounded footprint; a reused row is
   separated by the expression's ownership certificate. *)
Theorem abi_encode_nonword_output_site:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  ~is_word_type (post_value_type ce e) /\ eval_operand op s = SOME w /\
  (0 < val_footprint tv v ==> w2n w + val_footprint tv v <= s.vs_alloca_next) /\
  fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w outsz)] /\ outsz < dimword (:256) /\
  inst.inst_outputs = [q] /\ not_local_ptr ce es'.scopes q /\
  sa.cs_next_id <= inst.inst_id ==>
  let a = abi_builtin_allocate_state inst.inst_id outsz s in
  alloca_inv a /\ alloca_room ctx func a /\
  ?p. FLOOKUP a.vs_allocas inst.inst_id = SOME (p,outsz) /\
      p+outsz <= a.vs_alloca_next /\ a.vs_alloca_next < dimword (:256) /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (p,outsz)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' s` by fs[expr_post_def] >>
  drule_all abi_encode_allocate_resources >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (Cases_on `val_footprint tv v = 0` >>
      gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE,
          venomMemDefsTheory.regions_disjoint_def]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME row` >>
  PairCases_on `row` >>
  `venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (row0,row1)` by
    (irule abi_encode_expr_footprint_site_disjoint >>
     fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[abi_builtin_allocate_state_def]
QED

Theorem abi_encode_nonword_setup_output:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  ~is_word_type (post_value_type ce e) /\ eval_operand op s = SOME w /\
  (0 < val_footprint tv v ==> w2n w + val_footprint tv v <= s.vs_alloca_next) /\
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  fn_has_code sa ready func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  32 + 32 * word_size (maxlen + (case mid of NONE => 0 | SOME _ => 4))
    < dimword (:256) ==>
  let outsz = 32 + 32 * word_size
    (maxlen + (case mid of NONE => 0 | SOME _ => 4)) in
  let a = abi_builtin_allocate_state sa.cs_next_id outsz s in
  alloca_inv a /\ alloca_room ctx func a /\
  ?p. FLOOKUP a.vs_allocas sa.cs_next_id = SOME (p,outsz) /\
      p+outsz <= a.vs_alloca_next /\ a.vs_alloca_next < dimword (:256) /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (p,outsz)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_setup_alloca_code >> strip_tac >>
  drule_at (Pat `MEM _ _`) abi_encode_nonword_output_site >>
  disch_then (irule o SRULE [LET_THM, mk_inst_def]) >>
  simp[] >> metis_tac[local_ptrs_reserved_fresh, arithmeticTheory.LESS_EQ_REFL]
QED

(* Any contained slice of the registered output is disjoint from a
   different allocation row, including empty slices and rows. *)
Theorem abi_encode_output_slice_disjoint:
  alloca_inv a /\
  FLOOKUP a.vs_allocas output_id = SOME (p,outsz) /\
  FLOOKUP a.vs_allocas aid = SOME (b,sz) /\ output_id <> aid /\
  offset+n <= outsz ==>
  venomMemDefs$regions_disjoint (p+offset,n) (b,sz)
Proof
  strip_tac >>
  `p+outsz <= b \/ b+sz <= p` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >>
     first_x_assum drule_all >> simp[]) >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_encode_setup_scratch_slices:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  aid IN frag_ids ready body_end /\ alloca_inv a /\
  FLOOKUP a.vs_allocas sa.cs_next_id = SOME (p,outsz) /\
  FLOOKUP a.vs_allocas aid = SOME (b,sz) /\
  32+m+n <= outsz /\ 32+mw <= outsz ==>
  venomMemDefs$regions_disjoint (p+32+m,n) (b,sz) /\
  venomMemDefs$regions_disjoint (p+32,mw) (b,sz)
Proof
  strip_tac >>
  `sa.cs_next_id <> aid` by
    (drule_all abi_encode_setup_before_body_id >> decide_tac) >>
  conj_tac
  >- (pure_rewrite_tac [GSYM ADD_ASSOC] >>
      irule (Q.INST [`offset` |-> `32+m`] abi_encode_output_slice_disjoint) >>
      qexistsl [`a`, `aid`, `sa.cs_next_id`, `outsz`] >> simp[ADD_ASSOC]) >>
  irule abi_encode_output_slice_disjoint >>
  qexistsl [`a`, `aid`, `sa.cs_next_id`, `outsz`] >> simp[]
QED

Theorem abi_encode_source_method_exclusion:
  venomMemDefs$regions_disjoint (sb,cap) (p,outsz) /\
  0 < cap /\ (mw = 0 \/ mw = 32) /\ 32+mw <= outsz ==>
  sb+cap <= p+32 \/ p+32+mw <= sb
Proof
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED
