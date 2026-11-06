Theory exprSimAbiEncodeTupleResources
Ancestors
  exprSimAbiEncodeProducerAssembly exprSimAbiEncodePrefixWindow
  exprSimAbiEncodeArgsSeparation abiEncodeEndpointMetadata
  exprSimHash abiEncodeArgsSim abiTupleProps
  exprSimAlloc localPtrsProps abiBuiltinAllocation compileEnv
  exprLoweringProps venomMemDefs venomInst venomState words list finite_map arithmetic

Theorem abi_encode_args_tuple_allocation_resources:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs initial /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) st = (buf,allocated) /\
  fn_has_code st allocated func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce st ==>
  let n = abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) in
  let a = abi_builtin_allocate_state st.cs_next_id n initial in
  ?sb. ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
         FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,n)) /\
    sb+n < dimword (:256) /\ alloca_inv a /\ alloca_room ctx func a /\
    FLOOKUP a.vs_allocas st.cs_next_id = SOME (sb,n) /\ sb+n <= a.vs_alloca_next /\
    a.vs_alloca_next < dimword (:256) /\
    (!k tv w. k < LENGTH args /\
      evaluate_type (get_tenv cx) (expr_type (EL k args)) = SOME tv /\
      ~is_word_type (expr_type (EL k args)) /\ eval_operand (EL k ops) initial = SOME w ==>
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv (EL k vs)) (sb,n))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_args_post_lengths >> strip_tac >>
  `abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) =
    type_memory_bytes ce (TupleT (MAP expr_type args))` by
    simp[abi_tuple_bytes_def, type_memory_bytes_def, MAP_MAP_o, combinTheory.o_DEF, MAP_ZIP] >>
  `abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) < dimword (:256)` by
    (drule abi_encode_endpoint_staging_size >>
     impl_tac >- simp[] >> simp[dimword_def]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' initial` by fs[abi_args_post_def] >>
  drule_at (Pat `MEM _ (fn_insts _)`) abi_encode_allocate_resources >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  disch_then drule >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  first_x_assum (qspec_then `abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexists `p` >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id` >>
      gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
  conj_tac >- decide_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id`
  >- (`p = initial.vs_alloca_next` by
        gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
      drule abi_encode_args_value_at >>
      disch_then (qspec_then `k` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      `alloca_inv initial /\ local_ptrs_rel func ce es'.scopes initial` by
        fs[stmt_state_rel_def, state_rel_def] >>
      drule_all expr_val_at_footprint >> strip_tac
      >- (fs[alloca_inv_def, alloca_next_valid_def,
             venomMemDefsTheory.regions_disjoint_def] >> metis_tac[LESS_EQ_TRANS])
      >- (gvs[local_region_def, local_ptrs_rel_def] >>
          first_x_assum drule_all >> strip_tac >> gvs[lookup_var_def] >>
          simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
      simp[venomMemDefsTheory.regions_disjoint_def]) >>
  `FLOOKUP initial.vs_allocas st.cs_next_id =
    SOME (p,type_memory_bytes ce (TupleT (MAP expr_type args)))` by
    gvs[abi_builtin_allocate_state_def] >>
  `not_local_ptr ce es'.scopes (STRING #"%" (toString st.cs_next_var))` by
    metis_tac[local_ptrs_reserved_fresh, arithmeticTheory.LESS_EQ_REFL] >>
  `alloca_inv initial /\ local_ptrs_rel func ce es'.scopes initial` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`) abi_encode_args_footprint_site_disjoint >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  disch_then (qspecl_then [`w`, `tv`] mp_tac) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspec_then `k` mp_tac) >>
  asm_simp_tac (srw_ss()) []
QED
