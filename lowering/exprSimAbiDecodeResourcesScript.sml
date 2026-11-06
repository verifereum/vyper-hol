Theory exprSimAbiDecodeResources
Ancestors
  exprSimAbiDecodeBoundary exprSimAbiDecodeFootprint
  exprSimAbiDecodeLocalSeparation exprSimAbiDecodeOblivious
  exprSimAbiDecodeCoverageBoundary exprSimAbiDecodeCoverageMutual
  exprSimAbiGasBridge exprLoweringProps localPtrsProps
  exprSimAbiDecodeCoverageActions abiBuiltinDecodeSetup abiBuiltinDecodeCorrect
  abiDecoderAppend actualDecoderSites abiDecoderFrame loweringPosts fragExec venomExecProofs venomInst venomState venomMemDefs compileEnv
  list rich_list finite_map arithmetic words

Theorem abi_decode_resources_code_member:
  cs_extends a z /\ fn_has_code a z fn ==>
  !i. MEM i (frag_code a z) ==> MEM i (fn_insts fn)
Proof
  strip_tac >> gen_tac >>
  Cases_on `NULL (emitted_blocks a z)`
  >- (simp[frag_code_def, emitted_insts_def] >> strip_tac >>
      fs[fn_has_code_def, IS_PREFIX_APPEND] >>
      irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      metis_tac[MEM_DROP_IMP, MEM_APPEND]) >>
  simp[frag_code_def, MEM_APPEND, MEM_FLAT, MEM_MAP] >>
  strip_tac
  >- (irule lookup_block_fn_insts >>
      qexists_tac `LAST (emitted_blocks a z)` >>
      fs[fn_has_code_def] >>
      metis_tac[MEM_LAST_NOT_NIL, NULL_EQ, MEM_DROP_IMP])
  >- (irule lookup_block_fn_insts >>
      fs[fn_has_code_def] >>
      `emitted_blocks a z = FRONT (emitted_blocks a z) ++
          [LAST (emitted_blocks a z)]` by fs[NULL_EQ, APPEND_FRONT_LAST] >>
      metis_tac[MEM_APPEND]) >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[MEM_APPEND]
QED

(* The source is below the frontier and misses every pre-existing decoder site. *)
Theorem abi_decode_caller_source[local]:
  expr_post ctx func ce cx e es st st2 s0 es1 (BytesV bs) data s2 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
  ~is_word_type (expr_type e) /\
  lower_abi_decode data info mn mx outsz st2 = (out,final) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st2 /\
  (!i. MEM i (frag_code st2 final) ==> MEM i (fn_insts func)) ==>
  ?p. eval_operand data s2 = SOME (n2w p) /\
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s2.vs_memory /\
      p + 32 + LENGTH bs <= s2.vs_alloca_next /\
      (!id b sz. st2.cs_next_id <= id /\ id < final.cs_next_id /\
          FLOOKUP s2.vs_allocas id = SOME (b,sz) ==>
          abi_footprint_disjoint (p+32) (LENGTH bs) [(b,sz)])
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es1 s2` by fs[expr_post_def] >>
  `alloca_inv s2 /\ local_ptrs_rel func ce es1.scopes s2` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all abi_decode_bytes_post_footprint >> strip_tac >>
  qexists_tac `p` >> simp[]
  >- (conj_tac
      >- (fs[alloca_inv_def, alloca_next_valid_def] >>
          first_x_assum drule >> decide_tac) >>
      rpt strip_tac >> `aid <> id` by decide_tac >>
      fs[alloca_inv_def, allocas_non_overlapping_def, abi_footprint_disjoint_def] >>
      first_x_assum drule_all >> decide_tac) >>
  conj_tac
  >- (fs[local_ptrs_rel_def, local_region_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac) >>
  rpt strip_tac >> drule_all abi_decode_lower_interval_local_disjoint >>
  simp[compileEnvTheory.regions_disjoint_def, abi_footprint_disjoint_def] >>
  decide_tac
QED

Theorem abi_decode_caller_resources:
  expr_post ctx func ce cx e es st st2 s0 es1 (BytesV bs) data s2 /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  ~is_word_type (expr_type e) /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
    (abi_static_size ce.ce_struct_fields wty)
    (abi_size_bound ce.ce_struct_fields wty)
    (type_memory_bytes ce wty) st2 = (out,final) /\
  fn_has_code st2 final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st2 /\
  abi_size_bound ce.ce_struct_fields wty < dimword (:256) /\
  type_memory_bytes ce wty < dimword (:256) ==>
  ?p d. eval_operand data s2 = SOME (n2w p) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s2.vs_memory /\
    abi_builtin_decode_site_resources ctx func st2 final.cs_next_id
      (abi_static_size ce.ce_struct_fields wty)
      (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) (LENGTH bs) p d s2
Proof
  strip_tac >>
  `cs_extends st2 final` by metis_tac[lower_abi_decode_frag_facts] >>
  `!i. MEM i (frag_code st2 final) ==> MEM i (fn_insts func)` by
    metis_tac[abi_decode_resources_code_member] >>
  `stmt_state_rel ctx func ce cx es1 s2` by fs[loweringPostsTheory.expr_post_def] >>
  `decode_site_resources ctx func s2` by metis_tac[stmt_state_rel_decode_site_resources] >>
  `alloca_inv s2 /\ local_ptrs_rel func ce es1.scopes s2` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all abi_decode_caller_source >> strip_tac >>
  drule abi_decode_lower_output_allocation >> strip_tac >>
  `MEM i (fn_insts func)` by metis_tac[] >>
  `st2.cs_next_id <= i.inst_id /\ i.inst_id < final.cs_next_id` by
    (drule lower_abi_decode_setup_trace >> strip_tac >>
     drule abi_builtin_decode_setup_shape >> strip_tac >>
     `ready.cs_next_id <= final.cs_next_id` by
       (mp_tac abi_decode_id_coverage_mutual >>
        simp[abi_decode_id_coverage_def] >> metis_tac[]) >>
     fs[abi_builtin_decode_output_site_def] >> decide_tac) >>
  Cases_on `FLOOKUP s2.vs_allocas i.inst_id`
  >- (qexistsl_tac [`p`, `s2.vs_alloca_next`] >>
      `s2.vs_alloca_next + type_memory_bytes ce wty < dimword (:256)` by
        (`alloca_room ctx func s2` by fs[decode_site_resources_def] >>
         `i.inst_id NOTIN FDOM s2.vs_allocas` by fs[FLOOKUP_DEF] >>
         drule_all alloca_room_fresh >> simp[]) >>
      simp[exprSimAbiDecodeBuiltinTheory.abi_builtin_decode_site_resources_def,
           abi_footprint_disjoint_def] >>
      fs[abi_footprint_disjoint_def] >>
      conj_tac >- first_assum ACCEPT_TAC >> disj1_tac >> metis_tac[]) >>
  rename1 `FLOOKUP s2.vs_allocas i.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  `entry1 = type_memory_bytes ce wty` by
    (fs[decode_site_resources_def] >>
     qpat_x_assum `!i n b sz. _` drule_all >> simp[]) >>
  `entry0 + entry1 <= s2.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `s2.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> metis_tac[decode_site_resources_def]) >>
  qexistsl_tac [`p`, `entry0`] >>
  simp[exprSimAbiDecodeBuiltinTheory.abi_builtin_decode_site_resources_def] >>
  conj_tac
  >- (qpat_x_assum `!id b sz. _` drule_all >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> metis_tac[]
QED
