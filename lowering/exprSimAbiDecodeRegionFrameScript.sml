Theory exprSimAbiDecodeRegionFrame
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeProtection exprSimAbiDecodeLiveFrame
  exprSimAbiDecodeLocalSeparation exprSimAbiDecodeQuantifiedLift
  exprSimAbiDecodeSetupExec exprSimAbiDecodeEndpointFrame compileEnv finite_map

Theorem abi_decode_local_region_upper:
  local_ptrs_rel fn ce scopes s /\ local_region ce scopes s name q n ==>
  q + n <= s.vs_alloca_next
Proof
  rw[local_region_def] >>
  fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]
QED

Theorem abi_decode_success_local_memory:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce scopes s /\ local_region ce scopes s name q n /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >>
  drule_all abi_decode_local_region_upper >> strip_tac >>
  `!id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      compileEnv$regions_disjoint b sz q n` by
    (rpt gen_tac >> strip_tac >>
     drule abi_decode_lower_interval_local_disjoint >>
     asm_rewrite_tac [] >>
     disch_then drule_all >> simp[]) >>
  drule abi_decode_output_site_interval >> strip_tac >>
  qpat_x_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >>
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `abi_decode_success_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_post_def] >> strip_tac >>
  fs[abi_decode_allocation_floor_def] >>
  `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas u` by
    simp[abi_decode_allocation_floor_def] >>
  qpat_x_assum `decode_site_effect _ _ _ _ _ _` mp_tac >>
  rewrite_tac[GSYM abi_decode_write_set_def] >> strip_tac >>
  irule (SRULE [] abi_decode_write_set_memory_frame) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  conj_tac >- decide_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  goal_assum (drule_at Any) >> asm_rewrite_tac []
QED

Theorem abi_decode_success_output_local_disjoint:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce scopes s /\ local_region ce scopes s name q n /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  compileEnv$regions_disjoint d (type_memory_bytes ce ty) q n
Proof
  strip_tac >>
  drule_all abi_decode_local_region_upper >> strip_tac >>
  `!id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      compileEnv$regions_disjoint b sz q n` by
    (rpt gen_tac >> strip_tac >>
     drule abi_decode_lower_interval_local_disjoint >>
     asm_rewrite_tac [] >> disch_then drule_all >> simp[]) >>
  drule abi_decode_output_site_interval >> strip_tac >>
  fs[abi_decode_success_closed_def] >>
  irule abi_decode_interval_row_separation >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  qexistsl_tac [`s`, `t`] >> asm_rewrite_tac [] >> decide_tac
QED
