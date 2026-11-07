Theory exprSimAbiDecodeValueFrame
Ancestors
  exprSimAbiDecodeStateFrame exprSimAbiDecodeProtection exprSimAbiDecodeLiveFrame
  exprSimAbiDecodeRegionFrame
  exprSimAbiDecodeOutcomeAllocation exprSimAbiDecodeConsumerProbe exprSimAbiDecodeSetupExec
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeEndpointFrame
  abiDecoderSiteEffect actualDecoderSites compileEnv venomState venomMemDefs
  finite_map valueEncodingProps loweringPosts exprLoweringProps exprSimProps
  vyperState vyperTyping vyperTypeABI context valueTypingMemoryProps

Theorem abi_decode_success_value:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  ?v. evaluate_abi_decode env ty bs = INL v /\
      eval_operand out t = SOME (n2w d) /\ val_in_memory tv v d t.vs_memory
Proof
  strip_tac >> gvs[abi_decode_success_closed_def, abi_decode_success_post_def] >>
  Cases_on `out` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_success_old_var:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
  not_fresh_at start x /\ lookup_var x s = SOME w ==>
  lookup_var x t = SOME w
Proof
  strip_tac >> drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  drule_all abi_decode_old_var_frame >> simp[]
QED

Theorem abi_decode_success_old_allocation:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
  FLOOKUP s.vs_allocas aid = SOME row ==>
  FLOOKUP t.vs_allocas aid = SOME row
Proof
  strip_tac >> drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  fs[decode_site_effect_def]
QED

Theorem abi_decode_success_old_memory:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (q,n) /\ aid < start.cs_next_id /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >>
  `q + n <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  `!id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      compileEnv$regions_disjoint b sz q n` by
    (rpt strip_tac >> fs[alloca_inv_def, allocas_non_overlapping_def] >>
     `id <> aid` by decide_tac >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  drule abi_decode_output_site_interval >> strip_tac >>
  qpat_x_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >> gvs[] >>
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

Theorem abi_decode_success_address_bound:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  d < dimword (:256)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas (abi_builtin_decode_output_site start
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)) =
      SOME (d,type_memory_bytes ce ty)` by fs[abi_decode_success_closed_def] >>
  drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  fs[decode_site_effect_def, decode_site_resources_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED

Theorem abi_decode_memory_vv_holds:
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand out t = SOME (n2w d) /\ d < dimword (:256) /\
  val_in_memory tv v d t.vs_memory ==>
  vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr out LocMemory)) es t
Proof
  strip_tac >> simp[vv_holds_def, mk_ptr_def, read_result_def, return_def] >>
  rpt strip_tac >> drule_all val_in_memory_word_type >> simp[]
QED

Theorem abi_decode_success_vv_holds:
  abi_decode_success_closed ce (get_tenv cx) ty tv bs out d start final ctx func s t /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?v. evaluate_abi_decode (get_tenv cx) ty bs = INL v /\
    vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr out LocMemory)) es t
Proof
  strip_tac >> drule abi_decode_success_value >> strip_tac >>
  drule_all evaluate_abi_decode_well_typed >> strip_tac >>
  drule abi_decode_success_address_bound >> strip_tac >>
  qexists_tac `v` >> simp[] >> irule abi_decode_memory_vv_holds >>
  metis_tac[]
QED

Theorem abi_decode_success_singleton_vv_holds:
  abi_decode_success_closed ce (get_tenv cx) (TupleT [ty]) (TupleTV [tv]) bs out d start final
    ctx func s t /\
  evaluate_type (get_tenv cx) (TupleT [ty]) = SOME (TupleTV [tv]) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?v. evaluate_abi_decode (get_tenv cx) (TupleT [ty]) bs = INL (ArrayV (TupleV [v])) /\
    vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr out LocMemory)) es t
Proof
  strip_tac >> drule abi_decode_success_value >> strip_tac >>
  drule_all abi_decode_singleton_endpoint_projection >> strip_tac >> gvs[] >>
  drule abi_decode_success_address_bound >> strip_tac >>
  irule abi_decode_memory_vv_holds >> metis_tac[]
QED

Theorem abi_decode_success_vv_at:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce dec_ty)
    (abi_static_size ce.ce_struct_fields dec_ty) (abi_size_bound ce.ce_struct_fields dec_ty)
    (type_memory_bytes ce dec_ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  alloca_inv s /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce es.scopes s /\
  abi_decode_success_closed ce (get_tenv cx) dec_ty dec_tv bs out d start final ctx func s t /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_size tv <= type_memory_bytes ce dec_ty /\ sa.cs_next_id <= start.cs_next_id ==>
  vv_at ce cx ty sa final es (Value v) (LocatedValue ty (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `val_wf tv v /\ val_footprint tv v <= type_memory_size tv` by
    (drule value_has_type_memory_wf >> strip_tac >> simp[val_footprint_le]) >>
  drule abi_decode_success_value >> strip_tac >>
  drule abi_decode_success_address_bound >> strip_tac >>
  drule abi_decode_output_site_interval >> strip_tac >>
  simp[vv_at_def, mk_ptr_def, read_result_def, return_def] >>
  disj1_tac >>
  qexistsl_tac [`abi_builtin_decode_output_site start
      (abi_static_size ce.ce_struct_fields dec_ty) (abi_size_bound ce.ce_struct_fields dec_ty)`,
      `d`, `type_memory_bytes ce dec_ty`] >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `local_region ce es.scopes s n lb lsz` by
        metis_tac[abi_decode_success_local_region] >>
      drule_all abi_decode_success_output_local_disjoint >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  fs[abi_decode_success_closed_def] >> decide_tac
QED
