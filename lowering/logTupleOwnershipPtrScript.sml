(* Actual allocation-site ownership, including allocations reused in loops. *)
Theory logTupleOwnershipPtr
Ancestors
  localPtrsProps abiDecoderFrame bodyPtrDefs compileEnv exprLoweringProps abiBuiltinAllocation
  logTupleShapePtr abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderArrayFrame
  stmtSimLogTrace emitHelperProps exprSimProps abiDecoderReentry context ASCIInumbers string
  venomMemDefs venomState venomInst finite_map list words arithmetic

Theorem log_alloca_candidate_other_region:
  alloca_inv s /\ id <> site /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas site = SOME (p,cap)) /\
  FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
  abi_footprint_disjoint b sz [(p,cap)]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `(_ /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- (fs[alloca_inv_def, alloca_next_valid_def, abi_footprint_disjoint_def] >>
      disj1_tac >> first_x_assum irule >> metis_tac[]) >>
  fs[alloca_inv_def, allocas_non_overlapping_def, abi_footprint_disjoint_def] >>
  first_x_assum (qspecl_then [`id`,`site`,`b`,`sz`,`p`,`cap`] mp_tac) >> simp[]
QED

Theorem log_alloca_candidate_local_region:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ ~not_fresh_at st q /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas inst.inst_id = SOME (p,cap)) ==>
  !name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz [(p,cap)]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `local_ptrs_rel func ce es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `not_local_ptr ce es.scopes q` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `(_ /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- (`regions_disjoint lo sz p cap` by
        (irule local_ptrs_rel_above_frontier >> metis_tac[LESS_EQ_REFL]) >>
      fs[compileEnvTheory.regions_disjoint_def, abi_footprint_disjoint_def]) >>
  `regions_disjoint p cap lo sz` by
    (irule local_ptrs_rel_alloca_disjoint >> metis_tac[]) >>
  fs[compileEnvTheory.regions_disjoint_def, abi_footprint_disjoint_def] >>
  metis_tac[]
QED

Theorem log_builtin_allocation_candidate:
  t.vs_allocas = (abi_builtin_allocate_state site cap s).vs_allocas /\
  FLOOKUP t.vs_allocas site = SOME (p,cap) ==>
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas site = SOME (p,cap))
Proof
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[FLOOKUP_UPDATE]
QED

Theorem log_tuple_cursor_instruction:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  fn_has_code st end_st func /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_trace >> strip_tac >> gvs[] >>
  drule_all log_tuple_dynamic_prefix_code >> strip_tac >>
  drule_all log_buffer_trace_code >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[]
QED

Theorem log_tuple_cursor_local_region:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  fn_has_code st end_st func /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\
  t.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) ==>
  !name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz [(p,32)]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_tuple_cursor_instruction >> disch_tac >>
  drule_all log_builtin_allocation_candidate >> disch_tac >>
  rpt gen_tac >> disch_tac >>
  irule log_alloca_candidate_local_region >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  qexistsl_tac [`STRING #"%" (toString st.cs_next_var)`,`st`] >>
  asm_simp_tac bool_ss [mk_inst_def] >> simp[not_fresh_at_def]
QED

Theorem log_buffer_registered_local_region:
  compile_alloc_buffer cap st = (buf,prepared) /\ fn_has_code st prepared func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,cap) ==>
  !name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz [(p,cap)]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_buffer_trace_code >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  rpt gen_tac >> disch_tac >> irule log_alloca_candidate_local_region >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  qexistsl_tac [`STRING #"%" (toString st.cs_next_var)`,`st`] >>
  asm_simp_tac bool_ss [mk_inst_def] >> simp[not_fresh_at_def]
QED

Theorem log_allocation_local_regions:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  abi_builtin_allocation_frame st.cs_next_var site cap s t ==>
  !name b sz. (local_region ce es.scopes t name b sz <=>
              local_region ce es.scopes s name b sz)
Proof
  strip_tac >>
  `local_ptrs_rel func ce es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     qpat_x_assum `abi_builtin_allocation_frame _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_builtin_allocation_frame_def] >> strip_tac >>
     first_x_assum (qspec_then `Var x` mp_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, eval_operand_def] >> fs[not_fresh_at_def]) >>
  metis_tac[local_region_frame, local_region_frame_fwd]
QED

Theorem log_local_region_inst_idx[simp]:
  local_region ce scopes (s with vs_inst_idx := k) name b sz <=>
  local_region ce scopes s name b sz
Proof
  simp[local_region_def, lookup_var_def]
QED

Theorem log_one_allocation_protected_bytes:
  alloca_inv s /\ cut <= site /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas site = SOME (p,cap)) /\
  (!name b sz. local_region ce scopes s name b sz ==>
    abi_footprint_disjoint b sz [(p,cap)]) ==>
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < cut /\ off <= i /\ i < off+sz ==>
    abi_footprint_disjoint i 1 [(p,cap)]) /\
  (!name b sz i. local_region ce scopes s name b sz /\ b <= i /\ i < b+sz ==>
    abi_footprint_disjoint i 1 [(p,cap)])
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `aid <> site` by decide_tac >>
      drule_all log_alloca_candidate_other_region >> disch_tac >>
      irule abi_footprint_disjoint_subwindow >>
      qexistsl_tac [`off`,`sz`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule abi_footprint_disjoint_subwindow >>
  qexistsl_tac [`b`,`sz`] >> simp[] >> metis_tac[]
QED

Theorem log_two_allocations_protected_bytes:
  alloca_inv s /\ alloca_inv t /\ cut <= site1 /\ cut <= site2 /\
  abi_builtin_allocation_frame next site1 cap1 s t /\
  ((FLOOKUP s.vs_allocas site1 = NONE /\ p1 = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas site1 = SOME (p1,cap1)) /\
  ((FLOOKUP t.vs_allocas site2 = NONE /\ p2 = t.vs_alloca_next) \/
   FLOOKUP t.vs_allocas site2 = SOME (p2,cap2)) /\
  (!name b sz. local_region ce scopes s name b sz ==>
    abi_footprint_disjoint b sz [(p1,cap1)] /\
    abi_footprint_disjoint b sz [(p2,cap2)]) ==>
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < cut /\ off <= i /\ i < off+sz ==>
    abi_footprint_disjoint i 1 [(p1,cap1);(p2,cap2)]) /\
  (!name b sz i. local_region ce scopes s name b sz /\ b <= i /\ i < b+sz ==>
    abi_footprint_disjoint i 1 [(p1,cap1);(p2,cap2)])
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `aid <> site1 /\ aid <> site2` by decide_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by
        metis_tac[abi_builtin_allocation_frame_outside] >>
      `abi_footprint_disjoint off sz [(p1,cap1)]` by
        (irule log_alloca_candidate_other_region >>
         qexistsl_tac [`aid`,`s`,`site1`] >> asm_simp_tac bool_ss []) >>
      `abi_footprint_disjoint off sz [(p2,cap2)]` by
        (irule log_alloca_candidate_other_region >>
         qexistsl_tac [`aid`,`t`,`site2`] >> asm_simp_tac bool_ss []) >>
      `abi_footprint_disjoint off sz [(p1,cap1);(p2,cap2)]` by
        fs[abi_footprint_disjoint_def] >>
      irule abi_footprint_disjoint_subwindow >>
      qexistsl_tac [`off`,`sz`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `abi_footprint_disjoint b sz [(p1,cap1);(p2,cap2)]` by
    (first_x_assum drule >> simp[abi_footprint_disjoint_def]) >>
  irule abi_footprint_disjoint_subwindow >>
  qexistsl_tac [`b`,`sz`] >> simp[]
QED
