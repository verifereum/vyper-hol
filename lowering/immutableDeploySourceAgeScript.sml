Theory immutableDeploySourceAge
Ancestors
  annassignRelayoutPost
  supportedTypes placeMemoryTypeInterfaces vyperTypeValues valueEncodingProps
  vyperValue valueEncoding vyperTypeSystem immutableDeployAssignRanges
  bodyMemoryDefs stmtSimLogTrace exprSimOperands localPtrsProps stmtSimDefs
  compileEnv loweringStateRelDefs venomMemDefs emitHelperProps ASCIInumbers exprLoweringProps venomInst

Theorem immutable_supported_normalization_positive:
  supported_value_type tops dty /\ type_widens_to tenv sty dty /\
  sty <> dty /\ evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv ==>
  0 < type_memory_size stv /\ 0 < type_memory_size dtv
Proof
  strip_tac >>
  drule_all strict_widening_source_positive >> strip_tac >>
  drule_all type_widens_to_zero_memory_size >> decide_tac
QED

Theorem immutable_rhs_normalization_source_range:
  compile_alloc_buffer cap sa = (buf,mid) /\ fn_has_code sa mid func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel H ctx func ce cx ee s /\
  expr_val_at ce cx sty si sa ee v op s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  0 < type_memory_size stv /\ eval_operand op s = SOME sw ==>
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw)
Proof
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all immutable_assign_nonbytes_source_owned >> strip_tac
  >- gvs[]
  >- (gvs[alloca_inv_def, alloca_next_valid_def, allocas_non_overlapping_def] >>
      conj_tac >- (first_x_assum drule >> decide_tac) >>
      rpt strip_tac >>
      `aid <> sa.cs_next_id` by decide_tac >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac)
  >> `b + sz <= s.vs_alloca_next` by metis_tac[body_local_region_frontier] >>
  conj_tac >- decide_tac >> rpt strip_tac >>
  drule_all log_buffer_trace_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
   inst.inst_id = sa.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `not_local_ptr ce ee.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >>
     simp[not_fresh_at_def, toString_inj]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b',sz')` by simp[] >>
  drule_all alloca_clear_of_locals >> decide_tac
QED
