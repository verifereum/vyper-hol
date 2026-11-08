(* Allocation and counted memory interfaces for the checked slice data tail. *)
Theory bodyMemSliceData
Ancestors
  exprSimSliceMemory exprSimSliceData exprSimSliceTerminal builtinBytesMemory allocationPtr
  externalReturnBounds abiBuiltinAllocation allocaFootprint exprSimMemUnwrap
  fragGasSeqMem exprSimHash loweringHalt emitHelperProps exprLoweringProps
  venomMemDefs venomInst list finite_map words

Theorem slice_data_alloc_inst[local]:
  compile_slice_data sl data start len sz sa = (out,sb) /\
  fn_has_code sa sb func ==>
  MEM (mk_inst (sa.cs_next_id + 6) ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString (sa.cs_next_var + 5))]) (fn_insts func)
Proof
  strip_tac >> drule slice_data_decompose >> strip_tac >>
  drule_all slice_data_insts >> strip_tac >>
  drule slice_out_buf_decompose >> strip_tac >>
  drule builtinBytesMemoryTheory.slice_bounds_shape >> strip_tac >>
  `emitted_insts sc sd = emitted_insts sc sm ++ emitted_insts sm sd` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sc sm =
    [mk_inst sc.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sc.cs_next_var)]]` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     CONV_TAC (LHS_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  irule hash_emitted_inst_mem >> qexistsl_tac [`sa`, `sb`] >>
  simp[MEM_APPEND]
QED

Theorem slice_data_allocation_bound[local]:
  compile_slice_data sl data start len sz sa = (out,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  sz < dimword (:256) ==>
  ?p. FLOOKUP (abi_builtin_allocate_state (sa.cs_next_id + 6) sz s).vs_allocas
        (sa.cs_next_id + 6) = SOME (p,sz) /\ p + sz < dimword (:256)
Proof
  strip_tac >> drule_all slice_data_alloc_inst >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas (sa.cs_next_id + 6)`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      qexists_tac `s.vs_alloca_next` >>
      simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
  PairCases_on `x` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
  qexists_tac `x0` >> simp[abi_builtin_allocate_state_def]
QED

Theorem slice_data_body_mem_ok:
  compile_slice_data sl data start len sz sa = (out,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fresh_vars_wrt sa s /\
  eval_operand sl s = SOME l /\ eval_operand data s = SOME d /\
  eval_operand start s = SOME a /\ eval_operand len s = SOME n /\
  w2n d + w2n l <= s.vs_alloca_next /\
  32 + w2n n <= sz /\ sz < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule_all slice_data_allocation_bound >> strip_tac >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  irule compile_slice_data_mem_ok >> goal_assum (drule_at Any) >>
  metis_tac[]
QED
