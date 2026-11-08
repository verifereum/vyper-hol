(* Allocation and counted memory interfaces for the checked slice data tail. *)
Theory bodyMemSliceData
Ancestors
  exprSimSliceMemory exprSimSliceData exprSimSliceTerminal builtinBytesMemory allocationPtr
  abiBuiltinAllocation allocaFootprint exprSimMemUnwrap bodyUnopFragMemory fragGasMode
  fragGasSeqMem exprSimHash loweringHalt emitHelperProps exprLoweringProps
  venomMemDefs venomInst list rich_list finite_map words context compileEnv

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

Theorem slice_data_success_path_mem:
  compile_slice_data sl data start len sz sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand sl s = SOME l /\ eval_operand data s = SOME d /\
  eval_operand start s = SOME a /\ eval_operand len s = SOME n /\
  w2n d + w2n l <= s.vs_alloca_next /\
  32 + w2n n <= sz /\ sz < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule slice_data_body_mem_ok >> metis_tac[]) >>
  drule slice_data_control >> strip_tac >>
  drule slice_data_zero_code >> strip_tac >>
  `same_blocks sa sb` by
    (drule slice_data_decompose >> strip_tac >>
     drule slice_out_buf_decompose >> strip_tac >>
     drule (cj 4 builtinBytesMemoryTheory.slice_bounds_shape) >> strip_tac >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     imp_res_tac emit_op_extends >> fs[same_blocks_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem slice_data_abort_path_mem:
  compile_slice_data sl data start len sz sa = (out,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand start s = SOME a /\ eval_operand len s = SOME n /\
  eval_operand sl s = SOME l /\
  (!z. start = Var z ==> not_fresh_at sa z) /\
  (!z. len = Var z ==> not_fresh_at sa z) /\
  (!z. sl = Var z ==> not_fresh_at sa z) /\
  (a+n <+ a \/ l <+ a+n) ==>
  ?t. gas_path_mem ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >> drule_all slice_data_embedding >> strip_tac >>
  drule slice_data_zero_code >> strip_tac >>
  drule slice_data_decompose >> strip_tac >>
  drule_all slice_data_insts >> strip_tac >>
  `isPREFIX (emitted_insts sa sc)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sc)` by
    (fs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    metis_tac[compile_assert_slice_bounds_mem_ok] >>
  drule_all exprSimSliceBoundsTheory.slice_bounds_run >> simp[] >> strip_tac >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >>
  fs[gas_marked_path_def] >> metis_tac[]
QED
