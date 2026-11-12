(* Counted mapping scratch and dynamic-key continuations. *)
Theory popNestedMappingSuffixMemory
Ancestors
  targetSubscriptMapping bodyAllocMemory bodyDeclMemoryCore exprSimMemUnwrap exprSimMapKey exprSimHash loweringPosts
  allocaFootprint abiBuiltinAllocation venomMemDefs exprSimAlloc context emitHelper fragExec
  bodyMemTbExtract32MemoryTransfer bodyMemBiSha256Compose
  fragGasSeqMem exprSimConcatPath varsExt freshWrites exprSimProps
  instMemFrontier unitTransformDefs contextCodegenRel codegenRel memSafeRun fragExecMem fragGasMode venomExecSemantics
  loweringStateRelDefs emitHelperProps exprLoweringProps exprLowering
  compileEnv venomInst venomState finite_map list rich_list words arithmetic

Theorem pop_nested_mapping_inst_transfer[local]:
  MEM i.inst_opcode [ALLOCA; ADD; MSTORE; SHA3] /\ vars_ext u v /\
  ((?t. step_inst_base i u = OK t) \/ (?a t. step_inst_base i u = Abort a t)) /\
  inst_mem_below_frontier i u /\ inst_dload_in_section i u ==>
  inst_mem_below_frontier i v /\ inst_dload_in_section i v
Proof
  strip_tac >>
  Cases_on `MEM i.inst_opcode [ALLOCA; ADD]`
  >- (gvs[MEM, inst_dload_in_section_def] >>
      irule below_frontier_no_ranges >> simp[]) >>
  gvs[MEM, inst_dload_in_section_def] >>
  gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_write2_def, AllCaseEqs()] >>
  imp_res_tac eval_operand_vars_ext >>
  gvs[vars_ext_def, inst_mem_below_frontier_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def,
      fixed_source_write_range_def, memory_range_of_operands_def] >>
  qpat_x_assum `v = _` SUBST1_TAC >> simp[eval_operand_vars_ext]
QED

Theorem pop_nested_mapping_clean_mem[local]:
  compile_mapping_subscript bop key sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fresh_vars_wrt sa s /\ eval_operand bop s = SOME slot /\
  eval_operand key s = SOME kw ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (`MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
        [STRING #"%" (toString sa.cs_next_var)]) sb.cs_current_insts` by
       gvs[compile_mapping_subscript_def, contextTheory.compile_alloc_buffer_def,
           emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[MEM_APPEND]) >>
  `alloca_next_valid s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, alloca_inv_def] >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  `?p. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 64 s).vs_allocas
       sa.cs_next_id = SOME (p,64)` by
    (simp[alloca_site_cases] >> Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- simp[] >> PairCases_on `x` >> fs[stmt_state_rel_def] >>
     qpat_x_assum `!inst n base sz. _` drule >> simp[mk_inst_def]) >>
  `p + 64 < dimword (:256)` by
    (fs[alloca_site_cases] >-
       (`sa.cs_next_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
        drule alloca_room_fresh >> disch_then drule >> simp[mk_inst_def, dimword_def]) >>
     drule_all alloca_room_next_lt >> fs[alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  irule compile_mapping_subscript_mem_ok >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem pop_nested_mapping_run_mem_ok[local]:
  compile_mapping_subscript bop key sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand key s = SOME kw ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (drop_fresh sa s) /\
   eval_operand bop (drop_fresh sa s) = SOME slot /\
   eval_operand key (drop_fresh sa s) = SOME kw` by
    simp[stmt_state_rel_drop_fresh, eval_operand_drop_fresh] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) (drop_fresh sa s)` by
    (irule pop_nested_mapping_clean_mem >>
     simp[fresh_vars_wrt_drop_fresh] >> metis_tac[]) >>
  drule_at (Pat `compile_mapping_subscript _ _ _ = _`) target_mapping_run >>
  disch_then (qspecl_then [`slot`, `drop_fresh sa s`] mp_tac) >>
  disch_then drule_all >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; MSTORE; SHA3])
      (emitted_insts sa sb)` by
    (qpat_x_assum `compile_mapping_subscript _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[compile_mapping_subscript_def, contextTheory.compile_alloc_buffer_def,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[] >>
     simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[mk_inst_def]) >>
  irule run_inst_seq_mem_ok_total_vars_ext >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule pop_nested_mapping_inst_transfer >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `EVERY _ _` mp_tac >> rpt (pop_assum kall_tac) >>
      simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >>
      simp[MEM, is_terminator_def, is_ext_call_op_def] >>
      strip_tac >> gvs[is_terminator_def, is_ext_call_op_def]) >>
  qexists_tac `drop_fresh sa s` >> simp[vars_ext_drop_fresh] >> metis_tac[]
QED

Theorem pop_nested_mapping_run_path_mem[local]:
  compile_mapping_subscript bop key sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand key s = SOME kw /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule pop_nested_mapping_run_mem_ok >> metis_tac[]) >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[mapping_suffix_shape] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all straight_path_mem >> strip_tac >>
  simp[gas_marked_path_def] >>
  irule sha256_run_inst_seq_alloca_next_mono >>
  qexists_tac `emitted_insts sa sb` >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem pop_nested_mapping_counted_suffix_mem:
  compile_mapping_subscript bop keyop sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es' s /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  wb_frame cenv es es' sa s0 s /\
  (!x. bop = Var x ==> not_fresh_at sm x) /\
  (!x. keyop = Var x ==> not_fresh_at sm x) /\
  eval_operand bop s = SOME slot /\
  eval_operand keyop s = SOME (encode_hashmap_key kt key) /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es' =
    (INL pv, es'') /\
  alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    target_post ctx func cenv cx es sa sb s0 es'' pv vt
      (op,SOME (slot_loc tr),SOME (value_type_place vt)) t /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule_all target_mapping_run >> strip_tac >>
  drule_all pop_nested_mapping_run_path_mem >> strip_tac >>
  `es'' = es'` by metis_tac[target_mapping_extend_place] >> gvs[] >>
  `wb_frame cenv es es' sa s0 t` by
    (irule wb_frame_allocating_tail >> conj_tac >- simp[] >>
     qexistsl_tac [`s`, `es'.scopes`, `sm`] >> simp[] >> metis_tac[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> irule target_mapping_post >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[target_mapping_suffix_shape]
QED
