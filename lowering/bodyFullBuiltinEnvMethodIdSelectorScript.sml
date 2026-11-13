(* Joint two-shift MethodId selector, independent of hashing and allocation. *)
Theory bodyFullBuiltinEnvMethodIdSelector
Ancestors
  vyperStorageFootprint vyperStorageTrace exprSimHash bodyFullGhostFrame fragGasSeqPtr emitHelperProps emitHelper
  exprLoweringProps compileEnv fragExec fragExecMem loweringStateRelDefs
  allocaHistoryFragment instMemFrontier memSafeRun loweringSlice
  contextCodegenRel codegenRel ptrSafeRun bodyPtrDefs ptrDiscipline ptrDisciplineEmptyTaint
  venomState venomInst venomExecSemantics finite_map list rich_list

Theorem method_id_selector_ghosts[local]:
  builtin_result cx acc ann MethodId [ty] [v] = INL r /\
  emit_op SHR [Lit 224w; hash] sa = (sel,sm) /\
  emit_op SHL [Lit 224w; sel] sm = (op,sb) /\
  eval_operand hash s = SOME w /\ op_taint tn hash = {} /\
  op_prov G hash = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)
  ==> ?G' tn'.
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!D lo. ghost_inv_at D lo d cenv cx ee G tn s ==>
      inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
      ghost_inv_at D lo d cenv cx ee G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >>
  gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> gvs[] >>
  qmatch_goalsub_abbrev_tac `mk_inst iid SHR _ [v0]` >>
  qmatch_goalsub_abbrev_tac `mk_inst iid1 SHL _ [v1]` >>
  qexistsl_tac [`DRESTRICT G (COMPL {v0;v1})`,
    `tn with t_var := tn.t_var |+ (v0,{}) |+ (v1,{})`] >>
  `!x. not_fresh_at sa x ==> x <> v0 /\ x <> v1` by
    (simp[Abbr `v0`, Abbr `v1`, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_every >>
      simp[MEM, mk_inst_def, inst_dload_in_section_def] >>
      rpt strip_tac >> irule below_frontier_no_ranges >>
      simp[source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  rpt gen_tac >> strip_tac >>
  fs[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
     mk_inst_def, eval_operands_def, eval_operand_def, lookup_var_def,
     update_var_def, FLOOKUP_UPDATE, combinTheory.UPDATE_def] >>
  gvs[FLOOKUP_UPDATE] >>
  conj_tac >- suspend "pointer" >>
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`, `ee`, `s`, `sa`, `tn`] >>
  gvs[] >> simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    op_taint_def, shift_taint_empty] >> metis_tac[]
QED

Resume method_id_selector_ghosts[pointer]:
  simp[Once inst_seq_ptr_def] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    step_prov_def, out_prov_def, set_prov_def, first_prov_def,
    op_prov_def, step_taint_def, out_taint_def, set_var_taint_def,
    store_taint_def, imm_taint_def, adopt_reset_def] >>
  conj_tac
  >- (fs[ghost_inv_at_def] >>
      simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
        source_memory_read_ranges_def, source_memory_write_ranges_def,
        step_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
        eval_operands_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
        op_taint_def, update_var_def, allocas_from_def] >>
      fs[allocas_from_def] >> gen_tac >> Cases_on `op` >>
      gvs[op_taint_def] >> metis_tac[]) >>
  simp[mem_taint_def, new_site_bytes_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, range_bytes_def,
    FLOOKUP_DEF] >>
  simp[Once inst_seq_ptr_def] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    step_prov_def, out_prov_def, set_prov_def, first_prov_def,
    op_prov_def, FLOOKUP_DRESTRICT, step_taint_def, out_taint_def,
    set_var_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    op_taint_def, shift_taint_empty] >>
  conj_tac
  >- (fs[ghost_inv_at_def] >>
      simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
        source_memory_read_ranges_def, source_memory_write_ranges_def,
        step_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
        eval_operands_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
        op_taint_def, update_var_def, allocas_from_def] >>
      fs[allocas_from_def] >> conj_tac >- (gen_tac >> Cases_on `op` >> simp[] >> metis_tac[]) >> metis_tac[]) >>
  simp[inst_seq_ptr_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, range_bytes_def,
    FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac
  >- (AP_TERM_TAC >> simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[taint_component_equality]
QED
Finalise method_id_selector_ghosts

Theorem method_id_selector_full_run:
  builtin_result cx acc ann MethodId [ty] [v] = INL r /\
  emit_op SHR [Lit 224w; hash] sa = (sel,sm) /\
  emit_op SHL [Lit 224w; sel] sm = (op,sb) /\
  eval_operand hash s = SOME w /\ op_taint tn hash = {} /\
  op_prov G hash = NONE /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ storage_trace_domain cx st0 ee.storage_trace /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s)
  ==> ?t G' tn'.
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    eval_operand op t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
        (BytesV (TAKE 4 (word_to_bytes w T)))) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' t)
Proof
  strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
    (fs[storage_trace_domain_def] >> metis_tac[]) >>
  drule_all method_id_mask_frame >> strip_tac >>
  drule_all method_id_selector_ghosts >>
  disch_then (qspecl_then [`func`, `ee`, `d`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`, `G'`, `tn'`] >>
  suspend "package"
QED

Resume method_id_selector_full_run[package]:
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   LENGTH (emitted_insts sa sb) = 2 /\ sa.cs_next_var <= sb.cs_next_var /\
   (!x. op = Var x ==> not_fresh_at sb x) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[NoAsms, mk_inst_def, is_terminator_def, not_fresh_at_def]) >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)` by metis_tac[LENGTH_APPEND] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >> metis_tac[DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
     simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `t with vs_vars := _ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[eval_operand_inst_idx, lookup_var_def] >>
  conj_tac >- suspend "exterior" >>
  conj_tac >- fs[lookup_var_def] >>
  qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s /\
   storage_well_formed_on cx ee (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx ee G tn s` by metis_tac[] >>
  conj_tac >- suspend "path" >>
  suspend "state"
QED

Resume method_id_selector_full_run[exterior]:
  qpat_x_assum `t with vs_vars := _ = s` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume method_id_selector_full_run[path]:
  `inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by metis_tac[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED
Resume method_id_selector_full_run[state]:
  simp[stmt_state_rel_inst_idx] >>
  drule_all method_id_mask_frame >> strip_tac >>
  gvs[]
QED
Finalise method_id_selector_full_run
