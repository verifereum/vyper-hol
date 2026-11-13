(* Joint two-shift MethodId selector, independent of hashing and allocation. *)
Theory bodyFullBuiltinEnvMethodIdSelector
Ancestors
  exprSimHash bodyFullGhostFrame fragGasSeqPtr emitHelperProps emitHelper
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
