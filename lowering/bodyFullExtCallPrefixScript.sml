(* Successful optional external-code check: exact checked scalar steps. *)
Theory bodyFullExtCallPrefix
Ancestors
  bodyFullExtCallBoundary bodyFullExtCallPrecheckExit
  exprSimSliceExtcode fragGasSeqPtr fragGasOriginPtr ptrDiscipline
  ptrSafeRun memSafeRun venomInst venomState venomExecSemantics
  emitHelper emitHelperProps exprLoweringProps compileEnv fragExec exprSafeOperand
  instMemFrontier unitTransformDefs codegenRel contextCodegenRel loweringStateRelDefs
  pred_set finite_map

Theorem extcall_extcodesize_exact_edge:
  emit_op EXTCODESIZE [addr] a = (op,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  ~ctx_has_dalloca ctx ==>
  ?out. op = Var out /\ ~not_fresh_at a out /\
    !D lo. allocas_from lo s ==> gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (update_var out
        (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
        with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst a.cs_next_id EXTCODESIZE [addr] [out])
         (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s),
       step_taint (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) s
         (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s) tn)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH a.cs_current_insts) =
    SOME (mk_inst a.cs_next_id EXTCODESIZE [addr]
      [STRING #"%" (toString a.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[not_fresh_at_def] >> rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `v = update_var (STRING #"%" (toString a.cs_next_var))
    (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s` >>
  `step_inst_base inst s = OK v` by
    simp[Abbr `inst`, Abbr `v`, slice_extcodesize_step] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (`inst.inst_opcode <> INVOKE` by simp[Abbr `inst`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke, Abbr `v`, update_var_def] >>
     simp[Abbr `inst`, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[Abbr `inst`, mk_inst_def, Abbr `v`]
QED

Theorem extcall_assert_nonzero_edge:
  emit_void ASSERT [op] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand op s = SOME w /\ w <> 0w /\ op_taint tn op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (s with vs_inst_idx := SUC s.vs_inst_idx),G,tn)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst a.cs_next_id ASSERT [op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  `step_inst_base inst s = OK s` by simp[Abbr `inst`, step_ASSERT_ok] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (`inst.inst_opcode <> INVOKE` by simp[Abbr `inst`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke] >>
     simp[Abbr `inst`, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[Abbr `inst`, mk_inst_def, step_prov_def, set_prov_def,
    step_taint_def, set_var_taint_def, mem_taint_def, step_writes_def,
    imm_taint_def, new_site_bytes_def, EXTENSION, FLOOKUP_DEF, SF CONJ_ss,
    source_memory_write_ranges_def, written_taint_def, store_taint_def,
    adopt_reset_def, range_bytes_def, DRESTRICT_UNIV] >>
  `<|t_mem := tn.t_mem; t_var := tn.t_var; t_stor := tn.t_stor;
     t_trans := tn.t_trans; t_imm := tn.t_imm|> = tn` by
    simp[taint_component_equality] >> simp[]
QED
