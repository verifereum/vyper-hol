Theory exprPtrUnwrapAllocation
Ancestors
  exprPtrUnwrapAllocSeparation fragGasSeqPtr fragExecPtr emitHelperProps
  bufferAllocationExecution exprLoweringProps venomExecSemantics venomInst
  finite_map words list context compileEnv ptrSafeRun ptrDiscipline contextCodegenRel
  venomState fragGasSeqAbort fragGasPathPtr venomInstProofs arithmetic fragExec rich_list

Theorem unwrap_alloc_generated_code:
  compile_alloc_buffer nb sm = (buf,mid) ==>
  ?out. out = STRING #"%" (toString sm.cs_next_var) /\
    buf.buf_operand = Var out /\ buf.buf_size = nb /\
    emitted_insts sm mid =
      [mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]] /\
    mid.cs_current_insts = sm.cs_current_insts ++
      [mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]]
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[]
QED

Theorem unwrap_alloc_generated_step:
  compile_alloc_buffer nb sm = (buf,mid) /\ nb < dimword (:256) ==>
  ?out. buf.buf_operand = Var out /\ buf.buf_size = nb /\
    emitted_insts sm mid =
      [mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]] /\
    step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s =
      OK (update_var out (n2w (buffer_allocation_base s sm.cs_next_id))
        (buffer_allocation_fields s sm.cs_next_id nb))
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  qpat_x_assum `out = _` kall_tac >>
  qexists_tac `out` >> simp[] >>
  drule compile_alloc_buffer_execution >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[run_inst_seq_def] >>
  Cases_on `step_inst_base
    (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s` >>
  simp[run_inst_seq_def]
QED

Theorem unwrap_alloc_ptr_check:
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [out]) s = OK u /\
  u.vs_requests = s.vs_requests ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id ALLOCA [Lit n] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
    codegenRelTheory.source_memory_write_ranges_def,
    source_memory_read_ranges_def, op_taint_def,
    step_inst_non_invoke]
QED

Theorem unwrap_alloc_counted_edge:
  compile_alloc_buffer nb sm = (buf,mid) /\ nb < dimword (:256) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?out u. buf.buf_operand = Var out /\ buf.buf_size = nb /\
    u = update_var out (n2w (buffer_allocation_base s sm.cs_next_id))
          (buffer_allocation_fields s sm.cs_next_id nb) /\
    gas_path_ptr D lo ctx func PG G tn s 0
      (step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u)
      (step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all unwrap_alloc_generated_step >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  qexists_tac `out` >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  qexists_tac `u` >> simp[] >>
  `u.vs_requests = s.vs_requests` by
    (simp[Abbr `u`, buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[Abbr `inst`] >> irule unwrap_alloc_ptr_check >>
     simp[] >> qexists_tac `u` >> simp[]) >>
  `isPREFIX (inst::[]) (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule instruction_prefix_cursor >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS` by simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  `gas_path_ptr_edge D lo ctx func PG G tn s 0
     (step_prov PG G inst u) (step_taint inst s u tn)
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all straight_line_ptr_edge >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    (simp[Abbr `u`, update_var_def, buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]) >>
  metis_tac[gas_path_ptr_rules, ADD_0]
QED

Theorem unwrap_alloc_current_block:
  compile_alloc_buffer nb sm = (buf,mid) ==>
  mid.cs_current_bb = sm.cs_current_bb
Proof
  simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
    comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
    comp_ignore_bind_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem unwrap_alloc_code_prefix:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sm mid) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  drule unwrap_alloc_current_block >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED
