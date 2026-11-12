Theory bodyFullIfExpSuffix
Ancestors
  fragGasSeqPtr fragGasOriginJump fragGasOriginPtr emitHelper emitHelperProps
  fragExec compileEnv codegenRel contextCodegenRel arithmetic instMemFrontier memSafeRun
  ptrSafeRun ptrDiscipline venomInst venomState venomExecSemantics venomExecProofs

Theorem ifexp_suffix_origin_ptr_path:
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\ ~ctx_has_dalloca ctx /\
  ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\
  allocas_from lo u /\ eval_operand op u = SOME w ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (u,G,tn) []
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)),
     step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u),
     step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn)
Proof
  strip_tac >>
  `sy.cs_blocks = sd.cs_blocks /\ sy.cs_current_bb = sd.cs_current_bb /\
   sy.cs_current_insts = sd.cs_current_insts ++
     [mk_inst sd.cs_next_id ASSIGN [op] [rv]]` by
    metis_tac[emit_inst_extends] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb u.vs_inst_idx =
     SOME (mk_inst sd.cs_next_id ASSIGN [op] [rv])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u =
     OK (update_var rv w u)` by
    simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def,
         comp_bind_def, comp_return_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def,
          comp_bind_def, comp_return_def, update_var_def, allocas_from_def]) >>
  `inst_mem_below_frontier (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `inst_dload_in_section (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u` by
    simp[inst_dload_in_section_def, mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G,tn) []
    (OK (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts),
     step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u),
     step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn)` by
    (`lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     `~is_terminator (mk_inst sd.cs_next_id ASSIGN [op] [rv]).inst_opcode /\
      (mk_inst sd.cs_next_id ASSIGN [op] [rv]).inst_opcode <> INVOKE` by
       simp[mk_inst_def, is_terminator_def] >>
     drule_all straight_line_origin_ptr_edge >>
     simp[mk_inst_def, is_terminator_def, ADD1]) >>
  `sz.cs_blocks = sy.cs_blocks /\ sz.cs_current_bb = sy.cs_current_bb /\
   sz.cs_current_insts = sy.cs_current_insts ++
     [mk_inst sy.cs_next_id JMP [Label xl] []]` by
    metis_tac[emit_inst_extends] >>
  drule (cj 2 gas_origin_ptr_path_rules) >> simp[] >>
  disch_then irule >>
  irule emit_jump_origin_ptr_path >>
  simp[update_var_def, allocas_from_def] >>
  conj_tac >- gvs[allocas_from_def] >>
  qexistsl_tac [`sy`, `sz`] >> simp[]
QED
