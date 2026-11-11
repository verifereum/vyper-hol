(* The raw jumps branch lowering emits, as joint memory and pointer paths:
   no GAS site, the ghost kept, above any bound lo the allocas respect. *)
Theory fragGasOriginJump
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr gasEvents gasCount
  stmtSimProps fragExec ptrSafeRun ptrDiscipline memSafeRun instMemFrontier
  codegenRel contextCodegenRel venomInst venomState venomExecSemantics
  venomExecProofs emitHelper emitHelperProps list

Theorem emit_jump_origin_ptr_path:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  allocas_from lo s ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (OK (jump_to lbl s), G, tn)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `mem_safe_step 0 ctx (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
    (simp[mem_safe_step_non_invoke, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK (jump_to lbl s), G, tn)` by
    (rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def,
                 gas_path_ptr_edge_def] >>
     simp[] >> conj_tac >> qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_events_step_def,
          gas_count_step_def, step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]
QED

Theorem emit_jnz_origin_ptr_path:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []] /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  allocas_from lo s /\
  eval_operand op s = SOME (if b then 1w else 0w) /\
  op_taint tn op = {} ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (OK (jump_to (if b then lt else lf) s), G, tn)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] assume_tac) >>
  `mem_safe_step 0 ctx
     (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s` by
    (simp[mem_safe_step_non_invoke, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jnz_behavior, jump_to_def] >>
     Cases_on `b` >> gvs[op_taint_def] >>
     gen_tac >> Cases_on `op' = op` >> gvs[] >>
     Cases_on `op' = Label lt` >> gvs[] >>
     Cases_on `op' = Label lf` >> gvs[]) >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK (jump_to (if b then lt else lf) s), G, tn)` by
    (rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def,
                 gas_path_ptr_edge_def] >>
     simp[] >> conj_tac >> qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_events_step_def,
          gas_count_step_def, step_jnz_behavior, is_terminator_def] >>
     Cases_on `b` >> gvs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]
QED
