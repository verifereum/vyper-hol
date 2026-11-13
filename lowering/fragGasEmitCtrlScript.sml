(*
 * Zero-mark joint paths of the emitted control instructions (JMP, JNZ,
 * zero-operand abort), stated once for every case of the full body
 * induction that executes them, and the pointer ghosts across a jump.
 *
 * TOP-LEVEL:
 *   emit_jmp_origin_ptr, emit_jnz_origin_ptr, emit_abort_origin_ptr
 *   ghost_inv_at_jump_to
 *)
Theory fragGasEmitCtrl
Ancestors
  bodyPtrDefs fragGasOriginPtr fragGasOrigin fragGasPathPtr gasCount
  gasEvents gasContext emitHelper emitHelperProps fragExec memSafeRun
  ptrSafeRun ptrDiscipline instMemFrontier codegenRel contextCodegenRel
  unitTransformDefs venomExecProps venomExecSemantics venomInst venomState list

(* The gas, memory and pointer facts of one emitted control instruction at
   its block position, as a zero-mark joint edge. *)
val ctrl_edge_tac =
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `0` >> simp[] >> metis_tac[];

Theorem emit_jmp_origin_ptr:
  emit_inst JMP [Label lbl] [] sa = ((), sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (OK (jump_to lbl s), G, tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id JMP [Label lbl] []` >>
  `!fuel. step_inst fuel ctx i s = OK (jump_to lbl s)` by
    simp[Abbr `i`, step_inst_non_invoke, mk_inst_def, step_jmp_behavior] >>
  `gas_events_step 0 ctx func.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s /\
   is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK (jump_to lbl s), G, tn)` by ctrl_edge_tac >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem emit_jnz_origin_ptr:
  emit_inst JNZ [op; Label lt; Label lf] [] sa = ((), sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  eval_operand op s = SOME (if b then 1w else 0w) /\ op_taint tn op = {} /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (OK (jump_to (if b then lt else lf) s), G, tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!fuel. step_inst fuel ctx
      (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s =
      OK (jump_to (if b then lt else lf) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_jnz_behavior >>
     disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] mp_tac) >>
     simp[mk_inst_def] >> Cases_on `b` >> simp[]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          mk_inst_def] >>
     simp[GSYM mk_inst_def, jump_to_def] >>
     qx_gen_tac `x` >> Cases_on `x = op` >> gvs[op_taint_def] >>
     Cases_on `x` >> simp[]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []` >>
  `gas_events_step 0 ctx func.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s /\
   is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK (jump_to (if b then lt else lf) s), G, tn)` by
    ctrl_edge_tac >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

(* ptr_inst_ok_abort_zero at any reserved bound. *)
Theorem ptr_inst_ok_abort_at[local]:
  ((opc = REVERT /\ ops = [Lit 0w; Lit 0w]) \/ (opc = INVALID /\ ops = [])) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id opc ops []) s
Proof
  rpt strip_tac >> gvs[]
  >- (qspecl_then [`id`, `s`] strip_assume_tac step_revert_zero >>
      gvs[mk_inst_def, ptr_inst_ok_def, step_inst_non_invoke] >>
      simp[access_ok_def, taint_ok_def, op_taint_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def,
           memory_range_of_operands_def, eval_operand_def,
           about_to_revert_def] >>
      metis_tac[op_taint_def]) >>
  qspecl_then [`id`, `s`] strip_assume_tac step_invalid >>
  gvs[mk_inst_def, ptr_inst_ok_def, step_inst_non_invoke] >>
  simp[access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def]
QED

Theorem emit_abort_origin_ptr:
  emit_inst opc ops [] sa = ((), sb) /\ fn_has_code sa sb func /\
  ((opc = REVERT /\ ops = [Lit 0w; Lit 0w]) \/ (opc = INVALID /\ ops = [])) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = Abort a t ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (Abort a t, G, tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst sa.cs_next_id opc ops []) s` by
    (irule ptr_inst_ok_abort_at >> simp[]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc ops []` >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS` by
    gvs[Abbr `i`, mk_inst_def] >>
  `ptr_safe_step D lo 0 ctx func PG G tn i s` by
    simp[ptr_safe_step_def] >>
  `!fuel. step_inst fuel ctx i s = Abort a t` by
    simp[step_inst_non_invoke] >>
  `gas_events_step 0 ctx func.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s` by
    gvs[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
        mem_safe_step_non_invoke, inst_mem_below_frontier_def,
        inst_dload_in_section_def, source_memory_read_ranges_def,
        source_memory_write_ranges_def, memory_range_of_operands_def,
        eval_operand_def] >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_def] >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `0` >> simp[exit_result_def]
QED

Theorem ghost_inv_at_jump_to:
  ghost_inv_at D lo d cenv cx (es with gas_obs := gs) G tn (jump_to l s) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >> TRY (PairCases_on `x`) >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

(* Any single exiting instruction with no GAS events and no gas count, at
   the current block position, as a zero-mark joint path. *)
Theorem exit_inst_origin_ptr:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ ~s.vs_halted /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  (!fuel. step_inst fuel ctx i s = r) /\ exit_result r /\
  ptr_inst_ok D lo 0 ctx func G tn i s /\ mem_safe_step 0 ctx i s /\
  gas_events_step 0 ctx func.fn_name i s = [] /\
  gas_count_step 0 ctx i s = 0 ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (r, G, tn)
Proof
  strip_tac >>
  `ptr_safe_step D lo 0 ctx func PG G tn i s` by simp[ptr_safe_step_def] >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[] >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `0` >> simp[] >> metis_tac[]
QED
