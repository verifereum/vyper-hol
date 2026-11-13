(* Joint control segments for the word-array membership lowering. *)
Theory bodyFullBopRestWordControl
Ancestors
  bodyPtrBopInLoopSearch fragGasEmitCtrl fragGasSeqPtr fragGasOriginPtr
  gasEvents gasCount ptrSafeRun memSafeRun instMemFrontier
  ptrDiscipline unitTransformDefs contextCodegenRel codegenRel fragGasOrigin fragGasPathPtr list
  venomExecSemantics venomExecProps venomInst venomState finite_map

Theorem rest_word_membership_jnz_joint:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op;Label lt;Label lf] []) /\
  eval_operand op s = SOME (bool_to_word b) /\ op_taint tn op = {} ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK (jump_to (if b then lt else lf) s),G,tn)
Proof
  strip_tac >>
  `eval_operand op s = SOME (if b then 1w else 0w)` by
    (Cases_on `b` >> gvs[bool_to_word_def]) >>
  `!fuel. step_inst fuel ctx
      (mk_inst id JNZ [op;Label lt;Label lf] []) s =
      OK (jump_to (if b then lt else lf) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_jnz_behavior >>
     disch_then (qspecl_then [`lt`, `lf`, `id`] mp_tac) >>
     simp[mk_inst_def] >> Cases_on `b` >> simp[]) >>
  `ptr_safe_step D lo 0 ctx fn PG G tn
    (mk_inst id JNZ [op;Label lt;Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          mk_inst_def] >>
     simp[GSYM mk_inst_def, jump_to_def] >>
     qx_gen_tac `x` >> Cases_on `x = op` >> gvs[op_taint_def] >>
     Cases_on `x` >> simp[]) >>
  qabbrev_tac `i = mk_inst id JNZ [op;Label lt;Label lf] []` >>
  `gas_events_step 0 ctx fn.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s /\
   is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK (jump_to (if b then lt else lf) s),G,tn)` by
    (simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >> simp[] >> metis_tac[]) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem rest_word_membership_jump_joint:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst id JMP [Label lbl] []) s =
    OK (jump_to lbl s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_jmp_behavior] >>
  `ptr_safe_step D lo 0 ctx fn PG G tn (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  qabbrev_tac `i = mk_inst id JMP [Label lbl] []` >>
  `gas_events_step 0 ctx fn.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s /\
   is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK (jump_to lbl s),G,tn)` by
    (simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >> simp[] >> metis_tac[]) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem rest_word_membership_eq_check:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  eval_operand a s = SOME aw /\ eval_operand b s = SOME bw /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  op_prov G a = NONE /\ op_prov G b = NONE ==>
  ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id EQ [a;b] [dst]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mk_inst_def] >>
  conj_tac >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  conj_tac >- metis_tac[] >>
  `step_inst 0 ctx (mk_inst id EQ [a;b] [dst]) s =
    OK (update_var dst (bool_to_word (aw = bw)) s)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
         eval_operands_def] >>
  fs[mk_inst_def, update_var_def, allocas_from_def]
QED

Theorem rest_word_membership_eq_joint_edge:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [a;b] [dst]) /\
  eval_operand a s = SOME aw /\ eval_operand b s = SOME bw /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  op_prov G a = NONE /\ op_prov G b = NONE ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (update_var dst (bool_to_word (aw = bw)) s with
           vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst id EQ [a;b] [dst])
       (update_var dst (bool_to_word (aw = bw)) s),
     step_taint (mk_inst id EQ [a;b] [dst]) s
       (update_var dst (bool_to_word (aw = bw)) s) tn)
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id EQ [a;b] [dst]) s` by
    (irule rest_word_membership_eq_check >> metis_tac[]) >>
  `step_inst_base (mk_inst id EQ [a;b] [dst]) s =
    OK (update_var dst (bool_to_word (aw = bw)) s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >> simp[exec_pure2_def]) >>
  `~is_terminator (mk_inst id EQ [a;b] [dst]).inst_opcode /\
   (mk_inst id EQ [a;b] [dst]).inst_opcode <> INVOKE /\
   inst_mem_below_frontier (mk_inst id EQ [a;b] [dst]) s /\
   inst_dload_in_section (mk_inst id EQ [a;b] [dst]) s` by
    simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  drule_all straight_line_origin_ptr_edge >> simp[mk_inst_def]
QED
