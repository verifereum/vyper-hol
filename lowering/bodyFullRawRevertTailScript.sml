Theory bodyFullRawRevertTail
Ancestors
  fragGasSeqPtr fragGasEmitCtrl fragGasOriginPtr fragExec gasEvents gasCount
  ghostPcTransportPtr unitTransformDefs memSafeRun instMemFrontier ptrSafetyTransport contextCodegenRel codegenRel memLocDefs
  ptrSafeRun ptrDiscipline venomExecSemantics venomInstProofs venomInst
  venomState finite_map list arithmetic

Theorem raw_revert_tail_joint_steps:
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\ ~t.vs_halted /\
  get_instruction bb t.vs_inst_idx = SOME i1 /\
  get_instruction bb (SUC t.vs_inst_idx) = SOME i2 /\
  get_instruction bb (SUC (SUC t.vs_inst_idx)) = SOME i3 /\
  i1.inst_opcode = MLOAD /\ i2.inst_opcode = ADD /\ i3.inst_opcode = REVERT /\
  step_inst_base i1 t = OK u /\
  t1 = (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  G1 = step_prov PG G i1 u /\ tn1 = step_taint i1 t u tn /\
  step_inst_base i2 t1 = OK v /\
  t2 = (v with vs_inst_idx := SUC (SUC t.vs_inst_idx)) /\
  G2 = step_prov PG G1 i2 v /\ tn2 = step_taint i2 t1 v tn1 /\
  step_inst_base i3 t2 = Abort Revert_abort w /\
  inst_mem_below_frontier i1 t /\ inst_dload_in_section i1 t /\
  inst_mem_below_frontier i2 t1 /\ inst_dload_in_section i2 t1 /\
  mem_safe_step 0 ctx i3 t2 /\
  ptr_inst_ok D lo 0 ctx func G tn i1 t /\
  ptr_inst_ok D lo 0 ctx func G1 tn1 i2 t1 /\
  ptr_inst_ok D lo 0 ctx func G2 tn2 i3 t2 ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G,tn) [] (Abort Revert_abort w,G2,tn2)
Proof
  strip_tac >>
  `step_inst 0 ctx i1 t = OK u /\ step_inst 0 ctx i2 t1 = OK v` by
    simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `step_inst 0 ctx i1 t = OK u`
       (mp_then Any mp_tac step_preserves_halted) >>
     qpat_assum `step_inst 0 ctx i1 t = OK u`
       (mp_then Any mp_tac step_preserves_control_flow) >>
     simp[is_terminator_def]) >>
  `~t1.vs_halted` by simp[] >>
  `~v.vs_halted /\ v.vs_current_bb = t1.vs_current_bb` by
    (qpat_assum `step_inst 0 ctx i2 t1 = OK v`
       (mp_then Any mp_tac step_preserves_halted) >>
     qpat_assum `step_inst 0 ctx i2 t1 = OK v`
       (mp_then Any mp_tac step_preserves_control_flow) >>
     simp[is_terminator_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (t,G,tn) [] (OK t1,G1,tn1)` by
    (qpat_assum `step_inst_base i1 t = OK u`
       (mp_then Any mp_tac straight_line_origin_ptr_edge) >>
     simp[is_terminator_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (t1,G1,tn1) [] (OK t2,G2,tn2)` by
    (qpat_assum `step_inst_base i2 t1 = OK v`
       (mp_then Any mp_tac straight_line_origin_ptr_edge) >>
     simp[is_terminator_def] >> disch_then irule >>
     simp[] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t2,G2,tn2) [] (Abort Revert_abort w,G2,tn2)` by
    (irule exit_inst_origin_ptr >> simp[exit_result_def] >>
     gvs[step_inst_non_invoke, gas_events_step_def, gas_count_step_def]) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

(* The two computed registers are distinct from the bytes buffer register. *)
Theorem raw_revert_tail_pointer_checks:
  src <> len /\ src <> start /\ len <> start /\
  lookup_var src t = SOME p /\ FLOOKUP G src = SOME (root,sz) /\
  root <= w2n p /\ w2n p + 32 + n <= root + sz /\
  w2n p + 32 < dimword(:256) /\ n < dimword(:256) /\
  mload (w2n p) t = n2w n /\ op_taint tn (Var src) = {} /\
  (!i. w2n p <= i /\ i < w2n p + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo t /\ ~ctx_has_dalloca ctx /\
  i1 = mk_inst id MLOAD [Var src] [len] /\
  i2 = mk_inst (id+1) ADD [Var src; Lit 32w] [start] /\
  i3 = mk_inst (id+2) REVERT [Var start; Var len] [] /\
  t1 = (update_var len (n2w n) t with vs_inst_idx := SUC t.vs_inst_idx) /\
  G1 = step_prov PG G i1 t1 /\ tn1 = step_taint i1 t t1 tn /\
  t2 = (update_var start (p+32w) t1 with vs_inst_idx := SUC t1.vs_inst_idx) /\
  G2 = step_prov PG G1 i2 t2 /\ tn2 = step_taint i2 t1 t2 tn1 ==>
  ptr_inst_ok D lo 0 ctx func G tn i1 t /\
  ptr_inst_ok D lo 0 ctx func G1 tn1 i2 t1 /\
  ptr_inst_ok D lo 0 ctx func G2 tn2 i3 t2
Proof
  strip_tac >> rpt conj_tac
  >- (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def,
           eval_operand_def] >>
      conj_tac
      >- (rpt strip_tac >> gvs[mem_read_ops_def] >>
          qexistsl_tac [`src`, `root`, `sz`] >> simp[] >> decide_tac) >>
      simp[step_inst_non_invoke] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
        instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
      simp[exec_read1_def, eval_operand_def, mload_def, update_var_def])
  >- (gvs[] >> simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
        mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
        step_taint_def, step_prov_def, op_taint_def, set_var_taint_def,
        allocas_from_def, update_var_def, step_inst_non_invoke] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
        instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
      gvs[exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
        FLOOKUP_UPDATE, op_taint_def, allocas_from_def] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `op = Var src` >> gvs[] >>
      Cases_on `op = Lit 32w` >> gvs[] >> metis_tac[])
  >> (gvs[] >> simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      simp[about_to_revert_def, memory_range_of_operands_def,
        eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
        step_prov_def, op_prov_def, mem_read_ops_def] >>
      simp[set_prov_def, out_prov_def, first_prov_def, op_prov_def,
        FLOOKUP_UPDATE, step_inst_non_invoke] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
        instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
      simp[FLOOKUP_DRESTRICT, eval_operand_def, lookup_var_def,
        FLOOKUP_UPDATE, allocas_from_def] >>
      conj_tac
      >- (rpt strip_tac >> `w2n (p + 32w) = w2n p + 32` by
            simp[wordsTheory.w2n_add_2] >> simp[] >> decide_tac) >>
      reverse conj_tac >- metis_tac[allocas_from_def] >>
      simp[step_taint_def, op_taint_def, set_var_taint_def,
        out_taint_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `op = Var start` >> gvs[] >>
      Cases_on `op = Var len` >> gvs[lookup_var_def] >> simp[mem_word_taint_def, pred_setTheory.EXTENSION] >>
      gen_tac >> Cases_on `x < 32` >> simp[] >>
      first_x_assum irule >> decide_tac)
QED

Theorem raw_revert_tail_execution_checks:
  src <> len /\ src <> start /\ len <> start /\
  lookup_var src t = SOME p /\ mload (w2n p) t = n2w n /\
  w2n p + 32 < dimword(:256) /\ n < dimword(:256) /\
  w2n p + 32 + n <= t.vs_alloca_next /\
  i1 = mk_inst id MLOAD [Var src] [len] /\
  i2 = mk_inst (id+1) ADD [Var src; Lit 32w] [start] /\
  i3 = mk_inst (id+2) REVERT [Var start; Var len] [] /\
  u = update_var len (n2w n) t /\
  t1 = (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  v = update_var start (p+32w) t1 /\
  t2 = (v with vs_inst_idx := SUC (SUC t.vs_inst_idx)) /\
  w = revert_state (set_returndata
    (TAKE n (DROP (w2n p + 32) t.vs_memory ++ REPLICATE n 0w)) t2) ==>
  step_inst_base i1 t = OK u /\ step_inst_base i2 t1 = OK v /\
  step_inst_base i3 t2 = Abort Revert_abort w /\
  inst_mem_below_frontier i1 t /\ inst_dload_in_section i1 t /\
  inst_mem_below_frontier i2 t1 /\ inst_dload_in_section i2 t1 /\
  mem_safe_step 0 ctx i3 t2
Proof
  strip_tac >>
  `w2n (p+32w) = w2n p + 32` by simp[wordsTheory.w2n_add_2] >>
  rpt conj_tac
  >- (gvs[] >> simp[mk_inst_def] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
        instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
      simp[exec_read1_def, eval_operand_def])
  >- (gvs[] >> simp[mk_inst_def] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
        instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
      gvs[exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
        FLOOKUP_UPDATE])
  >- (gvs[] >> simp[mk_inst_def] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
        instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
      simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE])
  >- (gvs[] >> simp[below_frontier_MLOAD, eval_operand_def] >> decide_tac)
  >- simp[inst_dload_in_section_def, mk_inst_def]
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def])
  >- simp[inst_dload_in_section_def, mk_inst_def]
  >> simp[mem_safe_step_non_invoke, mk_inst_def,
       inst_dload_in_section_def] >>
     simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* All endpoints and ghosts are fixed before choosing the dead mask D. *)
Theorem raw_revert_tail_joint:
  src <> len /\ src <> start /\ len <> start /\
  lookup_var src t = SOME p /\ FLOOKUP G src = SOME (root,sz) /\
  root <= w2n p /\ w2n p + 32 + n <= root + sz /\
  w2n p + 32 < dimword(:256) /\ n < dimword(:256) /\
  w2n p + 32 + n <= t.vs_alloca_next /\
  mload (w2n p) t = n2w n /\ op_taint tn (Var src) = {} /\
  (!j. w2n p <= j /\ j < w2n p + 32 ==> j NOTIN tn.t_mem) /\
  allocas_from lo t /\ ~ctx_has_dalloca ctx /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\ ~t.vs_halted /\
  get_instruction bb t.vs_inst_idx = SOME i1 /\
  get_instruction bb (SUC t.vs_inst_idx) = SOME i2 /\
  get_instruction bb (SUC (SUC t.vs_inst_idx)) = SOME i3 /\
  i1 = mk_inst id MLOAD [Var src] [len] /\
  i2 = mk_inst (id+1) ADD [Var src; Lit 32w] [start] /\
  i3 = mk_inst (id+2) REVERT [Var start; Var len] [] ==>
  ?w G' tn'. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort w,G',tn')
Proof
  strip_tac >>
  qabbrev_tac `u = update_var len (n2w n) t` >>
  qabbrev_tac `t1 = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `v = update_var start (p+32w) t1` >>
  qabbrev_tac `t2 = v with vs_inst_idx := SUC (SUC t.vs_inst_idx)` >>
  qabbrev_tac `G1 = step_prov PG G i1 u` >>
  qabbrev_tac `tn1 = step_taint i1 t u tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i2 v` >>
  qabbrev_tac `tn2 = step_taint i2 t1 v tn1` >>
  qabbrev_tac `w = revert_state (set_returndata
    (TAKE n (DROP (w2n p + 32) t.vs_memory ++ REPLICATE n 0w)) t2)` >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all raw_revert_tail_execution_checks >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t1 = (update_var len (n2w n) t with vs_inst_idx := SUC t.vs_inst_idx) /\
   t2 = (update_var start (p+32w) t1 with vs_inst_idx := SUC t1.vs_inst_idx) /\
   G1 = step_prov PG G i1 t1 /\ tn1 = step_taint i1 t t1 tn /\
   G2 = step_prov PG G1 i2 t2 /\ tn2 = step_taint i2 t1 t2 tn1` by simp[] >>
  drule_all raw_revert_tail_pointer_checks >>
  disch_tac >> qexistsl_tac [`w`, `G2`, `tn2`] >> gen_tac >>
  first_x_assum (qspecl_then [`func`, `D`] strip_assume_tac) >>
  irule raw_revert_tail_joint_steps >>
  simp[mk_inst_def] >> qexistsl_tac [`u`, `v`] >> gvs[mk_inst_def]
QED
