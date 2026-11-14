(* Joint execution of the actual word-array membership control blocks. *)
Theory bodyFullBopRestWordControl
Ancestors
  bodyPtrBopInLoopSearch bodyPtrBopInLoopCode bodyPtrBopInLoopLookups
  bodyPtrBopInLoopContract bodyPtrBopInLiteralSuffix bodyPtrBopInScalarTransport
  fragGasEmitCtrl fragGasSeqPtr fragGasOriginPtr stmtAppendStorageRunPtr
  gasEvents gasCount ptrSafeRun memSafeRun instMemFrontier
  ptrDiscipline unitTransformDefs contextCodegenRel codegenRel fragGasOrigin fragGasPathPtr list
  venomExecSemantics venomExecProps venomInst venomState finite_map

Theorem rest_word_membership_condition_compare_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
  s.vs_inst_idx = 0 /\ membership_loop_registers sa i r G tn s /\
  eval_operand len s = SOME (n2w k) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  dst = "%" ++ toString (sa.cs_next_var+2) /\
  ins = mk_inst (sa.cs_next_id+4) EQ
    [Var ("%" ++ toString (sa.cs_next_var+1));len] [dst] /\
  t = update_var dst (bool_to_word ((n2w i:bytes32) = n2w k)) s ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := 1),step_prov PG G ins t,step_taint ins s t tn)
Proof
  strip_tac >> drule_all membership_compiled_condition_lookup >> strip_tac >>
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) s = SOME (n2w i) /\
   op_prov G (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
    fs[membership_loop_registers_def, eval_operand_def] >>
  fs[] >>
  `ptr_inst_ok D lo 0 ctx fn G tn ins s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          mk_inst_def] >>
     conj_tac >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
     conj_tac >- (fs[] >> metis_tac[]) >>
     `step_inst 0 ctx ins s = OK t` by
       simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
            exec_pure2_def, eval_operands_def] >>
     gvs[mk_inst_def, update_var_def, allocas_from_def]) >>
  `step_inst_base ins s = OK t` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >> simp[exec_pure2_def]) >>
  `~is_terminator ins.inst_opcode /\ ins.inst_opcode <> INVOKE /\
   inst_mem_below_frontier ins s /\ inst_dload_in_section ins s` by
    simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME ins` by
    simp[get_instruction_def] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[]
QED

Theorem rest_word_membership_condition_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
  s.vs_inst_idx = 0 /\ membership_loop_registers sa i r G tn s /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  eval_operand len s = SOME (n2w k) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  dst = "%" ++ toString (sa.cs_next_var+2) /\
  ins = mk_inst (sa.cs_next_id+4) EQ
    [Var ("%" ++ toString (sa.cs_next_var+1));len] [dst] /\
  t = update_var dst (bool_to_word ((n2w i:bytes32) = n2w k)) s /\
  G1 = step_prov PG G ins t /\ tn1 = step_taint ins s t tn /\
  target = (if (n2w i:bytes32) = n2w k then
    fresh_label_output "in_exit" (sa.cs_next_label+5) else
    fresh_label_output "in_body" (sa.cs_next_label+2)) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to target t),G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 (jump_to target t) /\
  membership_loop_registers sa i r G1 tn1 (jump_to target t)
Proof
  strip_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := 1),G1,tn1)` by
    (drule_all rest_word_membership_condition_compare_joint >> simp[]) >>
  `tn1 = tn with t_var := tn.t_var |+ (dst,{}) /\
   FLOOKUP G1 dst = NONE /\
   (!p. p <> dst ==> FLOOKUP G1 p = FLOOKUP G p)` by
    suspend "condition_ghost" >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (t with vs_inst_idx := 1,G1,tn1) []
     (OK (jump_to target t),G1,tn1)` by suspend "condition_branch" >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]) >>
  suspend "condition_frame"
QED

Resume rest_word_membership_condition_joint[condition_ghost]:
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) s = SOME (n2w i) /\
   op_prov G (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
    fs[membership_loop_registers_def, eval_operand_def] >>
  fs[] >> conj_tac
  >- (irule membership_scalar_ghost_frame >> simp[]) >>
  conj_tac
  >- (irule membership_scalar_provenance >> simp[]) >>
  rpt strip_tac >> simp[scalar_step_old_prov]
QED

Resume rest_word_membership_condition_joint[condition_branch]:
  drule_all membership_compiled_condition_lookup >> strip_tac >>
  qmatch_goalsub_abbrev_tac `(u,G1,tn1)` >>
  qabbrev_tac `j = mk_inst (sa.cs_next_id+5) JNZ
    [Var dst;Label (fresh_label_output "in_exit" (sa.cs_next_label+5));
     Label (fresh_label_output "in_body" (sa.cs_next_label+2))] []` >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb u.vs_inst_idx = SOME j /\ ~u.vs_halted /\
   allocas_from lo u` by
    (fs[Abbr `u`, Abbr `j`, get_instruction_def, update_var_def, allocas_from_def] >>
     metis_tac[]) >>
  `eval_operand (Var dst) u = SOME
      (if (n2w i:bytes32) = n2w k then 1w else 0w) /\
   op_taint tn1 (Var dst) = {}` by
    (qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
     Cases_on `(n2w i:bytes32) = n2w k` >>
     fs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
          op_taint_def, FLOOKUP_UPDATE, bool_to_word_def]) >>
  `!fuel. step_inst fuel ctx j u = OK (jump_to target t)` by
    suspend "condition_jump_semantics" >>
  `ptr_safe_step D lo 0 ctx fn PG G1 tn1 j u` by
    suspend "condition_jump_checks" >>
  `gas_events_step 0 ctx fn.fn_name j u = [] /\
   gas_count_step 0 ctx j u = 0 /\ mem_safe_step 0 ctx j u /\
   is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE` by
    simp[Abbr `j`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `jump_to target t = jump_to target u` by simp[Abbr `u`, jump_to_def] >>
  `~(jump_to target t).vs_halted` by simp[jump_to_def, update_var_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (u,G1,tn1) [] (OK (jump_to target t),G1,tn1)` by
    (gvs[] >>
     simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >> simp[] >>
     disj2_tac >> disj1_tac >>
     qmatch_goalsub_abbrev_tac `jump_to dest _` >> qexists_tac `dest` >> simp[]) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Resume rest_word_membership_condition_joint[condition_jump_semantics]:
  simp[Abbr `j`, step_inst_non_invoke, mk_inst_def] >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then
    [`fresh_label_output "in_exit" (sa.cs_next_label+5)`,
     `fresh_label_output "in_body" (sa.cs_next_label+2)`,
     `sa.cs_next_id+5`] mp_tac) >>
  Cases_on `(n2w i:bytes32) = n2w k` >>
  gvs[mk_inst_def, Abbr `u`, jump_to_def]
QED

Resume rest_word_membership_condition_joint[condition_jump_checks]:
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `j`, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, jump_to_def] >>
  reverse conj_tac >- simp[Abbr `u`, update_var_def] >>
  qx_gen_tac `x` >> Cases_on `x` >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume rest_word_membership_condition_joint[condition_frame]:
  `(!x. not_fresh_at sa x ==> x <> dst)` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `2` mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
      irule membership_frame_scalar_jump >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G`, `tn`] >>
      qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
      simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
  fs[membership_loop_registers_def, op_prov_def, op_taint_def,
     lookup_var_def] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Finalise rest_word_membership_condition_joint
