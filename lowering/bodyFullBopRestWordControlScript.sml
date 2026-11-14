(* Joint execution of the actual word-array membership control blocks. *)
Theory bodyFullBopRestWordControl
Ancestors
  bodyPtrBopInLoopSearch bodyPtrBopInLoopCode bodyPtrBopInLoopLookups
  bodyPtrBopInLoopContract bodyPtrBopInLiteralSuffix bodyPtrBopInScalarTransport
  fragGasEmitCtrl fragGasSeqPtr fragGasOriginPtr stmtAppendStorageRunPtr
  gasEvents gasCount ptrSafeRun memSafeRun instMemFrontier
  ptrDiscipline unitTransformDefs contextCodegenRel codegenRel fragGasOrigin fragGasPathPtr list
  venomExecSemantics venomExecProps venomInst venomState finite_map

Theorem rest_word_membership_compare_segment_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  lhs = Var ("%" ++ toString (sa.cs_next_var + (if cond_site then 1 else 4+delta+width))) /\
  rhs = (if cond_site then len else needle) /\
  dst = "%" ++ toString (sa.cs_next_var + (if cond_site then 2 else 5+delta+width)) /\
  eid = sa.cs_next_id + (if cond_site then 4 else 8+delta+width) /\
  s.vs_current_bb = fresh_label_output (if cond_site then "in_cond" else "in_body")
    (sa.cs_next_label + (if cond_site then 1 else 2)) /\
  s.vs_inst_idx = (if cond_site then 0 else 2+delta+width) /\
  yes = fresh_label_output (if cond_site then "in_exit" else "in_found")
    (sa.cs_next_label + (if cond_site then 5 else 3)) /\
  no = fresh_label_output (if cond_site then "in_body" else "in_incr")
    (sa.cs_next_label + (if cond_site then 2 else 4)) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  eval_operand lhs s = SOME x /\ eval_operand rhs s = SOME y /\
  op_prov G lhs = NONE /\ op_prov G rhs = NONE /\
  op_taint tn lhs = {} /\ op_taint tn rhs = {} /\
  ins = mk_inst eid EQ [lhs;rhs] [dst] /\
  t = update_var dst (bool_to_word (x=y)) s /\
  G1 = step_prov PG G ins t /\ tn1 = step_taint ins s t tn /\
  u = jump_to (if x=y then yes else no) t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 u /\
  membership_loop_registers sa i r G1 tn1 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME ins /\
     get_instruction bb (SUC s.vs_inst_idx) =
       SOME (mk_inst (eid+1) JNZ [Var dst;Label yes;Label no] [])` by
    suspend "layout" >>
  `(!z. not_fresh_at sa z ==> z <> dst) /\
   dst <> "%" ++ toString (sa.cs_next_var+1) /\
   dst <> "%" ++ toString sa.cs_next_var` by suspend "freshness" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx),G1,tn1)` by
    suspend "compare" >>
  `tn1 = tn with t_var := tn.t_var |+ (dst,{}) /\
   FLOOKUP G1 dst = NONE /\
   (!p. p <> dst ==> FLOOKUP G1 p = FLOOKUP G p)` by
    (qpat_x_assum `tn1 = step_taint _ _ _ _` SUBST1_TAC >>
     qpat_x_assum `G1 = step_prov _ _ _ _` SUBST1_TAC >>
     qpat_x_assum `ins = mk_inst _ _ _ _` SUBST1_TAC >>
     qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
     conj_tac >- (irule membership_scalar_ghost_frame >> simp[]) >>
     conj_tac >- (irule membership_scalar_provenance >> simp[]) >>
     rpt strip_tac >> simp[scalar_step_old_prov]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (t with vs_inst_idx := SUC s.vs_inst_idx,G1,tn1) [] (OK u,G1,tn1)` by
    suspend "branch" >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]) >>
  suspend "frame"
QED

Resume rest_word_membership_compare_segment_joint[layout]:
  Cases_on `cond_site`
  >- (gvs[] >> drule_all membership_compiled_condition_lookup >> strip_tac >>
      qexists_tac `bb` >> simp[get_instruction_def]) >>
  drule_all membership_compiled_compare_lookup >> strip_tac >>
  drule membership_drop_pair_lookup >> strip_tac >>
  qexists_tac `bb` >> gvs[]
QED

Resume rest_word_membership_compare_segment_joint[freshness]:
  conj_tac
  >- (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `if cond_site then 2 else 5+delta+width` mp_tac) >>
      simp[]) >>
  Cases_on `cond_site` >> simp[] >>
  Cases_on `0 < skip` >>
  Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]
QED

Resume rest_word_membership_compare_segment_joint[compare]:
  qpat_x_assum `lhs = _` kall_tac >>
  qpat_x_assum `rhs = _` kall_tac >>
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
  drule_all straight_line_origin_ptr_edge >> simp[]
QED

Resume rest_word_membership_compare_segment_joint[branch]:
  qmatch_goalsub_abbrev_tac `(v,G1,tn1)` >>
  qabbrev_tac `j = mk_inst (eid+1) JNZ [Var dst;Label yes;Label no] []` >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb v.vs_inst_idx = SOME j /\ ~v.vs_halted /\
   allocas_from lo v` by
    (gvs[Abbr `v`, Abbr `j`, update_var_def, allocas_from_def] >> gvs[]) >>
  `eval_operand (Var dst) v = SOME (if x=y then 1w else 0w) /\
   op_taint tn1 (Var dst) = {}` by
    (qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
     Cases_on `x=y` >>
     fs[Abbr `v`, eval_operand_def, lookup_var_def, update_var_def,
          op_taint_def, FLOOKUP_UPDATE, bool_to_word_def]) >>
  `!fuel. step_inst fuel ctx j v = OK u` by suspend "jump_semantics" >>
  `ptr_safe_step D lo 0 ctx fn PG G1 tn1 j v` by suspend "jump_checks" >>
  `gas_events_step 0 ctx fn.fn_name j v = [] /\
   gas_count_step 0 ctx j v = 0 /\ mem_safe_step 0 ctx j v /\
   is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE` by
    simp[Abbr `j`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `u = jump_to (if x=y then yes else no) v` by simp[Abbr `v`, jump_to_def] >>
  `~u.vs_halted` by simp[jump_to_def, update_var_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (v,G1,tn1) [] (OK u,G1,tn1)` by
    (gvs[] >>
     simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >> simp[] >>
     disj2_tac >> disj1_tac >>
     qmatch_goalsub_abbrev_tac `jump_to dest _` >> qexists_tac `dest` >> simp[]) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Resume rest_word_membership_compare_segment_joint[jump_semantics]:
  simp[Abbr `j`, step_inst_non_invoke, mk_inst_def] >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`yes`, `no`, `eid+1`] mp_tac) >>
  Cases_on `x=y` >> gvs[mk_inst_def, Abbr `v`, jump_to_def]
QED

Resume rest_word_membership_compare_segment_joint[jump_checks]:
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `j`, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, jump_to_def] >>
  reverse conj_tac >- simp[Abbr `v`, update_var_def] >>
  qx_gen_tac `z` >> Cases_on `z` >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume rest_word_membership_compare_segment_joint[frame]:
  conj_tac
  >- (qpat_x_assum `u = jump_to _ _` SUBST1_TAC >>
      qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
      irule membership_frame_scalar_jump >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G`, `tn`] >>
      qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
      simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  reverse conj_tac
  >- (fs[jump_to_def, update_var_def, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  qpat_x_assum `u = jump_to _ _` SUBST1_TAC >>
  qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
  fs[membership_loop_registers_def, op_prov_def, op_taint_def, lookup_var_def] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> gvs[]
QED

Finalise rest_word_membership_compare_segment_joint

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
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) s = SOME (n2w i) /\
   op_prov G (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
    fs[membership_loop_registers_def, eval_operand_def] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.GENL [`delta`, `width`, `lhs`, `rhs`, `dst`, `eid`, `yes`, `no`,
             `ins`, `t`, `G1`, `tn1`, `u`]
      (Q.INST [`cond_site` |-> `T`] rest_word_membership_compare_segment_joint))) >>
  strip_tac >> gvs[]
QED
