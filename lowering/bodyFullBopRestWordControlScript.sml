(* Joint execution of the actual word-array membership control blocks. *)
Theory bodyFullBopRestWordControl
Ancestors
  bodyPtrBopInLoopSearch bodyPtrBopInLoopCode bodyPtrBopInLoopLookups bodyPtrBopInLoopLayout
  bodyPtrBopInLoopContract bodyPtrBopInLiteralSuffix bodyPtrBopInScalarTransport
  exprLoweringProps fragExecMem fragGasEmitCtrl fragGasSeqPtr fragGasOriginPtr fragGasOriginPtrLoop stmtAppendStorageRunPtr
  gasEvents gasCount ptrSafeRun memSafeRun instMemFrontier
  ptrDiscipline unitTransformDefs contextCodegenRel codegenRel fragGasOrigin fragGasPathPtr list
  venomExecSemantics venomExecProps venomInst venomState finite_map

Theorem rest_word_membership_segment_compare_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME ins /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (eid+1) JNZ [Var dst;Label yes;Label no] []) /\
  (!z. not_fresh_at sa z ==> z <> dst) /\
  dst <> "%" ++ toString (sa.cs_next_var+1) /\
  dst <> "%" ++ toString sa.cs_next_var /\
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

Resume rest_word_membership_segment_compare_joint[compare]:
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

Resume rest_word_membership_segment_compare_joint[branch]:
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

Resume rest_word_membership_segment_compare_joint[jump_semantics]:
  simp[Abbr `j`, step_inst_non_invoke, mk_inst_def] >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`yes`, `no`, `eid+1`] mp_tac) >>
  Cases_on `x=y` >> gvs[mk_inst_def, Abbr `v`, jump_to_def]
QED

Resume rest_word_membership_segment_compare_joint[jump_checks]:
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `j`, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, jump_to_def] >>
  reverse conj_tac >- simp[Abbr `v`, update_var_def] >>
  qx_gen_tac `z` >> Cases_on `z` >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume rest_word_membership_segment_compare_joint[frame]:
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

Finalise rest_word_membership_segment_compare_joint

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
    (Cases_on `cond_site`
     >- (gvs[] >> drule_all membership_compiled_condition_lookup >> strip_tac >>
         qexists_tac `bb` >> simp[get_instruction_def]) >>
     drule_all membership_compiled_compare_lookup >> strip_tac >>
     drule membership_drop_pair_lookup >> strip_tac >>
     qexists_tac `bb` >> gvs[]) >>
  `(!z. not_fresh_at sa z ==> z <> dst) /\
   dst <> "%" ++ toString (sa.cs_next_var+1) /\
   dst <> "%" ++ toString sa.cs_next_var` by
    (conj_tac
     >- (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
         first_x_assum (qspec_then `if cond_site then 2 else 5+delta+width` mp_tac) >>
         simp[]) >>
     Cases_on `cond_site` >> simp[] >>
     Cases_on `0 < skip` >>
     Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]) >>
  drule_all rest_word_membership_segment_compare_joint >> simp[]
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

Theorem rest_word_membership_segment_found_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME ins /\
  get_instruction bb 1 = SOME (mk_inst (fid+1) JMP
    [Label (fresh_label_output "in_exit" (sa.cs_next_label+5))] []) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3) /\
  s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  dst = "%" ++ toString sa.cs_next_var /\
  ins = mk_inst fid ASSIGN [Lit 1w] [dst] /\
  t = update_var dst 1w s /\
  G1 = DRESTRICT G (COMPL {dst}) /\
  tn1 = tn with t_var := tn.t_var |+ (dst,{}) /\
  u = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5)) t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 u /\
  membership_loop_registers sa i 1w G1 tn1 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME ins` by simp[] >>
  `ptr_inst_ok D lo 0 ctx fn G tn ins s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          mk_inst_def, op_taint_def] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def,
          update_var_def]) >>
  `step_inst_base ins s = OK t /\
   ~is_terminator ins.inst_opcode /\ ins.inst_opcode <> INVOKE /\
   inst_mem_below_frontier ins s /\ inst_dload_in_section ins s` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
         is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  `step_prov PG G ins t = G1 /\ step_taint ins s t tn = tn1` by
    suspend "found_ghost" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := 1),G1,tn1)` by
    (drule_all straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> gvs[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (t with vs_inst_idx := 1,G1,tn1) [] (OK u,G1,tn1)` by
    suspend "found_jump" >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]) >>
  suspend "found_frame"
QED

Resume rest_word_membership_segment_found_joint[found_ghost]:
  simp[mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, step_taint_def,
       mem_taint_def, out_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, op_taint_def, taint_component_equality,
       new_site_bytes_def, step_writes_def, written_taint_def,
       eval_operand_def, update_var_def, range_bytes_def,
       source_memory_write_ranges_def, FLOOKUP_DEF, set_var_taint_def] >>
  SET_TAC[]
QED

Resume rest_word_membership_segment_found_joint[found_jump]:
  qmatch_goalsub_abbrev_tac `(v,G1,tn1)` >>
  qabbrev_tac `j = mk_inst (fid+1) JMP
    [Label (fresh_label_output "in_exit" (sa.cs_next_label+5))] []` >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb v.vs_inst_idx = SOME j /\ ~v.vs_halted /\
   allocas_from lo v` by
    (gvs[Abbr `v`, Abbr `j`, update_var_def, allocas_from_def] >> gvs[]) >>
  `!fuel. step_inst fuel ctx j v = OK u` by
    simp[Abbr `v`, Abbr `j`, step_inst_non_invoke, mk_inst_def,
         step_inst_base_opcode_eqs, jump_to_def] >>
  `ptr_safe_step D lo 0 ctx fn PG G1 tn1 j v` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `j`, source_memory_write_ranges_def,
          source_memory_read_ranges_def, mk_inst_def, op_taint_def] >>
     simp[GSYM mk_inst_def, jump_to_def, Abbr `v`, update_var_def]) >>
  `gas_events_step 0 ctx fn.fn_name j v = [] /\
   gas_count_step 0 ctx j v = 0 /\ mem_safe_step 0 ctx j v /\
   is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE` by
    simp[Abbr `j`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `u = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5)) v` by
    simp[Abbr `v`, jump_to_def] >>
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

Resume rest_word_membership_segment_found_joint[found_frame]:
  conj_tac
  >- (qpat_x_assum `u = jump_to _ _` SUBST1_TAC >>
      qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
      irule membership_frame_scalar_jump >>
      conj_tac
      >- (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
          first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      qexistsl_tac [`G`, `tn`] >>
      simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE]) >>
  gvs[membership_loop_registers_def, jump_to_def, update_var_def,
      lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
      op_prov_def, op_taint_def, allocas_from_def] >> gvs[]
QED

Finalise rest_word_membership_segment_found_joint

Theorem rest_word_membership_found_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3) /\
  s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  dst = "%" ++ toString sa.cs_next_var /\
  ins = mk_inst (sa.cs_next_id+10+delta+width) ASSIGN [Lit 1w] [dst] /\
  t = update_var dst 1w s /\
  G1 = DRESTRICT G (COMPL {dst}) /\
  tn1 = tn with t_var := tn.t_var |+ (dst,{}) /\
  u = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5)) t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 u /\
  membership_loop_registers sa i 1w G1 tn1 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >> drule_all membership_compiled_found_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb 0 = SOME ins /\
   get_instruction bb 1 = SOME (mk_inst (sa.cs_next_id+10+delta+width+1) JMP
     [Label (fresh_label_output "in_exit" (sa.cs_next_label+5))] [])` by
    simp[get_instruction_def] >>
  drule_all rest_word_membership_segment_found_joint >> simp[]
QED

Theorem rest_word_membership_segment_notin_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound F sa = (op,sb) /\
  fn_has_code sa sb fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME ins /\ op = Var dst /\
  (!z. not_fresh_at sa z ==> z <> dst) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = 0 /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  ins = mk_inst eid ISZERO
    [Var ("%" ++ toString sa.cs_next_var)] [dst] /\
  t = update_var dst (bool_to_word (r=0w)) s /\
  G1 = step_prov PG G ins t /\ tn1 = step_taint ins s t tn /\
  u = t with vs_inst_idx := 1 ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 u /\
  eval_operand op u = SOME (bool_to_word (r=0w)) /\
  op_prov G1 op = NONE /\ op_taint tn1 op = {} /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = 1 /\ allocas_from lo u
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME ins` by simp[] >>
  `eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME r /\
   op_prov G (Var ("%" ++ toString sa.cs_next_var)) = NONE /\
   op_taint tn (Var ("%" ++ toString sa.cs_next_var)) = {}` by
    fs[membership_loop_registers_def, eval_operand_def] >>

  `ptr_inst_ok D lo 0 ctx fn G tn ins s` by suspend "checks" >>
  `step_inst_base ins s = OK t` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def] >>
     gvs[eval_operand_def, membership_loop_registers_def]) >>
  `~is_terminator ins.inst_opcode /\ ins.inst_opcode <> INVOKE /\
   inst_mem_below_frontier ins s /\ inst_dload_in_section ins s` by
    simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK u,G1,tn1)` by
    (drule_all straight_line_origin_ptr_edge >> simp[]) >>
  conj_tac
  >- (drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> disch_then irule >>
      irule (cj 1 gas_origin_ptr_path_rules) >>
      simp[update_var_def]) >>
  suspend "post"
QED

Resume rest_word_membership_segment_notin_joint[checks]:
  `step_inst 0 ctx ins s = OK t` by
    (simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure1_def] >>
     gvs[eval_operand_def, membership_loop_registers_def]) >>
  gvs[ptr_inst_ok_def, access_ok_def, taint_ok_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def,
      mk_inst_def, op_prov_def, op_taint_def, update_var_def,
      allocas_from_def, FLOOKUP_DEF] >> first_assum ACCEPT_TAC
QED

Resume rest_word_membership_segment_notin_joint[post]:
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
  conj_tac
  >- (qpat_x_assum `u = _` SUBST1_TAC >>
      qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
      irule bodyPtrBopInElementLoadTheory.membership_frame_scalar_update >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`G`, `tn`] >>
      qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
      simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      op_prov_def, op_taint_def, FLOOKUP_UPDATE, allocas_from_def] >> gvs[]
QED

Finalise rest_word_membership_segment_notin_joint

Theorem rest_word_membership_notin_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE F sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta+width) /\
  ins = mk_inst (sa.cs_next_id+15+delta+width) ISZERO
    [Var ("%" ++ toString sa.cs_next_var)] [dst] /\
  t = update_var dst (bool_to_word (r=0w)) s /\
  G1 = step_prov PG G ins t /\ tn1 = step_taint ins s t tn /\
  u = t with vs_inst_idx := 1 ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 u /\
  eval_operand op u = SOME (bool_to_word (r=0w)) /\
  op_prov G1 op = NONE /\ op_taint tn1 op = {} /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = 1 /\ allocas_from lo u
Proof
  strip_tac >> drule_all membership_compiled_notin_exit_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb 0 = SOME ins` by
    (Cases_on `bb.bb_instructions` >> gvs[get_instruction_def]) >>
  `(!z. not_fresh_at sa z ==> z <> dst)` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `7+delta+width` mp_tac) >> simp[]) >>
  drule membership_compiled_loop_exit >> strip_tac >>
  `op = Var dst` by gvs[] >>
  drule_all rest_word_membership_segment_notin_joint >> simp[]
QED

Theorem rest_word_membership_segment_increment_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME a /\ get_instruction bb 1 = SOME b /\
  get_instruction bb 2 = SOME (mk_inst jid JMP
    [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] []) /\
  dst <> idx /\ dst <> "%" ++ toString sa.cs_next_var /\
  idx <> "%" ++ toString sa.cs_next_var /\
  (!z. not_fresh_at sa z ==> z <> dst /\ z <> idx) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
  s.vs_inst_idx = 0 /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  a = mk_inst aid ADD [Var idx;Lit 1w] [dst] /\
  b = mk_inst bid ASSIGN [Var dst] [idx] /\
  t = update_var dst (n2w (SUC i)) s /\
  G1 = step_prov PG G a t /\ tn1 = step_taint a s t tn /\
  v = update_var idx (n2w (SUC i)) (t with vs_inst_idx := 1) /\
  G2 = step_prov PG G1 b v /\
  tn2 = step_taint b (t with vs_inst_idx := 1) v tn1 /\
  u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) v ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G2,tn2) /\
  membership_loop_frame sa G0 tn0 s0 G2 tn2 u /\
  membership_loop_registers sa (SUC i) r G2 tn2 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME a /\
   get_instruction bb 1 = SOME b` by simp[] >>
  `eval_operand (Var idx) s = SOME (n2w i) /\
   op_prov G (Var idx) = NONE /\ op_taint tn (Var idx) = {}` by
    gvs[membership_loop_registers_def, eval_operand_def] >>

  `step_inst_base a s = OK t /\ step_inst 0 ctx a s = OK t` by
    (simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, eval_operands_def,
          lookup_var_def, GSYM wordsTheory.word_add_n2w, arithmeticTheory.ADD1] >>
     gvs[membership_loop_registers_def, lookup_var_def,
         wordsTheory.word_add_n2w, arithmeticTheory.ADD1]) >>
  `tn1 = tn with t_var := tn.t_var |+ (dst,{}) /\
   FLOOKUP G1 dst = NONE /\
   (!p. p <> dst ==> FLOOKUP G1 p = FLOOKUP G p)` by
    suspend "add_ghost" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := 1),G1,tn1)` by suspend "add_edge" >>
  `step_inst_base b (t with vs_inst_idx := 1) = OK v /\
   step_inst 0 ctx b (t with vs_inst_idx := 1) = OK v` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `tn2 = tn1 with t_var := tn1.t_var |+ (idx,{}) /\
   FLOOKUP G2 idx = NONE /\
   (!p. p <> idx ==> FLOOKUP G2 p = FLOOKUP G1 p)` by
    suspend "assign_ghost" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (t with vs_inst_idx := 1,G1,tn1) []
    (OK (v with vs_inst_idx := 2),G2,tn2)` by suspend "assign_edge" >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (v with vs_inst_idx := 2,G2,tn2) [] (OK u,G2,tn2)` by suspend "jump" >>
  conj_tac
  >- (`gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (t with vs_inst_idx := 1,G1,tn1) [] (OK u,G2,tn2)` by
        (qpat_assum `gas_origin_ptr_edge _ (_ with vs_inst_idx := 1,_,_) _ _`
           (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
         disch_then drule >> simp[]) >>
      qpat_assum `gas_origin_ptr_edge _ (s,G,tn) _ _`
        (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
      disch_then drule >> simp[]) >>
  suspend "frame"
QED

Resume rest_word_membership_segment_increment_joint[add_ghost]:
  qpat_x_assum `tn1 = step_taint _ _ _ _` SUBST1_TAC >>
  qpat_x_assum `G1 = step_prov _ _ _ _` SUBST1_TAC >>
  qpat_x_assum `a = mk_inst _ _ _ _` SUBST1_TAC >>
  qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
  conj_tac
  >- (gvs[mk_inst_def, step_taint_def, mem_taint_def, out_taint_def,
           store_taint_def, adopt_reset_def, imm_taint_def, op_taint_def,
           taint_component_equality, new_site_bytes_def, step_writes_def,
           written_taint_def, eval_operand_def, update_var_def,
           range_bytes_def, source_memory_write_ranges_def,
           FLOOKUP_UPDATE, FLOOKUP_DEF, set_var_taint_def] >> SET_TAC[]) >>
  conj_tac
  >- gvs[mk_inst_def, step_prov_def, out_prov_def, first_prov_def,
          op_prov_def, set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> simp[scalar_step_old_prov]
QED

Resume rest_word_membership_segment_increment_joint[add_edge]:
  `ptr_inst_ok D lo 0 ctx fn G tn a s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          mk_inst_def] >>
     qx_gen_tac `operand` >> Cases_on `operand` >>
     gvs[op_taint_def] >> metis_tac[]) >>
  `~is_terminator a.inst_opcode /\ a.inst_opcode <> INVOKE /\
   inst_mem_below_frontier a s /\ inst_dload_in_section a s` by
    simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  drule_all straight_line_origin_ptr_edge >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> gvs[]
QED

Resume rest_word_membership_segment_increment_joint[assign_ghost]:
  qpat_x_assum `tn2 = step_taint _ _ _ _` SUBST1_TAC >>
  qpat_x_assum `G2 = step_prov _ _ _ _` SUBST1_TAC >>
  qpat_x_assum `b = mk_inst _ _ _ _` SUBST1_TAC >>
  qpat_x_assum `v = update_var _ _ _` SUBST1_TAC >>
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  conj_tac
  >- (simp[mk_inst_def, step_taint_def, mem_taint_def, out_taint_def,
           store_taint_def, adopt_reset_def, imm_taint_def, op_taint_def,
           taint_component_equality, new_site_bytes_def, step_writes_def,
           written_taint_def, eval_operand_def, update_var_def,
           range_bytes_def, source_memory_write_ranges_def,
           FLOOKUP_UPDATE, FLOOKUP_DEF, set_var_taint_def, lookup_var_def] >> SET_TAC[]) >>
  conj_tac
  >- gvs[mk_inst_def, step_prov_def, out_prov_def, first_prov_def,
          op_prov_def, set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> simp[scalar_step_old_prov]
QED

Resume rest_word_membership_segment_increment_joint[assign_edge]:
  `ptr_inst_ok D lo 0 ctx fn G1 tn1 b (t with vs_inst_idx := 1)` by
    (qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
     gvs[ptr_inst_ok_def, access_ok_def, taint_ok_def,
         source_memory_write_ranges_def, source_memory_read_ranges_def,
         mk_inst_def, op_prov_def, op_taint_def, update_var_def,
         FLOOKUP_UPDATE, FLOOKUP_DEF, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `lookup_block (t with vs_inst_idx := 1).vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb (t with vs_inst_idx := 1).vs_inst_idx = SOME b /\
   ~(t with vs_inst_idx := 1).vs_halted /\
   ~is_terminator b.inst_opcode /\ b.inst_opcode <> INVOKE /\
   inst_mem_below_frontier b (t with vs_inst_idx := 1) /\
   inst_dload_in_section b (t with vs_inst_idx := 1)` by
    fs[update_var_def, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  drule_all straight_line_origin_ptr_edge >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> gvs[]
QED

Resume rest_word_membership_segment_increment_joint[jump]:
  qmatch_goalsub_abbrev_tac `(z,G2,tn2)` >>
  qabbrev_tac `j = mk_inst jid JMP
    [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] []` >>
  `lookup_block z.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb z.vs_inst_idx = SOME j /\ ~z.vs_halted /\
   allocas_from lo z` by
    (gvs[Abbr `z`, Abbr `j`, update_var_def, allocas_from_def] >> gvs[]) >>
  `!fuel. step_inst fuel ctx j z = OK u` by
    simp[Abbr `z`, Abbr `j`, step_inst_non_invoke, mk_inst_def,
         step_inst_base_opcode_eqs, jump_to_def] >>
  `ptr_safe_step D lo 0 ctx fn PG G2 tn2 j z` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `j`, source_memory_write_ranges_def,
          source_memory_read_ranges_def, mk_inst_def, op_taint_def] >>
     simp[GSYM mk_inst_def, jump_to_def, Abbr `z`, update_var_def]) >>
  `gas_events_step 0 ctx fn.fn_name j z = [] /\
   gas_count_step 0 ctx j z = 0 /\ mem_safe_step 0 ctx j z /\
   is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE` by
    simp[Abbr `j`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) z` by
    simp[Abbr `z`, jump_to_def] >>
  `~u.vs_halted` by simp[jump_to_def, update_var_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (z,G2,tn2) [] (OK u,G2,tn2)` by
    (gvs[] >>
     simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >> simp[] >>
     disj2_tac >> disj1_tac >>
     qmatch_goalsub_abbrev_tac `jump_to dest _` >> qexists_tac `dest` >> simp[]) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Resume rest_word_membership_segment_increment_joint[frame]:
  `membership_loop_frame sa G0 tn0 s0 G1 tn1 (t with vs_inst_idx := 1)` by
    (qpat_x_assum `t = update_var _ _ _` SUBST1_TAC >>
     irule bodyPtrBopInElementLoadTheory.membership_frame_scalar_update >>
     conj_tac >- metis_tac[] >> qexistsl_tac [`G`,`tn`] >>
     qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
     simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `u = jump_to _ _` SUBST1_TAC >>
      qpat_x_assum `v = update_var _ _ _` SUBST1_TAC >>
      irule membership_frame_scalar_jump >>
      conj_tac >- metis_tac[] >> qexistsl_tac [`G1`,`tn1`] >>
      qpat_x_assum `tn2 = tn1 with t_var := _` SUBST1_TAC >>
      simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qpat_x_assum `tn2 = tn1 with t_var := _` SUBST1_TAC >>
  qpat_x_assum `tn1 = tn with t_var := _` SUBST1_TAC >>
  gvs[membership_loop_registers_def, jump_to_def, update_var_def,
      lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_UPDATE,
      allocas_from_def] >> gvs[]
QED

Finalise rest_word_membership_segment_increment_joint

Theorem rest_word_membership_increment_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
  s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  dst = "%" ++ toString (sa.cs_next_var+6+delta+width) /\
  a = mk_inst (sa.cs_next_id+12+delta+width) ADD [Var idx;Lit 1w] [dst] /\
  b = mk_inst (sa.cs_next_id+13+delta+width) ASSIGN [Var dst] [idx] /\
  t = update_var dst (n2w (SUC i)) s /\
  G1 = step_prov PG G a t /\ tn1 = step_taint a s t tn /\
  v = update_var idx (n2w (SUC i)) (t with vs_inst_idx := 1) /\
  G2 = step_prov PG G1 b v /\
  tn2 = step_taint b (t with vs_inst_idx := 1) v tn1 /\
  u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) v ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G2,tn2) /\
  membership_loop_frame sa G0 tn0 s0 G2 tn2 u /\
  membership_loop_registers sa (SUC i) r G2 tn2 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >> drule_all membership_compiled_increment_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb 0 = SOME a /\ get_instruction bb 1 = SOME b /\
   get_instruction bb 2 = SOME (mk_inst (sa.cs_next_id+14+delta+width) JMP
     [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] [])` by
    simp[get_instruction_def] >>
  `dst <> idx /\ dst <> "%" ++ toString sa.cs_next_var /\
   idx <> "%" ++ toString sa.cs_next_var /\
   (!z. not_fresh_at sa z ==> z <> dst /\ z <> idx)` by
    (conj_tac >- (Cases_on `0 < skip` >>
       Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]) >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `6+delta+width` mp_tac) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  drule_all rest_word_membership_segment_increment_joint >> simp[]
QED

Theorem rest_word_membership_segment_init_prefix_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME old_bb /\
  get_instruction old_bb s.vs_inst_idx = SOME
    (mk_inst sa.cs_next_id JMP [Label (fresh_label_output "in_entry" sa.cs_next_label)] []) /\
  lookup_block e.vs_current_bb fn.fn_blocks = SOME entry_bb /\
  isPREFIX [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
            mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result]] entry_bb.bb_instructions /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  result = "%" ++ toString sa.cs_next_var /\
  e = jump_to (fresh_label_output "in_entry" sa.cs_next_label) s /\
  t = update_var result 0w (update_var idx 0w e) /\
  G2 = DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {result}) /\
  tn2 = tn with t_var := (tn.t_var |+ (idx,{})) |+ (result,{}) /\
  u = (t with vs_inst_idx := 2) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G2,tn2) /\
  membership_loop_frame sa G tn s G2 tn2 u /\
  membership_loop_registers sa 0 0w G2 tn2 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 2 /\ allocas_from lo u
Proof
  strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK e,G,tn)` by
    (qpat_x_assum `e = jump_to _ _` SUBST1_TAC >>
     irule fragGasOriginPtrLoopTheory.jmp_origin_ptr_path >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (e,G,tn) []
     (OK (t with vs_inst_idx := 2),G2,tn2)` by suspend "assigns" >>
  conj_tac
  >- (gvs[] >> metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  suspend "post"
QED

Resume rest_word_membership_segment_init_prefix_joint[assigns]:
  qabbrev_tac `code =
    [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
     mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result]]` >>
  `run_inst_seq code e = OK t` by
    simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
         mk_inst_def, eval_operand_def] >>
  `run_inst_seq_mem_ok code e` by
    (irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
     simp[Abbr `code`, inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def]) >>
  `inst_seq_ptr D lo ctx fn PG G tn code e G2 tn2` by suspend "init_seq_ptr" >>
  `~e.vs_halted /\ e.vs_inst_idx = 0` by simp[jump_to_def] >>
  `isPREFIX code (DROP e.vs_inst_idx entry_bb.bb_instructions) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (conj_tac >- fs[Abbr `code`] >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def]
QED

Resume rest_word_membership_segment_init_prefix_joint[post]:
  simp[membership_loop_frame_def, membership_loop_registers_def,
       jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_prov_def, op_taint_def, allocas_from_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> idx /\ x <> result` by
        (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
         first_assum (qspec_then `0` mp_tac) >>
         first_x_assum (qspec_then `1` mp_tac) >> simp[]) >> gvs[]) >>
  gvs[allocas_from_def]
QED

Resume rest_word_membership_segment_init_prefix_joint[init_seq_ptr]:
  qabbrev_tac `a = mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx]` >>
  qabbrev_tac `b = mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result]` >>
  qabbrev_tac `v = update_var idx 0w e` >>
  qabbrev_tac `q = tn with t_var := tn.t_var |+ (idx,{})` >>
  `step_prov PG G a v = DRESTRICT G (COMPL {idx}) /\
   step_taint a e v tn = q` by suspend "init_first_ghost" >>
  `step_prov PG (DRESTRICT G (COMPL {idx})) b
      (update_var result 0w (v with vs_inst_idx := 1)) = G2 /\
   step_taint b (v with vs_inst_idx := 1)
      (update_var result 0w (v with vs_inst_idx := 1)) q = tn2` by
    suspend "init_second_ghost" >>
  `e.vs_inst_idx = 0` by simp[jump_to_def] >>
  `code = [a;b] /\ step_inst_base a e = OK v /\
   step_inst_base b (v with vs_inst_idx := 1) =
     OK (update_var result 0w (v with vs_inst_idx := 1))` by
    simp[Abbr `code`, Abbr `a`, Abbr `b`, Abbr `v`,
         step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  qpat_x_assum `G2 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `tn2 = tn with t_var := _` kall_tac >>
  qpat_x_assum `code = [a;b]` SUBST1_TAC >>
  pure_once_rewrite_tac [inst_seq_ptr_def] >>
  qpat_assum `step_inst_base a e = _` (fn th => rewrite_tac [th, exec_result_case_def]) >> BETA_TAC >>
  qpat_assum `step_prov PG G a v = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `step_taint a e v tn = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `e.vs_inst_idx = 0` (fn th => rewrite_tac [th]) >>
  simp_tac std_ss [] >>
  pure_once_rewrite_tac [inst_seq_ptr_def] >>
  qpat_assum `step_inst_base b _ = _` (fn th => rewrite_tac [th, exec_result_case_def]) >> BETA_TAC >>
  qpat_assum `step_prov PG _ b _ = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `step_taint b _ _ q = _` (fn th => rewrite_tac [th]) >>
  pure_rewrite_tac [inst_seq_ptr_def] >>

  simp[Abbr `a`, Abbr `b`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       eval_operand_def, Abbr `v`, update_var_def, jump_to_def, allocas_from_def] >>
  gvs[allocas_from_def]
QED

Resume rest_word_membership_segment_init_prefix_joint[init_first_ghost]:
  simp[Abbr `a`, Abbr `v`, Abbr `q`, mk_inst_def,
       step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, step_taint_def,
       mem_taint_def, out_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, op_taint_def, taint_component_equality,
       new_site_bytes_def, step_writes_def, written_taint_def,
       eval_operand_def, update_var_def, range_bytes_def,
       source_memory_write_ranges_def, FLOOKUP_DEF, set_var_taint_def] >> SET_TAC[]
QED

Resume rest_word_membership_segment_init_prefix_joint[init_second_ghost]:
  simp[Abbr `b`, Abbr `q`, Abbr `v`, mk_inst_def,
       step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, step_taint_def,
       mem_taint_def, out_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, op_taint_def, taint_component_equality,
       new_site_bytes_def, step_writes_def, written_taint_def,
       eval_operand_def, update_var_def, range_bytes_def,
       source_memory_write_ranges_def, FLOOKUP_DEF, set_var_taint_def] >> SET_TAC[]
QED

Finalise rest_word_membership_segment_init_prefix_joint

Theorem rest_word_membership_init_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  result = "%" ++ toString sa.cs_next_var /\
  e = jump_to (fresh_label_output "in_entry" sa.cs_next_label) s /\
  t = update_var result 0w (update_var idx 0w e) /\
  G2 = DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {result}) /\
  tn2 = tn with t_var := (tn.t_var |+ (idx,{})) |+ (result,{}) /\
  u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G2,tn2) /\
  membership_loop_frame sa G tn s G2 tn2 u /\
  membership_loop_registers sa 0 0w G2 tn2 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >>
  `?old_bb entry_bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME old_bb /\
    get_instruction old_bb s.vs_inst_idx = SOME
      (mk_inst sa.cs_next_id JMP [Label (fresh_label_output "in_entry" sa.cs_next_label)] []) /\
    lookup_block e.vs_current_bb fn.fn_blocks = SOME entry_bb /\
    entry_bb.bb_instructions =
      [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
       mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result];
       mk_inst (sa.cs_next_id+3) JMP
         [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] []]` by
    (gvs[SRULE [] membership_loop_layout] >>
     fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
     gvs[DISJ_IMP_THM, FORALL_AND_THM, jump_to_def] >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  `isPREFIX [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
             mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result]]
      entry_bb.bb_instructions` by simp[] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := 2),G2,tn2) /\
   membership_loop_frame sa G tn s G2 tn2 (t with vs_inst_idx := 2) /\
   membership_loop_registers sa 0 0w G2 tn2 (t with vs_inst_idx := 2) /\
   ~(t with vs_inst_idx := 2).vs_halted /\
   (t with vs_inst_idx := 2).vs_inst_idx = 2 /\
   allocas_from lo (t with vs_inst_idx := 2)` by
    (irule (Q.GEN `u` rest_word_membership_segment_init_prefix_joint) >>
     metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (t with vs_inst_idx := 2,G2,tn2) [] (OK u,G2,tn2)` by
    (`u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
        (t with vs_inst_idx := 2)` by simp[jump_to_def] >>
     pop_assum SUBST1_TAC >>
     irule fragGasOriginPtrLoopTheory.jmp_origin_ptr_path >>
     simp[update_var_def, jump_to_def, allocas_from_def] >>
     qexistsl_tac [`entry_bb`,`sa.cs_next_id+3`] >>
     gvs[update_var_def, jump_to_def, get_instruction_def]) >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, APPEND] >>
  fs[membership_loop_frame_def, membership_loop_registers_def,
     jump_to_def, update_var_def, allocas_from_def, lookup_var_def] >>
  gvs[] >> first_assum ACCEPT_TAC
QED

(* The finite search uses common, guarded phase endpoints.  Its callbacks
   are the five phases of this membership compilation, not generic edges. *)
Theorem rest_word_membership_segment_search_joint_all:
  !i s Gs Ts.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) bound is_in sa = (op,sb) /\
  (!i s Gs Ts. i <= LENGTH ws /\
    (!H:num. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) ==>
    ?t Gt Tt. !H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if i = LENGTH ws then
        fresh_label_output "in_exit" (sa.cs_next_label+5) else
        fresh_label_output "in_body" (sa.cs_next_label+2))) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H:num. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2)) ==>
    ?t Gt Tt. !H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand loaded t = SOME (EL i ws) /\
      op_prov (Gt H) loaded = NONE /\ op_taint (Tt H) loaded = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H:num. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand loaded s = SOME (EL i ws) /\
      op_prov (Gs H) loaded = NONE /\ op_taint (Ts H) loaded = {}) ==>
    ?t Gt Tt. !H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if EL i ws = w then
        fresh_label_output "in_found" (sa.cs_next_label+3) else
        fresh_label_output "in_incr" (sa.cs_next_label+4))) /\
  (!i s Gs Ts.
    (!H:num. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3)) ==>
    ?t Gt Tt. !H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 1w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)) /\
  (!i s Gs Ts.
    (!H:num. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
      s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4)) ==>
    ?t Gt Tt. !H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa (SUC i) 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) /\
  i <= LENGTH ws /\
  (!H:num. guard H ==>
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
    ~s.vs_halted /\ allocas_from lo s /\ s.vs_inst_idx = 0 /\
    s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)) ==>
  ?t Gt Tt j. !H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa j (bool_to_word (MEM w (DROP i ws))) (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  measureInduct_on `LENGTH ws-i` >> rpt strip_tac >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H:num. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ t.vs_current_bb = (if j = LENGTH ws then _ else _)`
    (mk_asm "condition") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H:num. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ t.vs_current_bb = (if EL j ws = w then _ else _)`
    (mk_asm "compare") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H:num. guard H ==> _ /\ _ /\ membership_loop_registers sa (SUC j) _ _ _ _ /\ _`
    (mk_asm "increment") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H:num. guard H ==> _ /\ _ /\ membership_loop_registers sa j 1w _ _ _ /\ _`
    (mk_asm "found") >>
  qpat_x_assum `!j u Gu Tu. _ ==> ?t Gt Tt. !H:num. guard H ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ eval_operand loaded t = _ /\ _`
    (mk_asm "load") >>
  asm "condition" (qspecl_then [`i`,`s`,`Gs`,`Ts`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `cs` (qx_choose_then `CG` (qx_choose_then `CT` assume_tac))) >>
  Cases_on `i = LENGTH ws`
  >- (qexistsl_tac [`cs`,`CG`,`CT`,`i`] >> gvs[bool_to_word_def] >> metis_tac[]) >>
  `i < LENGTH ws` by decide_tac >>
  asm "load" (qspecl_then [`i`,`cs`,`CG`,`CT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h:num. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `ls` (qx_choose_then `LG` (qx_choose_then `LTs` assume_tac))) >>
  asm "compare" (qspecl_then [`i`,`ls`,`LG`,`LTs`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h:num. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `bs` (qx_choose_then `BG` (qx_choose_then `BT` assume_tac))) >>
  `DROP i ws = EL i ws :: DROP (SUC i) ws` by
    metis_tac[rich_listTheory.DROP_CONS_EL] >>
  Cases_on `EL i ws = w`
  >- suspend "hit" >>
  suspend "miss"
QED

Resume rest_word_membership_segment_search_joint_all[hit]:
  asm "found" (qspecl_then [`i`,`bs`,`BG`,`BT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h:num. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `fin` (qx_choose_then `GF` (qx_choose_then `TF` assume_tac))) >>
  qexistsl_tac [`fin`,`GF`,`TF`,`i`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!y. LENGTH ws-y < _ ==> _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  simp[bool_to_word_def] >>
  metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Resume rest_word_membership_segment_search_joint_all[miss]:
  asm "increment" (qspecl_then [`i`,`bs`,`BG`,`BT`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    rpt (qpat_x_assum `!h:num. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> gvs[])) >>
  disch_then (qx_choose_then `is` (qx_choose_then `IG` (qx_choose_then `IT` assume_tac))) >>
  qpat_x_assum `!y. LENGTH ws-y < _ ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`is`,`IG`,`IT`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- asm "condition" ACCEPT_TAC >>
    conj_tac >- asm "load" ACCEPT_TAC >>
    conj_tac >- asm "compare" ACCEPT_TAC >>
    conj_tac >- asm "found" ACCEPT_TAC >>
    conj_tac >- asm "increment" ACCEPT_TAC >>
    conj_tac >- decide_tac >>
    gen_tac >> disch_tac >>
    rpt (qpat_x_assum `!h:num. guard h ==> _`
      (qspec_then `H` (drule_then strip_assume_tac))) >> simp[])) >>
  disch_then (qx_choose_then `fin` (qx_choose_then `GF` (qx_choose_then `TF`
    (qx_choose_then `j` assume_tac)))) >>
  qexistsl_tac [`fin`,`GF`,`TF`,`j`] >> gen_tac >> disch_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  simp[] >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

Finalise rest_word_membership_segment_search_joint_all

Theorem rest_word_membership_search_suffix_joint_all:
  !i s Gs Ts.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  (!H:num. guard H ==>
    eval_operand needle s0 = SOME w /\ op_prov (G0 H) needle = NONE /\
    op_taint (T0 H) needle = {} /\
    eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
    op_prov (G0 H) len = NONE /\ op_taint (T0 H) len = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H:num. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov (Gt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint (Tt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}) /\
  i <= LENGTH ws /\
  (!H:num. guard H ==>
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
    membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
    ~s.vs_halted /\ allocas_from lo s /\
    s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    s.vs_inst_idx = 0) ==>
  ?t Gt Tt j. !H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    membership_loop_registers sa j (bool_to_word (MEM w (DROP i ws))) (Gt H) (Tt H) t /\
    ~t.vs_halted /\ allocas_from lo t /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)
Proof
  rpt strip_tac >>
  qspecl_then [`i`,`s`,`Gs`,`Ts`] mp_tac
    (Q.INST [`bound` |-> `NONE`,
      `loaded` |-> `Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))`]
      rest_word_membership_segment_search_joint_all) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- suspend "condition" >>
    conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
    conj_tac >- suspend "compare" >>
    conj_tac >- suspend "found" >>
    conj_tac >- suspend "increment" >>
    simp[] >> metis_tac[])) >>
  disch_then ACCEPT_TAC
QED

Resume rest_word_membership_search_suffix_joint_all[condition]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `ci = mk_inst (sa.cs_next_id+4) EQ
    [Var ("%" ++ toString (sa.cs_next_var+1));len]
    ["%" ++ toString (sa.cs_next_var+2)]` >>
  qabbrev_tac `cv = update_var ("%" ++ toString (sa.cs_next_var+2))
    (bool_to_word ((n2w j:bytes32) = n2w (LENGTH ws))) u` >>
  qabbrev_tac `cs = jump_to (if (n2w j:bytes32) = n2w (LENGTH ws) then
    fresh_label_output "in_exit" (sa.cs_next_label+5) else
    fresh_label_output "in_body" (sa.cs_next_label+2)) cv` >>
  qabbrev_tac `CG = \H:num. step_prov PG (Gu H) ci cv` >>
  qabbrev_tac `CT = \H:num. step_taint ci u cv (Tu H)` >>
  qexistsl_tac [`cs`,`CG`,`CT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `eval_operand len u = SOME (n2w (LENGTH ws)) /\
   op_prov (Gu H) len = NONE /\ op_taint (Tu H) len = {}` by
    metis_tac[membership_loop_frame_operand] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK cs,CG H,CT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (CG H) (CT H) cs /\
   membership_loop_registers sa j 0w (CG H) (CT H) cs` by
    (map_every qunabbrev_tac [`CG`,`CT`,`cs`,`cv`,`ci`] >> BETA_TAC >>
     irule (SIMP_RULE bool_ss [] (Q.GENL [`dst`,`ins`,`t`,`G1`,`tn1`,`target`]
       rest_word_membership_condition_joint)) >> metis_tac[]) >>
  `j < dimword (:256)` by decide_tac >>
  simp[] >> gvs[Abbr `cs`, Abbr `cv`, jump_to_def, update_var_def,
    allocas_from_def, wordsTheory.n2w_11] >> first_assum ACCEPT_TAC
QED
Resume rest_word_membership_search_suffix_joint_all[compare]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `bi = mk_inst (sa.cs_next_id+(8+delta+width)) EQ
    [Var ("%" ++ toString (sa.cs_next_var+(4+delta+width)));needle]
    ["%" ++ toString (sa.cs_next_var+(5+delta+width))]` >>
  qabbrev_tac `bv = update_var ("%" ++ toString (sa.cs_next_var+(5+delta+width)))
    (bool_to_word (EL j ws = w)) u` >>
  qabbrev_tac `bs = jump_to (if EL j ws = w then
    fresh_label_output "in_found" (sa.cs_next_label+3) else
    fresh_label_output "in_incr" (sa.cs_next_label+4)) bv` >>
  qabbrev_tac `BG = \H:num. step_prov PG (Gu H) bi bv` >>
  qabbrev_tac `BT = \H:num. step_taint bi u bv (Tu H)` >>
  qexistsl_tac [`bs`,`BG`,`BT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `eval_operand needle u = SOME w /\ op_prov (Gu H) needle = NONE /\
   op_taint (Tu H) needle = {}` by metis_tac[membership_loop_frame_operand] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK bs,BG H,BT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (BG H) (BT H) bs /\
   membership_loop_registers sa j 0w (BG H) (BT H) bs /\
   ~bs.vs_halted /\ bs.vs_inst_idx = 0 /\ allocas_from lo bs` by
    (map_every qunabbrev_tac [`BG`,`BT`,`bs`,`bv`,`bi`,`delta`,`width`] >> BETA_TAC >>
     irule (SIMP_RULE bool_ss [] (Q.GENL
       [`delta`,`width`,`lhs`,`rhs`,`dst`,`eid`,`yes`,`no`,`ins`,`t`,`G1`,`tn1`,`u`]
       (Q.INST [`cond_site` |-> `F`] rest_word_membership_compare_segment_joint))) >>
     rule_assum_tac (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> metis_tac[]) >>
  simp[] >> simp[Abbr `bs`, jump_to_def]
QED
Resume rest_word_membership_search_suffix_joint_all[found]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `fu = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5))
    (update_var ("%" ++ toString sa.cs_next_var) 1w u)` >>
  qabbrev_tac `FG = \H:num. DRESTRICT (Gu H) (COMPL {"%" ++ toString sa.cs_next_var})` >>
  qabbrev_tac `FT = \H:num. (Tu H) with t_var := (Tu H).t_var |+
    ("%" ++ toString sa.cs_next_var,{})` >>
  qexistsl_tac [`fu`,`FG`,`FT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK fu,FG H,FT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (FG H) (FT H) fu /\
   membership_loop_registers sa j 1w (FG H) (FT H) fu /\
   ~fu.vs_halted /\ fu.vs_inst_idx = 0 /\ allocas_from lo fu` by
    (map_every qunabbrev_tac [`FG`,`FT`,`fu`] >> BETA_TAC >>
     irule (Q.GENL [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
       rest_word_membership_found_joint) >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `fu`, jump_to_def]
QED
Resume rest_word_membership_search_suffix_joint_all[increment]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+6+delta+width)` >>
  qabbrev_tac `a = mk_inst (sa.cs_next_id+12+delta+width) ADD [Var idx;Lit 1w] [dst]` >>
  qabbrev_tac `b = mk_inst (sa.cs_next_id+13+delta+width) ASSIGN [Var dst] [idx]` >>
  qabbrev_tac `v = update_var dst (n2w (SUC j)) u` >>
  qabbrev_tac `iv = update_var idx (n2w (SUC j)) (v with vs_inst_idx := 1)` >>
  qabbrev_tac `iu = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) iv` >>
  qabbrev_tac `IG = \H:num. step_prov PG (step_prov PG (Gu H) a v) b iv` >>
  qabbrev_tac `IT = \H:num. step_taint b (v with vs_inst_idx := 1) iv
    (step_taint a u v (Tu H))` >>
  qexistsl_tac [`iu`,`IG`,`IT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gu H,Tu H) [] (OK iu,IG H,IT H) /\
   membership_loop_frame sa (G0 H) (T0 H) s0 (IG H) (IT H) iu /\
   membership_loop_registers sa (SUC j) 0w (IG H) (IT H) iu /\
   ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu` by
    (map_every qunabbrev_tac [`IG`,`IT`,`iu`,`iv`,`v`,`a`,`b`,`idx`,`dst`,`delta`,`width`] >>
     BETA_TAC >> drule (Q.GENL
       [`delta`,`width`,`idx`,`dst`,`a`,`b`,`t`,`G1`,`tn1`,`v`,`G2`,`tn2`,`u`]
       rest_word_membership_increment_joint) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `iu`, jump_to_def]
QED
Finalise rest_word_membership_search_suffix_joint_all

Theorem rest_word_membership_loop_joint_all:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  (!H:num. guard H ==>
    eval_operand needle s0 = SOME w /\ op_prov (G0 H) needle = NONE /\
    op_taint (T0 H) needle = {} /\
    eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
    op_prov (G0 H) len = NONE /\ op_taint (T0 H) len = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H:num. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H:num. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov (Gt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint (Tt H) (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}) /\
  (!H:num. guard H ==> ~s0.vs_halted /\ allocas_from lo s0 /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts) ==>
  ?t Gt Tt. !H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0 H,T0 H) [] (OK t,Gt H,Tt H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov (Gt H) op = NONE /\ op_taint (Tt H) op = {} /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `ix = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `res = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `it = update_var res 0w (update_var ix 0w
    (jump_to (fresh_label_output "in_entry" sa.cs_next_label) s0))` >>
  qabbrev_tac `iu = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) it` >>
  qabbrev_tac `GI = \H:num. DRESTRICT (DRESTRICT (G0 H) (COMPL {ix})) (COMPL {res})` >>
  qabbrev_tac `TI = \H:num. (T0 H) with t_var := ((T0 H).t_var |+ (ix,{})) |+ (res,{})` >>
  `!H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0 H,T0 H) [] (OK iu,GI H,TI H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (GI H) (TI H) iu /\
    membership_loop_registers sa 0 0w (GI H) (TI H) iu /\
    ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu /\
    iu.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1)` by
    suspend "entry" >>
  `?fin GF TF j. !H:num. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (iu,GI H,TI H) [] (OK fin,GF H,TF H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (GF H) (TF H) fin /\
    membership_loop_registers sa j (bool_to_word (MEM w ws)) (GF H) (TF H) fin /\
    ~fin.vs_halted /\ allocas_from lo fin /\ fin.vs_inst_idx = 0 /\
    fin.vs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5)` by
    (mp_tac (Q.SPECL [`0`,`iu`,`GI`,`TI`] rest_word_membership_search_suffix_joint_all) >>
     (impl_tac >-
       (pure_asm_rewrite_tac [] >> rewrite_tac [] >>
        conj_tac >- simp[] >>
        gen_tac >> disch_tac >>
        qpat_x_assum `!h:num. guard h ==> gas_origin_ptr_path _ (s0,_,_) _ _ /\ _`
          (qspec_then `H` (drule_then strip_assume_tac)) >>
        pure_asm_rewrite_tac [] >> rewrite_tac [])) >>
     simp[]) >>
  drule membership_compiled_loop_exit >> strip_tac >>
  Cases_on `is_in`
  >- suspend "in_exit" >>
  suspend "notin_exit"
QED

Resume rest_word_membership_loop_joint_all[entry]:
  gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0 H,T0 H) [] (OK iu,GI H,TI H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (GI H) (TI H) iu /\
    membership_loop_registers sa 0 0w (GI H) (TI H) iu /\
    ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu` by
    (map_every qunabbrev_tac [`GI`,`TI`,`iu`,`it`,`ix`,`res`] >> BETA_TAC >>
     irule (SIMP_RULE bool_ss [] (Q.GENL
       [`idx`,`result`,`e`,`t`,`G2`,`tn2`,`u`] rest_word_membership_init_joint)) >>
     pure_asm_rewrite_tac [] >> metis_tac[]) >>
  pure_asm_rewrite_tac [] >> simp[Abbr `iu`, jump_to_def]
QED

Resume rest_word_membership_loop_joint_all[in_exit]:
  qexistsl_tac [`fin`,`GF`,`TF`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s0,G0 H,T0 H) [] (OK fin,GF H,TF H)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  pure_asm_rewrite_tac [] >>
  gvs[membership_loop_registers_def, eval_operand_def, op_prov_def, op_taint_def]
QED

Resume rest_word_membership_loop_joint_all[notin_exit]:
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+7+delta+width)` >>
  qabbrev_tac `ni = mk_inst (sa.cs_next_id+15+delta+width) ISZERO
    [Var ("%" ++ toString sa.cs_next_var)] [dst]` >>
  qabbrev_tac `nv = update_var dst (bool_to_word (~MEM w ws)) fin` >>
  qabbrev_tac `nu = nv with vs_inst_idx := 1` >>
  qabbrev_tac `NG = \H:num. step_prov PG (GF H) ni nv` >>
  qabbrev_tac `NT = \H:num. step_taint ni fin nv (TF H)` >>
  qexistsl_tac [`nu`,`NG`,`NT`] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (fin,GF H,TF H) [] (OK nu,NG H,NT H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (NG H) (NT H) nu /\
    eval_operand op nu = SOME (bool_to_word (~MEM w ws)) /\
    op_prov (NG H) op = NONE /\ op_taint (NT H) op = {} /\
    ~nu.vs_halted /\ nu.vs_current_bb = sb.cs_current_bb /\
    nu.vs_inst_idx = 1 /\ allocas_from lo nu` by
    (map_every qunabbrev_tac [`NG`,`NT`,`nu`,`nv`,`ni`,`dst`,`delta`,`width`] >>
     BETA_TAC >>
     `~MEM w ws <=> (bool_to_word (MEM w ws):bytes32) = 0w` by
       (Cases_on `MEM w ws` >> simp[bool_to_word_def]) >>
     pop_assum SUBST1_TAC >>
     irule (SIMP_RULE bool_ss [] (Q.GENL
       [`delta`,`width`,`dst`,`ins`,`t`,`G1`,`tn1`,`u`]
       rest_word_membership_notin_joint)) >>
     rule_assum_tac (REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
     rewrite_tac [] >>
     conj_tac
     >- (qexistsl_tac [`arr`,`len`,`needle`,`stride`] >> metis_tac[]) >>
     qexists_tac `j` >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s0,G0 H,T0 H) [] (OK nu,NG H,NT H)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  pure_asm_rewrite_tac [] >> simp[]
QED

Finalise rest_word_membership_loop_joint_all

Theorem rest_word_membership_loop_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) NONE is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  eval_operand needle s0 = SOME w /\ op_prov G0 needle = NONE /\
  op_taint tn0 needle = {} /\
  eval_operand len s0 = SOME (n2w (LENGTH ws)) /\
  op_prov G0 len = NONE /\ op_taint tn0 len = {} /\
  (!i s G tn. i < LENGTH ws /\
      membership_loop_frame sa G0 tn0 s0 G tn s /\
      membership_loop_registers sa i 0w G tn s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0 ==>
    ?t Gt tt.
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,Gt,tt) /\
      membership_loop_frame sa G0 tn0 s0 Gt tt t /\
      membership_loop_registers sa i 0w Gt tt t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov Gt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint tt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}) /\
  ~s0.vs_halted /\ allocas_from lo s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t GF TF.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s0,G0,tn0) [] (OK t,GF,TF) /\
    membership_loop_frame sa G0 tn0 s0 GF TF t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov GF op = NONE /\ op_taint TF op = {} /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qspecl_then [`\H:num. D`, `\H:num. G0`, `\H:num. tn0`, `\H:num. H=0`]
    mp_tac (Q.GENL [`DF`,`G0`,`T0`,`guard`]
      rest_word_membership_loop_joint_all) >>
  BETA_TAC >>
  (impl_tac >-
    (pure_asm_rewrite_tac [] >> rewrite_tac [] >>
     suspend "callback")) >>
  disch_then (qx_choose_then `fin` (qx_choose_then `GF` (qx_choose_then `TF` assume_tac))) >>
  qexistsl_tac [`fin`,`GF 0`,`TF 0`] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Resume rest_word_membership_loop_joint[callback]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!H:num. H = 0 ==> _` (qspec_then `0` assume_tac) >>
  gvs[] >>
  qpat_x_assum `!i s G tn. _`
    (qspecl_then [`i`,`s`,`Gs 0`,`Ts 0`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac [] >> rewrite_tac [])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `GU` (qx_choose_then `TU` assume_tac))) >>
  qexistsl_tac [`u`,`\H:num. GU`,`\H:num. TU`] >> simp[]
QED

Finalise rest_word_membership_loop_joint
