(* Joint control segments for the bounded word-array membership compiler. *)
Theory bodyFullBopRestWordBoundedControl
Ancestors
  bodyFullBopRestWordControl bodyPtrBopInBoundedLayout
  bodyPtrSignedConvertClamp fragGasCopyLoop
  bodyPtrBopInLoopSearch bodyPtrBopInLoopCode bodyPtrBopInLoopLookups bodyPtrBopInLoopLayout
  bodyPtrBopInLoopContract bodyPtrBopInLiteralSuffix bodyPtrBopInScalarTransport
  exprLoweringProps fragExecMem fragGasEmitCtrl fragGasSeqPtr fragGasOriginPtr fragGasOriginPtrLoop stmtAppendStorageRunPtr
  gasEvents gasCount ptrSafeRun memSafeRun instMemFrontier
  ptrDiscipline unitTransformDefs contextCodegenRel codegenRel fragGasOrigin fragGasPathPtr list
  venomExecSemantics venomExecProps venomInst venomState finite_map

Theorem rest_word_membership_bounded_compare_segment_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  lhs = Var ("%" ++ toString (sa.cs_next_var + (if cond_site then 1 else 6+delta+width))) /\
  rhs = (if cond_site then len else needle) /\
  dst = "%" ++ toString (sa.cs_next_var + (if cond_site then 4 else 7+delta+width)) /\
  eid = sa.cs_next_id + (if cond_site then 7 else 11+delta+width) /\
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
     >- (gvs[] >> drule_all membership_bounded_condition_lookup >> strip_tac >>
         qexists_tac `bb` >> simp[get_instruction_def]) >>
     drule_all membership_bounded_compare_lookup >> strip_tac >>
     drule membership_drop_pair_lookup >> strip_tac >>
     qexists_tac `bb` >> gvs[]) >>
  `(!z. not_fresh_at sa z ==> z <> dst) /\
   dst <> "%" ++ toString (sa.cs_next_var+1) /\
   dst <> "%" ++ toString sa.cs_next_var` by
    (conj_tac
     >- (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
         first_x_assum (qspec_then `if cond_site then 4 else 7+delta+width` mp_tac) >>
         simp[]) >>
     Cases_on `cond_site` >> simp[] >>
     Cases_on `0 < skip` >>
     Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]) >>
  drule_all rest_word_membership_segment_compare_joint >> simp[]
QED
Theorem rest_word_membership_bounded_condition_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
  s.vs_inst_idx = 0 /\ membership_loop_registers sa i r G tn s /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  eval_operand len s = SOME (n2w k) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  dst = "%" ++ toString (sa.cs_next_var+4) /\
  ins = mk_inst (sa.cs_next_id+7) EQ
    [Var ("%" ++ toString (sa.cs_next_var+1));len] [dst] /\
  t = update_var dst (bool_to_word ((n2w i:bytes32) = n2w k)) s /\
  G1 = step_prov PG G ins t /\ tn1 = step_taint ins s t tn /\
  target = (if (n2w i:bytes32) = n2w k then
    fresh_label_output "in_exit" (sa.cs_next_label+5) else
    fresh_label_output "in_body" (sa.cs_next_label+2)) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to target t),G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 (jump_to target t) /\
  membership_loop_registers sa i r G1 tn1 (jump_to target t) /\
  ~(jump_to target t).vs_halted /\ (jump_to target t).vs_inst_idx = 0 /\
  allocas_from lo (jump_to target t)
Proof
  strip_tac >>
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) s = SOME (n2w i) /\
   op_prov G (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
    fs[membership_loop_registers_def, eval_operand_def] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.GENL [`delta`, `width`, `lhs`, `rhs`, `dst`, `eid`, `yes`, `no`,
             `ins`, `t`, `G1`, `tn1`, `u`]
      (Q.INST [`cond_site` |-> `T`] rest_word_membership_bounded_compare_segment_joint))) >>
  strip_tac >> gvs[]
QED

Theorem rest_word_membership_bounded_found_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_found" (sa.cs_next_label+3) /\
  s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  dst = "%" ++ toString sa.cs_next_var /\
  ins = mk_inst (sa.cs_next_id+13+delta+width) ASSIGN [Lit 1w] [dst] /\
  t = update_var dst 1w s /\
  G1 = DRESTRICT G (COMPL {dst}) /\
  tn1 = tn with t_var := tn.t_var |+ (dst,{}) /\
  u = jump_to (fresh_label_output "in_exit" (sa.cs_next_label+5)) t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 u /\
  membership_loop_registers sa i 1w G1 tn1 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >> drule_all membership_bounded_found_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb 0 = SOME ins /\
   get_instruction bb 1 = SOME (mk_inst (sa.cs_next_id+13+delta+width+1) JMP
     [Label (fresh_label_output "in_exit" (sa.cs_next_label+5))] [])` by
    simp[get_instruction_def] >>
  drule_all rest_word_membership_segment_found_joint >> simp[]
QED

Theorem rest_word_membership_bounded_increment_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
  s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  dst = "%" ++ toString (sa.cs_next_var+8+delta+width) /\
  a = mk_inst (sa.cs_next_id+15+delta+width) ADD [Var idx;Lit 1w] [dst] /\
  b = mk_inst (sa.cs_next_id+16+delta+width) ASSIGN [Var dst] [idx] /\
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
  strip_tac >> drule_all membership_bounded_increment_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb 0 = SOME a /\ get_instruction bb 1 = SOME b /\
   get_instruction bb 2 = SOME (mk_inst (sa.cs_next_id+17+delta+width) JMP
     [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] [])` by
    simp[get_instruction_def] >>
  `dst <> idx /\ dst <> "%" ++ toString sa.cs_next_var /\
   idx <> "%" ++ toString sa.cs_next_var /\
   (!z. not_fresh_at sa z ==> z <> dst /\ z <> idx)` by
    (conj_tac >- (Cases_on `0 < skip` >>
       Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]) >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `8+delta+width` mp_tac) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  drule_all rest_word_membership_segment_increment_joint >> simp[]
QED

Theorem rest_word_membership_bounded_notin_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = 0 /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  dst = "%" ++ toString (sa.cs_next_var+9+delta+width) /\
  ins = mk_inst (sa.cs_next_id+18+delta+width) ISZERO
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
  strip_tac >> drule_all membership_bounded_notin_exit_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb 0 = SOME ins` by
    (Cases_on `bb.bb_instructions` >> gvs[get_instruction_def]) >>
  `(!z. not_fresh_at sa z ==> z <> dst)` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `9+delta+width` mp_tac) >> simp[]) >>
  drule membership_bounded_loop_exit >> strip_tac >>
  `op = Var dst` by gvs[] >>
  drule_all rest_word_membership_segment_notin_joint >> simp[]
QED

Theorem rest_word_membership_bounded_capacity_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = fresh_label_output "in_entry" sa.cs_next_label /\
  s.vs_inst_idx = 2 /\
  eval_operand len s = SOME (n2w n) /\ n <= cap /\ cap < dimword (:256) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  a = "%" ++ toString (sa.cs_next_var+2) /\
  b = "%" ++ toString (sa.cs_next_var+3) /\
  t = update_var b 1w (update_var a 0w s) /\
  G1 = DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b}) /\
  tn1 = tn with t_var := tn.t_var |+ (a,{}) |+ (b,{}) /\
  u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1)) t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G1,tn1) /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 u /\
  membership_loop_registers sa i r G1 tn1 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >> drule_all membership_bounded_entry_lookup >> strip_tac >>
  qabbrev_tac `code =
    [mk_inst (sa.cs_next_id+3) GT [len;Lit (n2w cap)] [a];
     mk_inst (sa.cs_next_id+4) ISZERO [Var a] [b];
     mk_inst (sa.cs_next_id+5) ASSERT [Var b] []]` >>
  `run_inst_seq code s = OK t` by suspend "run" >>
  `run_inst_seq_mem_ok code s` by
    (irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
     simp[Abbr `code`, inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def]) >>
  `inst_seq_ptr D lo ctx fn PG G tn code s G1 tn1` by suspend "ptr" >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME entry_bb /\
   isPREFIX code (DROP s.vs_inst_idx entry_bb.bb_instructions) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := 5),G1,tn1)` by
    (drule_all run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (t with vs_inst_idx := 5,G1,tn1) [] (OK u,G1,tn1)` by
    (`u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
       (t with vs_inst_idx := 5)` by simp[jump_to_def] >>
     pop_assum SUBST1_TAC >>
     irule fragGasOriginPtrLoopTheory.jmp_origin_ptr_path >>
     simp[update_var_def, allocas_from_def] >>
     conj_tac
     >- (qexists_tac `sa.cs_next_id+6` >> gvs[get_instruction_def]) >>
     gvs[allocas_from_def]) >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, APPEND] >>
  suspend "post"
QED

Resume rest_word_membership_bounded_capacity_joint[run]:
  `n < dimword (:256)` by decide_tac >>
  simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
       mk_inst_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, wordsTheory.word_gt_def, wordsTheory.word_lo_n2w,
       bool_to_word_def, exec_pure2_def, exec_pure1_def,
       eval_operands_def, wordsTheory.w2n_n2w]
QED

Resume rest_word_membership_bounded_capacity_joint[ptr]:
  `n < dimword (:256)` by decide_tac >>
  `run_inst_seq
    [mk_inst (sa.cs_next_id+3) GT [len;Lit (n2w cap)] [a];
     mk_inst (sa.cs_next_id+4) ISZERO [Var a] [b]] s = OK t` by
    simp[run_inst_seq_def, step_inst_base_opcode_eqs,
       mk_inst_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, bool_to_word_def, exec_pure2_def, exec_pure1_def,
       eval_operands_def, wordsTheory.w2n_n2w] >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s G1 tn1` by
    (simp[Abbr `code`] >>
     irule (SRULE [GSYM arithmeticTheory.ADD_ASSOC]
       (Q.INST [`id` |-> `sa.cs_next_id+3`]
         (SPEC_ALL scalar_iszero_assert_certificate))) >>
     simp[op_prov_def, op_taint_def] >> qexists_tac `t` >> gvs[]) >>
  irule fragGasCopyLoopTheory.inst_seq_ptr_lower_bound_transport >>
  conj_tac >- simp[Abbr `code`, mk_inst_def] >>
  simp[] >> qexists_tac `0` >> gvs[]
QED

Resume rest_word_membership_bounded_capacity_joint[post]:
  `(!z. not_fresh_at sa z ==> z <> a /\ z <> b) /\
   a <> "%" ++ toString sa.cs_next_var /\
   b <> "%" ++ toString sa.cs_next_var /\
   a <> "%" ++ toString (sa.cs_next_var+1) /\
   b <> "%" ++ toString (sa.cs_next_var+1)` by
    (rpt conj_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >>
     first_assum (qspec_then `2` mp_tac) >>
     first_x_assum (qspec_then `3` mp_tac) >> simp[]) >>
  fs[membership_loop_frame_def, membership_loop_registers_def,
     jump_to_def, update_var_def, allocas_from_def, lookup_var_def,
     FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_prov_def, op_taint_def] >>
  rpt strip_tac >> gvs[] >>
  fs[venom_state_component_equality] >> metis_tac[]
QED

Finalise rest_word_membership_bounded_capacity_joint

Theorem rest_word_membership_bounded_init_joint:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand len s = SOME (n2w n) /\ n <= cap /\ cap < dimword (:256) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  result = "%" ++ toString sa.cs_next_var /\
  a = "%" ++ toString (sa.cs_next_var+2) /\
  b = "%" ++ toString (sa.cs_next_var+3) /\
  e = jump_to (fresh_label_output "in_entry" sa.cs_next_label) s /\
  t = update_var result 0w (update_var idx 0w e) /\
  G2 = DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {result}) /\
  tn2 = tn with t_var := tn.t_var |+ (idx,{}) |+ (result,{}) /\
  G3 = DRESTRICT (DRESTRICT G2 (COMPL {a})) (COMPL {b}) /\
  tn3 = tn2 with t_var := tn2.t_var |+ (a,{}) |+ (b,{}) /\
  u = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
        (update_var b 1w (update_var a 0w t)) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,G3,tn3) /\
  membership_loop_frame sa G tn s G3 tn3 u /\
  membership_loop_registers sa 0 0w G3 tn3 u /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u
Proof
  strip_tac >> drule_all membership_bounded_entry_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME old_bb /\
   get_instruction old_bb s.vs_inst_idx = SOME
     (mk_inst sa.cs_next_id JMP [Label (fresh_label_output "in_entry" sa.cs_next_label)] []) /\
   lookup_block e.vs_current_bb fn.fn_blocks = SOME entry_bb /\
   isPREFIX [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
             mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result]] entry_bb.bb_instructions` by
    fs[jump_to_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := 2),G2,tn2) /\
   membership_loop_frame sa G tn s G2 tn2 (t with vs_inst_idx := 2) /\
   membership_loop_registers sa 0 0w G2 tn2 (t with vs_inst_idx := 2) /\
   ~(t with vs_inst_idx := 2).vs_halted /\
   (t with vs_inst_idx := 2).vs_inst_idx = 2 /\
   allocas_from lo (t with vs_inst_idx := 2)` by
    (irule (Q.GEN `u` rest_word_membership_segment_init_prefix_joint) >>
     metis_tac[]) >>
  `eval_operand len (t with vs_inst_idx := 2) = SOME (n2w n) /\
   op_prov G2 len = NONE /\ op_taint tn2 len = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (t with vs_inst_idx := 2,G2,tn2) [] (OK u,G3,tn3) /\
   membership_loop_frame sa G tn s G3 tn3 u /\
   membership_loop_registers sa 0 0w G3 tn3 u /\
   ~u.vs_halted /\ u.vs_inst_idx = 0 /\ allocas_from lo u` by
    (irule (Q.GENL [`t`,`u`] rest_word_membership_bounded_capacity_joint) >>
     gvs[update_var_def, jump_to_def, eval_operand_def, lookup_var_def] >>
     metis_tac[]) >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED

Theorem rest_word_membership_bounded_search_suffix_joint_all:
  !i s Gs Ts.
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
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
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+6+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov (Gt H) (Var ("%" ++ toString (sa.cs_next_var+6+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint (Tt H) (Var ("%" ++ toString (sa.cs_next_var+6+
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
    (Q.INST [`bound` |-> `SOME cap`,
      `loaded` |-> `Var ("%" ++ toString (sa.cs_next_var+6+
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

Resume rest_word_membership_bounded_search_suffix_joint_all[condition]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `ci = mk_inst (sa.cs_next_id+7) EQ
    [Var ("%" ++ toString (sa.cs_next_var+1));len]
    ["%" ++ toString (sa.cs_next_var+4)]` >>
  qabbrev_tac `cv = update_var ("%" ++ toString (sa.cs_next_var+4))
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
   membership_loop_registers sa j 0w (CG H) (CT H) cs /\
   ~cs.vs_halted /\ cs.vs_inst_idx = 0 /\ allocas_from lo cs` by
    (map_every qunabbrev_tac [`CG`,`CT`,`cs`,`cv`,`ci`] >> BETA_TAC >>
     irule (SIMP_RULE bool_ss [] (Q.GENL [`dst`,`ins`,`t`,`G1`,`tn1`,`target`]
       rest_word_membership_bounded_condition_joint)) >> metis_tac[]) >>
  `j < dimword (:256)` by decide_tac >>
  simp[] >> simp[Abbr `cs`, jump_to_def, wordsTheory.n2w_11]
QED
Resume rest_word_membership_bounded_search_suffix_joint_all[compare]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `bi = mk_inst (sa.cs_next_id+(11+delta+width)) EQ
    [Var ("%" ++ toString (sa.cs_next_var+(6+delta+width)));needle]
    ["%" ++ toString (sa.cs_next_var+(7+delta+width))]` >>
  qabbrev_tac `bv = update_var ("%" ++ toString (sa.cs_next_var+(7+delta+width)))
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
       (Q.INST [`cond_site` |-> `F`] rest_word_membership_bounded_compare_segment_joint))) >>
     rule_assum_tac (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> metis_tac[]) >>
  simp[] >> simp[Abbr `bs`, jump_to_def]
QED
Resume rest_word_membership_bounded_search_suffix_joint_all[found]:
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
       rest_word_membership_bounded_found_joint) >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `fu`, jump_to_def]
QED
Resume rest_word_membership_bounded_search_suffix_joint_all[increment]:
  map_every qx_gen_tac [`j`,`u`,`Gu`,`Tu`] >> strip_tac >>
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `idx = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+8+delta+width)` >>
  qabbrev_tac `a = mk_inst (sa.cs_next_id+15+delta+width) ADD [Var idx;Lit 1w] [dst]` >>
  qabbrev_tac `b = mk_inst (sa.cs_next_id+16+delta+width) ASSIGN [Var dst] [idx]` >>
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
       rest_word_membership_bounded_increment_joint) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  simp[] >> simp[Abbr `iu`, jump_to_def]
QED
Finalise rest_word_membership_bounded_search_suffix_joint_all

Theorem rest_word_membership_loop_bounded_joint_all:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ LENGTH ws < dimword (:256) /\
  LENGTH ws <= cap /\ cap < dimword (:256) /\
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
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+6+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov (Gt H) (Var ("%" ++ toString (sa.cs_next_var+6+
        (if 0 < skip then 1 else 0)+
        (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
      op_taint (Tt H) (Var ("%" ++ toString (sa.cs_next_var+6+
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
  qabbrev_tac `a = "%" ++ toString (sa.cs_next_var+2)` >>
  qabbrev_tac `b = "%" ++ toString (sa.cs_next_var+3)` >>
  qabbrev_tac `it = update_var res 0w (update_var ix 0w
    (jump_to (fresh_label_output "in_entry" sa.cs_next_label) s0))` >>
  qabbrev_tac `iu = jump_to (fresh_label_output "in_cond" (sa.cs_next_label+1))
    (update_var b 1w (update_var a 0w it))` >>
  qabbrev_tac `GI = \H:num. DRESTRICT (DRESTRICT
    (DRESTRICT (DRESTRICT (G0 H) (COMPL {ix})) (COMPL {res})) (COMPL {a})) (COMPL {b})` >>
  qabbrev_tac `TI = \H:num. (T0 H) with t_var :=
    ((((T0 H).t_var |+ (ix,{})) |+ (res,{})) |+ (a,{})) |+ (b,{})` >>
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
    (mp_tac (Q.SPECL [`0`,`iu`,`GI`,`TI`] rest_word_membership_bounded_search_suffix_joint_all) >>
     (impl_tac >-
       (pure_asm_rewrite_tac [] >> rewrite_tac [] >>
        conj_tac >- simp[] >>
        gen_tac >> disch_tac >>
        qpat_x_assum `!h:num. guard h ==> gas_origin_ptr_path _ (s0,_,_) _ _ /\ _`
          (qspec_then `H` (drule_then strip_assume_tac)) >>
        pure_asm_rewrite_tac [] >> rewrite_tac [])) >>
     simp[]) >>
  drule membership_bounded_loop_exit >> strip_tac >>
  Cases_on `is_in`
  >- suspend "in_exit" >>
  suspend "notin_exit"
QED

Resume rest_word_membership_loop_bounded_joint_all[entry]:
  gen_tac >> disch_tac >>
  qpat_x_assum `!i s Gs Ts. _` kall_tac >>
  rpt (qpat_x_assum `!h:num. guard h ==> _`
    (qspec_then `H` (drule_then strip_assume_tac))) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s0,G0 H,T0 H) [] (OK iu,GI H,TI H) /\
    membership_loop_frame sa (G0 H) (T0 H) s0 (GI H) (TI H) iu /\
    membership_loop_registers sa 0 0w (GI H) (TI H) iu /\
    ~iu.vs_halted /\ iu.vs_inst_idx = 0 /\ allocas_from lo iu` by
    (map_every qunabbrev_tac [`GI`,`TI`,`iu`,`it`,`ix`,`res`,`a`,`b`] >> BETA_TAC >>
     drule (Q.GENL
       [`idx`,`result`,`a`,`b`,`e`,`t`,`G2`,`tn2`,`G3`,`tn3`,`u`]
       rest_word_membership_bounded_init_joint) >>
     disch_then irule >> simp[] >> qexists_tac `LENGTH ws` >> simp[]) >>
  pure_asm_rewrite_tac [] >> simp[Abbr `iu`, jump_to_def]
QED

Resume rest_word_membership_loop_bounded_joint_all[in_exit]:
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

Resume rest_word_membership_loop_bounded_joint_all[notin_exit]:
  qabbrev_tac `delta = if 0 < skip then 1 else 0` >>
  qabbrev_tac `width = if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1` >>
  qabbrev_tac `dst = "%" ++ toString (sa.cs_next_var+9+delta+width)` >>
  qabbrev_tac `ni = mk_inst (sa.cs_next_id+18+delta+width) ISZERO
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
       rest_word_membership_bounded_notin_joint)) >>
     rule_assum_tac (REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
     rewrite_tac [] >>
     conj_tac
     >- (qexistsl_tac [`arr`,`cap`,`len`,`needle`,`stride`] >> metis_tac[]) >>
     qexists_tac `j` >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s0,G0 H,T0 H) [] (OK nu,NG H,NT H)` by
    metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  pure_asm_rewrite_tac [] >> simp[]
QED

Finalise rest_word_membership_loop_bounded_joint_all
