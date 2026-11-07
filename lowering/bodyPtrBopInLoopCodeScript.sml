Theory bodyPtrBopInLoopCode
Ancestors bodyPtrBopInLoopLayout bodyPtrBopInLoopLookups
  bodyPtrBopInLoopControl bodyPtrBopInLoopExit compileEnv exprLowering list

Theorem membership_compiled_loop_exit:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) ==>
  sb.cs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
  LENGTH sb.cs_current_insts = (if is_in then 0 else 1) /\
  op = Var ("%" ++ toString
    (sa.cs_next_var + (if is_in then 0 else 7 + (if 0 < skip then 1 else 0) +
      (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))))
Proof
  simp[SRULE [] membership_loop_layout] >> strip_tac >> gvs[] >>
  Cases_on `is_in` >> simp[]
QED

Theorem membership_compiled_loop_init:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  result = "%" ++ toString sa.cs_next_var ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    t.vs_inst_idx = 0 /\
    lookup_var idx t = SOME 0w /\ lookup_var result t = SOME 0w /\
    FLOOKUP G' idx = NONE /\ FLOOKUP G' result = NONE /\
    op_taint tn' (Var idx) = {} /\ op_taint tn' (Var result) = {} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t = s with <|vs_vars := t.vs_vars; vs_current_bb := t.vs_current_bb;
      vs_prev_bb := t.vs_prev_bb; vs_inst_idx := t.vs_inst_idx|>
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  irule (SRULE [] membership_init_path_ptr) >> simp[] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  qexists_tac `fresh_label_output "in_entry" sa.cs_next_label` >>
  goal_assum (drule_at Any) >>
  simp[venomInstTheory.get_instruction_def, EL_APPEND_EQN]
QED

(* Only the five finished loop blocks have a generated non-PHI head.
   In's open exit is deliberately absent from this statement. *)
Theorem membership_compiled_loop_closed_nonphi:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  (lbl = fresh_label_output "in_entry" sa.cs_next_label \/
   lbl = fresh_label_output "in_cond" (sa.cs_next_label+1) \/
   lbl = fresh_label_output "in_body" (sa.cs_next_label+2) \/
   lbl = fresh_label_output "in_found" (sa.cs_next_label+3) \/
   lbl = fresh_label_output "in_incr" (sa.cs_next_label+4)) /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]
QED

Theorem membership_compiled_notin_exit_ghost:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sb.cs_current_bb ==>
  entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  irule typedCopyArrayPtrTheory.entry_ghost_no_phi >> qexists_tac `bb` >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]
QED

Theorem membership_compiled_condition_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block (fresh_label_output "in_cond" (sa.cs_next_label+1))
         fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst (sa.cs_next_id+4) EQ
         [Var ("%" ++ toString (sa.cs_next_var+1));len]
         ["%" ++ toString (sa.cs_next_var+2)];
       mk_inst (sa.cs_next_id+5) JNZ
         [Var ("%" ++ toString (sa.cs_next_var+2));
          Label (fresh_label_output "in_exit" (sa.cs_next_label+5));
          Label (fresh_label_output "in_body" (sa.cs_next_label+2))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_compiled_compare_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
         fn.fn_blocks = SOME bb /\
    DROP (2+delta+width) bb.bb_instructions =
      [mk_inst (sa.cs_next_id+8+delta+width) EQ
         [Var ("%" ++ toString (sa.cs_next_var+4+delta+width));needle]
         ["%" ++ toString (sa.cs_next_var+5+delta+width)];
       mk_inst (sa.cs_next_id+9+delta+width) JNZ
         [Var ("%" ++ toString (sa.cs_next_var+5+delta+width));
          Label (fresh_label_output "in_found" (sa.cs_next_label+3));
          Label (fresh_label_output "in_incr" (sa.cs_next_label+4))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `0 < skip` >>
  Cases_on `is_ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]
QED

Theorem membership_compiled_increment_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block (fresh_label_output "in_incr" (sa.cs_next_label+4))
         fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst (sa.cs_next_id+12+delta+width) ADD
         [Var ("%" ++ toString (sa.cs_next_var+1));Lit 1w]
         ["%" ++ toString (sa.cs_next_var+6+delta+width)];
       mk_inst (sa.cs_next_id+13+delta+width) ASSIGN
         [Var ("%" ++ toString (sa.cs_next_var+6+delta+width))]
         ["%" ++ toString (sa.cs_next_var+1)];
       mk_inst (sa.cs_next_id+14+delta+width) JMP
         [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_compiled_notin_exit_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) F sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst (sa.cs_next_id+15+delta+width) ISZERO
         [Var ("%" ++ toString sa.cs_next_var)]
         ["%" ++ toString (sa.cs_next_var+7+delta+width)]]
      bb.bb_instructions
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_compiled_found_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block (fresh_label_output "in_found" (sa.cs_next_label+3))
         fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst (sa.cs_next_id+10+delta+width) ASSIGN [Lit 1w]
         ["%" ++ toString sa.cs_next_var];
       mk_inst (sa.cs_next_id+11+delta+width) JMP
         [Label (fresh_label_output "in_exit" (sa.cs_next_label+5))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> goal_assum (drule_at Any) >> simp[]
QED
