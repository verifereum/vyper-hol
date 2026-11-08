(* Counted scratch allocation and zero initialization for Concat. *)
Theory bodyPtrBytestringBuiltinsConcatPrefix
Ancestors
  bodyPtrBytestringBuiltinsBuffer bodyPtrBytestringBuiltinsAllocation
  bodyPtrPopMemoryStore loweringHalt
  fragGasPathPtr fragGasSeqPtr loweringPosts bodyPtrDefs context emitHelper
  emitHelperProps compileEnv venomState venomInst venomExecSemantics
  ptrDiscipline words finite_map pred_set list

Theorem concat_alloc_zero_counted:
  compile_alloc_buffer n sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 0w] sm = ((),sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ 32 <= n /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out G1 tn1 t a.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
    ptr_covers G1 tn1 out t n /\ lookup_var out t = SOME a /\
    mload (w2n a) t = 0w /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn1.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==>
      ptr_covers G1 tn1 x t k)
Proof
  strip_tac >> drule_all compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     strip_tac >> gvs[update_var_def]) >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `ptr_covers G1 tn1 out uh n` >>
  `~uh.vs_halted /\ uh.vs_current_bb = sm.cs_current_bb /\
   uh.vs_inst_idx = LENGTH sm.cs_current_insts /\
   lookup_var out uh = SOME (n2w a) /\ ptr_covers G1 tn1 out uh 32` by
    (gvs[Abbr `uh`, lookup_var_def, ptr_covers_def] >> decide_tac) >>
  `eval_operand (Lit 0w) uh = SOME 0w /\ op_taint tn1 (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `emit_void MSTORE [Var out; Lit 0w] sm = ((),sb)` by metis_tac[] >>
  drule_all pop_emit_mstore_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn' (OK t)` by
    (drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ G tn s _ _ _ _`)
       (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]) >>
  `ptr_covers G1 tn' out t n` by
    gvs[ptr_covers_def, op_taint_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >> `x <> out` by simp[] >>
     `op_taint tn' (Var x) = op_taint tn1 (Var x)` by simp[op_taint_def] >>
     `FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)` by
       simp[alloca_old_register_ghost_frame] >>
     gvs[Abbr `uh`, lookup_var_def]) >>
  `!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==>
    ptr_covers G1 tn' x t k` by
    (rpt strip_tac >> gvs[ptr_covers_def]) >>
  qexistsl_tac [`out`,`G1`,`tn'`,`t`,`n2w a`] >> simp[] >>
  `!ss z k. mload z (ss with vs_inst_idx := k) = mload z ss` by
    simp[mload_def] >>
  simp[venomMemProofsTheory.mload_mstore_same_proof]
QED
