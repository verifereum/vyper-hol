(* Resource boundary for the concrete array element-copy endpoint. *)
Theory bodyIntCallFamStmtForArrayResources
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtForArrayFrame
  bodyIntCallFamStmtForResources bodyIntCallFamStmtForFrontier
  stmtSimForArrayLoop stmtSimProps compileEnv venomState venomExecSemantics
  venomInst finite_map list rich_list intCallFrame
  bodyIntCallFamStmtForTransport bodyIntCallJointStmtJump
  bodyIntCallFamStmtForSetupGeneral exprLoweringProps fragGasMode

Theorem intcall_array_copy_entry:
  array_entry_inputs fp.jc_ctx fp.jc_func ce bc fp.jc_cx es s id p sz dst
    ainst tv v fty (get_tenv fp.jc_cx) sa sb0 idx saved arrbase k stride
    ov ep j3 j4 bb sb0 /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  type_memory_bytes ce fty < 2 ** 64 /\
  sc.cs_next_var <= sb0.cs_next_var /\ local_ptrs_reserved bc sb0 /\
  (!x. not_fresh_at sc x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) ==>
  ?s2. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK s2) /\
    intcall_joint_res fp bc (extend_local env id fty F)
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes) sb0 s2 /\
    s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    (!x. not_fresh_at sc x ==> lookup_var x s2 = lookup_var x s) /\
    s2.vs_allocas = s.vs_allocas /\ s.vs_alloca_next <= s2.vs_alloca_next
Proof
  strip_tac >>
  qhdtm_x_assum `array_entry_inputs` mp_tac >>
  rewrite_tac[array_entry_inputs_def] >> strip_tac >>
  drule_all intcall_array_body_entry_run_frame >>
  disch_then (qspecl_then [`j4`, `j3`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts` by
    (simp[mk_inst_def] >> metis_tac[iter_memory_copy_no_gas]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     sb0.cs_current_insts` by simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  drule_all intcall_array_prefix_continuation_frame >> strip_tac >>
  `s.vs_alloca_next <= s2.vs_alloca_next` by
    (drule intcall_marked_path_frontier_mono >> simp[]) >>
  `allocas_above fp.jc_lo s2` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!a len. fp.jc_prot a len ==>
     mem_bytes_at a len s2.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> simp[] >> first_x_assum irule >> disj1_tac >>
     fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def,
        allocas_above_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sc x ==> lookup_var x s2 = lookup_var x s` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `lookup_var p s2 = SOME dst` by
    (fs[local_ptrs_reserved_def] >> metis_tac[lookup_var_def]) >>
  qexists_tac `s2` >> simp[] >>
  irule intcall_for_declared_entry >> metis_tac[]
QED

(* One assignment followed by a jump, at its concrete resource endpoint. *)
Theorem intcall_for_assign_entry:
  lookup_block s.vs_current_bb fp.jc_func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst i ASSIGN [op] [x]; mk_inst j JMP [Label lbl] []] /\
  ~s.vs_halted /\ eval_operand op s = SOME w /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  not_local_ptr ce es.scopes x /\
  (!operand. fp.jc_reserved operand ==> operand <> Var x) ==>
  gas_marked_path F fp.jc_ctx fp.jc_func s 0
    (OK (jump_to lbl (update_var x w s))) /\
  intcall_joint_res fp ce env es sa (jump_to lbl (update_var x w s))
Proof
  strip_tac >> conj_tac
  >- (irule inst_seq_jump_zero_path >>
      simp[] >> qexists_tac `j` >>
      simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
           step_inst_base_def, exec_pure1_def, eval_operands_def]) >>
  simp[intcall_joint_res_jump_to] >>
  irule intcall_joint_res_update_var >> simp[] >> metis_tac[]
QED

(* The array condition uses EQ, rather than the range loop's ordered test. *)
Theorem intcall_array_condition_resources:
  lookup_block lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      [mk_inst i EQ [Var idx; Lit b] [dv];
       mk_inst j JNZ [Var dv; Label yes; Label no] []]|> /\
  s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var idx s = SOME a /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  not_local_ptr ce es.scopes dv /\
  (!op. fp.jc_reserved op ==> op <> Var dv) ==>
  let next = jump_to (if a = b then yes else no)
    (update_var dv (bool_to_word (a = b)) s) in
  gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK next) /\
  intcall_joint_res fp ce env es sa next /\
  next.vs_current_bb = (if a = b then yes else no) /\
  next.vs_inst_idx = 0 /\ ~next.vs_halted /\
  (!x. x <> dv ==> lookup_var x next = lookup_var x s) /\
  next.vs_allocas = s.vs_allocas /\ next.vs_alloca_next = s.vs_alloca_next /\
  next.vs_memory = s.vs_memory /\ next.vs_labels = s.vs_labels
Proof
  simp[LET_THM] >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
     (OK (jump_to (if a = b then yes else no)
       (update_var dv (bool_to_word (a = b)) s)))` by
    (irule eq_branch_zero_path >> simp[] >>
     qexistsl_tac [`i`, `j`, `Var idx`, `Lit b`] >>
     simp[get_instruction_def, eval_operand_def]) >>
  `intcall_joint_res fp ce env es sa
     (update_var dv (bool_to_word (a = b)) s)` by
    (irule intcall_joint_res_update_var >> simp[] >> metis_tac[]) >>
  simp[intcall_joint_res_jump_to, jump_to_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem intcall_array_start_no_history:
  aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  32 <= sz /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [aa; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry fp.jc_func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst i ASSIGN [Lit 0w] [idx]; mk_inst j' JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  local_ptrs_reserved ce sa /\ MEM aa (fn_insts fp.jc_func) /\
  fn_inst_ids_distinct fp.jc_func /\ p <> idx /\
  not_local_ptr ce es.scopes p /\ not_local_ptr ce es.scopes idx /\
  (!x. not_fresh_at sa x ==> x <> p /\ x <> idx) ==>
  ?cc w. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    cc.vs_current_bb = cond /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    intcall_joint_res fp ce env es sa cc /\
    lookup_var idx cc = SOME 0w /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas aid = SOME (w2n w,sz) /\
    (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0) /\
    (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==>
              FLOOKUP cc.vs_allocas id = SOME ent) /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    cc.vs_memory = s0.vs_memory /\ cc.vs_labels = s0.vs_labels
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> p` by metis_tac[] >>
  drule_all intcall_for_alloca_start_no_history >> strip_tac >>
  `!op. fp.jc_reserved op ==> op <> Var idx` by
    (fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func ee 0
     (OK (jump_to cond (update_var idx 0w ee))) /\
   intcall_joint_res fp ce env es sa (jump_to cond (update_var idx 0w ee))` by
    (irule intcall_for_assign_entry >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`i`, `j'`, `Lit 0w`] >> simp[eval_operand_def]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s0 0
     (OK (jump_to cond (update_var idx 0w ee)))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`jump_to cond (update_var idx 0w ee)`, `w`] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[lookup_var_def] >> metis_tac[]
QED

Theorem intcall_array_condition_entry:
  lookup_block cond fp.jc_func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst i EQ [Var idx; Lit (n2w n)] [dv];
       mk_inst j JNZ [Var dv; Label exit; Label bod] []]|> /\
  array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase p dst sz
    aa cond sa k es s /\ n = LENGTH vs /\ n < dimword (:256) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  not_local_ptr ce es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved = Var x ==> x <> dv) /\
  (!op. fp.jc_reserved op ==> op <> Var dv) ==>
  ?next. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK next) /\
    intcall_joint_res fp ce env es sa next /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase p dst sz
      aa (if k = n then exit else bod) sa k es next /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x s) /\
    next.vs_allocas = s.vs_allocas /\ next.vs_alloca_next = s.vs_alloca_next /\
    next.vs_memory = s.vs_memory /\ next.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
   lookup_var idx s = SOME (n2w k)` by fs[array_loop_inv_def] >>
  drule_all intcall_array_condition_resources >> simp[LET_THM] >> strip_tac >>
  `k < dimword (:256)` by (fs[array_loop_inv_def] >> decide_tac) >>
  `((n2w k:bytes32) = n2w n) = (k = n)` by
    simp[wordsTheory.n2w_11] >>
  qexists_tac `jump_to (if k = n then exit else bod)
    (update_var dv (bool_to_word (k = n)) s)` >> fs[] >>
  fs[array_loop_inv_def, intcall_joint_res_def, intcall_expr_res_def] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `saved` >> fs[eval_operand_def, lookup_var_def,
    jump_to_def, update_var_def, FLOOKUP_UPDATE]
QED
