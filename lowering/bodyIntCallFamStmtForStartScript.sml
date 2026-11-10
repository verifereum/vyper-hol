(* Joint resources at allocation and the memory-free range prefix. *)
Theory bodyIntCallFamStmtForStart
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtJump stmtForRangeMemoryStart
  bodyMemoryDefs stmtSimDeclPath stmtSimProps exprSimCopy intCallFrame loweringSlice venomMemProps
  venomStepProps venomExecSemantics venomState compileEnv finite_map
  stmtForRangeMemoryParts fragGasMode allocaHistory venomInst

Theorem intcall_joint_res_exec_alloca:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  fn_inst_ids_distinct fp.jc_func /\ MEM inst (fn_insts fp.jc_func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
  inst.inst_outputs = [p] /\ not_local_ptr ce es.scopes p /\
  ~not_fresh_at sa p /\ exec_alloca inst s n = OK t ==>
  intcall_joint_res fp ce env es sa t
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    (irule (cj 1 stmt_state_rel_exec_alloca) >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (drule_all exec_alloca_frames >> strip_tac >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory /\ s.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[exec_alloca_memory, exec_alloca_alloca_next_mono] >>
  `allocas_above fp.jc_lo t` by
    (fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >>
     drule (INST_TYPE [``:'a`` |-> ``:256``] exec_alloca_allocas_above) >>
     disch_then (qspecl_then [`inst`, `n:bytes32`] mp_tac) >>
     simp[result_allocas_above_def]) >>
  `!name b sz. local_region ce es.scopes t name b sz <=>
               local_region ce es.scopes s name b sz` by
    (irule copy_buffer_local_region_frame >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  `!op. fp.jc_reserved op ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> irule (INST_TYPE [``:'a`` |-> ``:256``]
       exec_alloca_operand_frame) >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  `ret_pc_ok ce sa t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`ce`, `s`, `sa`] >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def]) >>
  `return_buf_frame fp.jc_rb ce sa t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def]) >>
  fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `fp.jc_reserved fp.jc_rpc` by fs[intcall_frame_ok_def] >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_for_alloca_start:
  !fp ce env es s0 sa aa aid sz p pre lbl entry_lbl j.
    aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
    32 <= sz /\ sz < dimword (:256) /\
    lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
      SOME <|bb_label := lbl; bb_instructions :=
        pre ++ [aa; mk_inst j JMP [Label entry_lbl] []]|> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
    local_ptrs_reserved ce sa /\ alloca_history fp.jc_func s0 /\
    MEM aa (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
    not_local_ptr ce es.scopes p /\
    (!x. not_fresh_at sa x ==> x <> p) ==>
    ?ee w. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK ee) /\
      ee.vs_current_bb = entry_lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
      intcall_joint_res fp ce env es sa ee /\
      lookup_var p ee = SOME w /\ FLOOKUP ee.vs_allocas aid = SOME (w2n w,sz) /\
      ee.vs_memory = s0.vs_memory /\ ee.vs_labels = s0.vs_labels /\
      s0.vs_alloca_next <= ee.vs_alloca_next /\
      (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==>
                FLOOKUP ee.vs_allocas id = SOME ent) /\
      (!x. x <> p ==> lookup_var x ee = lookup_var x s0)
Proof
  rpt gen_tac >> strip_tac >>
  `?s1. exec_alloca aa s0 (n2w sz:bytes32) = OK s1` by
    (Cases_on `FLOOKUP s0.vs_allocas aa.inst_id`
     >- simp[exec_alloca_def, mk_inst_def] >>
     rename1 `FLOOKUP s0.vs_allocas aa.inst_id = SOME ent` >>
     PairCases_on `ent` >> simp[exec_alloca_def, mk_inst_def]) >>
  `intcall_joint_res fp ce env es sa s1` by
    (irule intcall_joint_res_exec_alloca >> simp[] >>
     qexistsl_tac [`aa`, `n2w sz`, `p`, `s0`] >>
     simp[mk_inst_def] >> metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0` by
    fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  drule stmt_state_rel_exec_alloca >>
  disch_then (qspecl_then [`aa`, `p`, `n2w sz`, `s1`] mp_tac) >>
  (impl_tac >- simp[mk_inst_def]) >> simp[mk_inst_def] >> strip_tac >>
  suspend "path"
QED

Resume intcall_for_alloca_start[path]:
  `s1.vs_current_bb = s0.vs_current_bb /\ ~s1.vs_halted /\
   s1.vs_labels = s0.vs_labels` by
    (qpat_assum `exec_alloca _ _ _ = _` mp_tac >>
     qpat_x_assum `aa = _` SUBST1_TAC >>
     qpat_x_assum `~s0.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exec_alloca_def, mk_inst_def, AllCaseEqs(), update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  `step_inst_base aa s0 = OK s1` by
    (qpat_assum `exec_alloca _ _ _ = _` mp_tac >>
     gvs[step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK (jump_to entry_lbl s1))` by
    (irule gas_marked_path_from_mem >> irule for_start_zero_path_mem >>
     simp[] >> qexists_tac `j` >> gvs[mk_inst_def]) >>
  drule_at (Pat `exec_alloca _ _ _ = _`) exec_alloca_frames >>
  disch_then (qspec_then `p` mp_tac) >> simp[mk_inst_def] >> strip_tac >>
  `s1.vs_memory = s0.vs_memory /\ s0.vs_alloca_next <= s1.vs_alloca_next` by
    metis_tac[exec_alloca_memory, exec_alloca_alloca_next_mono] >>
  qexistsl_tac [`jump_to entry_lbl s1`, `w`] >>
  simp[intcall_joint_res_jump_to, jump_to_def, lookup_var_def] >>
  fs[lookup_var_def]
QED
Finalise intcall_for_alloca_start
