(* General setup boundaries: no execution-history premise is used. *)
Theory bodyIntCallFamStmtForSetupGeneral
Ancestors
  bodyIntCallFamStmtForStart bodyIntCallFamStmtForSetup
  bodyIntCallJointContract bodyIntCallJointStmtJump stmtForRangeMemoryParts
  stmtSimDeclPath loweringSlice fragGasMode venomExecSemantics venomState
  compileEnv finite_map venomInst intCallFrame venomMemProps list

Theorem intcall_for_alloca_start_no_history:
  !fp ce env es s0 sa aa aid sz p pre lbl entry_lbl j.
    aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
    32 <= sz /\ sz < dimword (:256) /\
    lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
      SOME <|bb_label := lbl; bb_instructions :=
        pre ++ [aa; mk_inst j JMP [Label entry_lbl] []]|> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
    local_ptrs_reserved ce sa /\
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

Resume intcall_for_alloca_start_no_history[path]:
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
Finalise intcall_for_alloca_start_no_history

Theorem intcall_for_literal_start_no_history:
  aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  32 <= sz /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [aa; mk_inst j JMP [Label entry_lbl] []]|> /\
  lookup_block entry_lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := entry_lbl; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit a] [cv];
       mk_inst i2 ADD [Lit a; Lit (b-a)] [ev];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  local_ptrs_reserved ce sa /\
  MEM aa (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
  ALL_DISTINCT [p;cv;ev] /\
  not_local_ptr ce es.scopes p /\ not_local_ptr ce es.scopes cv /\
  not_local_ptr ce es.scopes ev /\
  (!x. not_fresh_at sa x ==> x <> p /\ x <> cv /\ x <> ev) ==>
  ?cc w. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    intcall_joint_res fp ce env es sa cc /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
    lookup_var p cc = SOME w /\ FLOOKUP cc.vs_allocas aid = SOME (w2n w,sz) /\
    (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0) /\
    (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent) /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    cc.vs_memory = s0.vs_memory /\ cc.vs_labels = s0.vs_labels
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> p` by metis_tac[] >>
  drule_all intcall_for_alloca_start_no_history >> strip_tac >>
  `!op. fp.jc_reserved op ==> op <> Var cv /\ op <> Var ev` by
    (fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  `cv <> ev` by fs[ALL_DISTINCT] >>
  drule_all intcall_for_literal_entry >> simp[LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F _ _ ee 0 (OK cc)` >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`cc`, `w`] >>
  simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE] >>
  fs[ALL_DISTINCT, lookup_var_def] >> metis_tac[]
QED
