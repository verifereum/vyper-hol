(* Memory-free range entry, retaining the joint resource at its concrete endpoint. *)
Theory bodyIntCallFamStmtForSetup
Ancestors
  bodyIntCallFamStmtForStart bodyIntCallFamStmtForTransport bodyIntCallJointStmtJump
  stmtForRangeMemoryParts fragGasMode venomState venomExecSemantics finite_map
  bodyIntCallJointContract list exprSimProps exprSimCopy compileEnv
  intCallFrame bodyMemoryDefs stmtSimProps stmtForRangeChecksMemory
  stmtSimForRange gasOutcome gasSummary vyperInterpreter vyperState
  vyperValue vyperValueOperation integer_word fragExec exprSimDefs
Libs
  monadsyntax

Theorem intcall_for_literal_entry:
  lookup_block entry_lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := entry_lbl; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit a] [cv];
       mk_inst i2 ADD [Lit a; Lit (b-a)] [ev];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  ee.vs_current_bb = entry_lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa ee /\
  cv <> ev /\ not_local_ptr ce es.scopes cv /\ not_local_ptr ce es.scopes ev /\
  (!op. fp.jc_reserved op ==> op <> Var cv /\ op <> Var ev) ==>
  let cc = jump_to cond_lbl (update_var ev b (update_var cv a ee)) in
  gas_marked_path F fp.jc_ctx fp.jc_func ee 0 (OK cc) /\
  cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  intcall_joint_res fp ce env es sa cc /\
  lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
  (!x. x <> cv /\ x <> ev ==> lookup_var x cc = lookup_var x ee) /\
  cc.vs_allocas = ee.vs_allocas /\ cc.vs_alloca_next = ee.vs_alloca_next /\
  cc.vs_memory = ee.vs_memory /\ cc.vs_labels = ee.vs_labels
Proof
  simp[LET_THM] >> strip_tac >>
  `a + (b-a) = b` by wordsLib.WORD_DECIDE_TAC >>
  `gas_marked_path F fp.jc_ctx fp.jc_func ee 0
    (OK (jump_to cond_lbl (update_var ev b (update_var cv a ee))))` by
    (irule gas_marked_path_from_mem >>
     drule_all for_entry_zero_path_mem >> simp[]) >>
  `intcall_joint_res fp ce env es sa (update_var cv a ee)` by
    (irule intcall_joint_res_update_var >> simp[] >> metis_tac[]) >>
  `intcall_joint_res fp ce env es sa (update_var ev b (update_var cv a ee))` by
    (irule intcall_joint_res_update_var >> simp[] >> metis_tac[]) >>
  simp[intcall_joint_res_jump_to, jump_to_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem intcall_for_literal_start:
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
  local_ptrs_reserved ce sa /\ alloca_history fp.jc_func s0 /\
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
  drule_all intcall_for_alloca_start >> strip_tac >>
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

Theorem intcall_joint_res_vars_frame:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  (!x. not_fresh_at sa x ==> lookup_var x (s with vs_vars := vs) = lookup_var x s) ==>
  intcall_joint_res fp ce env es sa (s with vs_vars := vs)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es (s with vs_vars := vs)` by
    (irule stmt_state_rel_vars_frame >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `!op. fp.jc_reserved op ==>
        eval_operand op (s with vs_vars := vs) = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def] >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  `!name b sz. local_region ce es.scopes (s with vs_vars := vs) name b sz <=>
              local_region ce es.scopes s name b sz` by
    (irule copy_buffer_local_region_frame >> fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> metis_tac[]) >>
  `ret_pc_ok ce sa (s with vs_vars := vs)` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`ce`, `s`, `sa`] >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def]) >>
  `return_buf_frame fp.jc_rb ce sa (s with vs_vars := vs)` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def]) >>
  fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def, allocas_above_def, intcall_frame_ok_def] >> metis_tac[]
QED

Theorem intcall_for_checked_entry:
  lookup_block lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      [mk_inst i ASSIGN [op1] [cv];
       mk_inst (i+1) SUB [op2;op1] [rv];
       mk_inst (i+2) cmp [op1;op2] [g1];
       mk_inst (i+3) ISZERO [Var g1] [z1];
       mk_inst (i+4) ASSERT [Var z1] [];
       mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
       mk_inst (i+6) ISZERO [Var g2] [z2];
       mk_inst (i+7) ASSERT [Var z2] [];
       mk_inst (i+8) ADD [op1;Var rv] [ev];
       mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  MEM cmp [SGT;GT] /\
  ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa ee /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) ==>
  (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
      w2n (b-a) > w2n (n2w bound : bytes32)) ==>
    ?t. gas_marked_path F fp.jc_ctx fp.jc_func ee 0 (Abort Revert_abort t)) /\
  (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
   ~(w2n (b-a) > w2n (n2w bound : bytes32)) ==>
  ?cc. gas_marked_path F fp.jc_ctx fp.jc_func ee 0 (OK cc) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    intcall_joint_res fp ce env es sa cc /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
    (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==> lookup_var x cc = lookup_var x ee) /\
    cc.vs_allocas = ee.vs_allocas /\ cc.vs_alloca_next = ee.vs_alloca_next /\
    cc.vs_memory = ee.vs_memory /\ cc.vs_labels = ee.vs_labels)
Proof
  strip_tac >>
  drule_all for_entry_checked_path_mem >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  conj_tac
  >- (disch_tac >>
      qpat_x_assum `_ \/ _ ==> ?t. _` mp_tac >> simp[] >> strip_tac >>
      qexists_tac `t` >> irule gas_marked_path_from_mem >>
      fs[gas_marked_path_def]) >>
  strip_tac >>
  qpat_x_assum `_ /\ _ ==> ?vs. _` drule_all >> strip_tac >>
  `intcall_joint_res fp ce env es sa (ee with vs_vars := vs)` by
    (irule intcall_joint_res_vars_frame >> simp[] >> metis_tac[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func ee 0
     (OK (jump_to cond_lbl (ee with vs_vars := vs)))` by
    (irule gas_marked_path_from_mem >> fs[gas_marked_path_def]) >>
  qexists_tac `jump_to cond_lbl (ee with vs_vars := vs)` >>
  simp[intcall_joint_res_jump_to, jump_to_def, lookup_var_def] >>
  fs[lookup_var_def] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem intcall_for_checked_start:
  aa = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  32 <= sz /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb fp.jc_func.fn_blocks =
    SOME <|bb_label := start_lbl; bb_instructions :=
      pre ++ [aa; mk_inst j JMP [Label lbl] []]|> /\
  lookup_block lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      [mk_inst i ASSIGN [op1] [cv];
       mk_inst (i+1) SUB [op2;op1] [rv];
       mk_inst (i+2) cmp [op1;op2] [g1];
       mk_inst (i+3) ISZERO [Var g1] [z1];
       mk_inst (i+4) ASSERT [Var z1] [];
       mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
       mk_inst (i+6) ISZERO [Var g2] [z2];
       mk_inst (i+7) ASSERT [Var z2] [];
       mk_inst (i+8) ADD [op1;Var rv] [ev];
       mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  MEM cmp [SGT;GT] /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  eval_operand op1 s0 = SOME a /\ eval_operand op2 s0 = SOME b /\
  ALL_DISTINCT [p;cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  local_ptrs_reserved ce sa /\ alloca_history fp.jc_func s0 /\
  MEM aa (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
  not_local_ptr ce es.scopes p /\
  (!x. not_fresh_at sa x ==> ~MEM x [p;cv;rv;g1;z1;g2;z2;ev]) ==>
  (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
      w2n (b-a) > w2n (n2w bound : bytes32)) ==>
    ?t. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (Abort Revert_abort t)) /\
  (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
   ~(w2n (b-a) > w2n (n2w bound : bytes32)) ==>
  ?cc w. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    intcall_joint_res fp ce env es sa cc /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
    lookup_var p cc = SOME w /\ FLOOKUP cc.vs_allocas aid = SOME (w2n w,sz) /\
    (!x. not_fresh_at sa x ==> lookup_var x cc = lookup_var x s0) /\
    (!id ent. FLOOKUP s0.vs_allocas id = SOME ent ==> FLOOKUP cc.vs_allocas id = SOME ent) /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    cc.vs_memory = s0.vs_memory /\ cc.vs_labels = s0.vs_labels)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> p` by (fs[] >> metis_tac[]) >>
  drule_all intcall_for_alloca_start >> strip_tac >>
  `eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b` by
    (conj_tac >> Cases_on `op1` >> Cases_on `op2` >>
     fs[eval_operand_def] >> metis_tac[]) >>
  `ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
   (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
   (!x. not_fresh_at sa x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev])` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  drule_all intcall_for_checked_entry >> strip_tac >>
  conj_tac
  >- (disch_tac >> qpat_x_assum `_ \/ _ ==> ?t. _` drule >> strip_tac >>
      qexists_tac `t` >> drule_all gas_marked_path_then >> simp[]) >>
  strip_tac >> qpat_x_assum `_ /\ _ ==> ?cc. _` drule_all >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK cc)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`cc`, `w`] >> simp[] >> fs[ALL_DISTINCT] >> metis_tac[]
QED

(* Connect the machine checks to the source tail without weakening its exit post. *)
Theorem intcall_for_checked_range_outcome:
  is_int_type fty /\ evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) /\
  (((if is_signed_type fty then word_gt (i2w n1 : bytes32) (i2w n2)
      else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) \/
     w2n (i2w n2 - i2w n1 : bytes32) > w2n (n2w bound : bytes32)) ==>
    ?t. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (Abort Revert_abort t)) /\
  (n1 <= n2 /\ Num (n2 - n1) <= bound ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_for fp.jc_cx tyv id stmts
        (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))))
      (es,s0) Q (intcall_stmt_exit fp)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for fp.jc_cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,s0) Q (intcall_stmt_exit fp)
Proof
  strip_tac >> drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
  disch_then (qspecl_then [`n1`, `n2`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `n1 <= n2`
  >- (Cases_on `Num (n2 - n1) <= bound`
      >- (simp[get_range_limits_def, lift_sum_def, check_def, assert_def,
               compatible_bound_def, lambdify vyperStateTheory.bind_def,
               vyperStateTheory.ignore_bind_def, lambdify vyperStateTheory.assert_def,
               lambdify vyperStateTheory.return_def] >>
          metis_tac[]) >>
      `?t. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (Abort Revert_abort t)` by
        (qpat_x_assum `_ \/ _ ==> ?t. _` irule >> simp[]) >>
      suspend "bound") >>
  `?t. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (Abort Revert_abort t)` by
    (qpat_x_assum `_ \/ _ ==> ?t. _` irule >> simp[] >> intLib.ARITH_TAC) >>
  suspend "order"
QED

Resume intcall_for_checked_range_outcome[bound]:
  simp[get_range_limits_def, lift_sum_def, check_def, assert_def,
       compatible_bound_def, lambdify vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, lambdify vyperStateTheory.return_def,
       lambdify vyperStateTheory.assert_def, lambdify vyperStateTheory.raise_def] >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "For too long"))`, `es`,
               `Abort Revert_abort t`] >>
  simp[gas_marked_exec_def, raise_def, exit_result_def,
       intcall_stmt_exit_def, expr_exit_def]
QED

Resume intcall_for_checked_range_outcome[order]:
  simp[get_range_limits_def, lift_sum_def,
       lambdify vyperStateTheory.bind_def, lambdify vyperStateTheory.raise_def] >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "no range"))`, `es`,
               `Abort Revert_abort t`] >>
  simp[gas_marked_exec_def, raise_def, exit_result_def,
       intcall_stmt_exit_def, expr_exit_def]
QED
Finalise intcall_for_checked_range_outcome
