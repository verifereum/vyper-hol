(* Counted array loops for intcall statement producers, independent of how
   the iterator is stored. The condition compares the counter with any
   length operand; the element copy into the loop variable and the scope
   invariant P are callbacks. Fixed, dynamic and immutable iterators share
   these theorems.

   TOP-LEVEL: intcall_array_gen_condition, intcall_array_gen_finish,
              intcall_array_gen_round_at_body, intcall_array_gen_round,
              intcall_array_gen_iterations, intcall_array_gen_loop *)
Theory bodyIntCallFamStmtForArrayGen
Ancestors
  bodyIntCallFamStmtForRange bodyIntCallFamStmtForRound
  bodyIntCallFamStmtForTransport bodyIntCallJointContract
  bodyIntCallJointStmtJump stmtSimForArrayLoop stmtSimForRounds
  stmtForRangeMemoryRound stmtSimDeclCompose stmtSimProps stmtSimDefs
  compileEnv fragGasMode fragGasPathMem exprSimMemDefs exprSimWordArgs
  gasOutcome loweringPosts bodySimDeclCases vyperEvalPreservesScopes
  vyperInterpreter vyperState venomState venomExecSemantics venomInst
  finite_map list rich_list arithmetic

(* The loop condition: EQ of the counter with a length operand, then JNZ. *)
Theorem intcall_array_gen_condition:
  lookup_block cond fp.jc_func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst i EQ [Var idx; lvo] [dv];
       mk_inst j JNZ [Var dv; Label exit; Label bod] []]|> /\
  array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
    p dst sz aa cond sa k es s /\
  eval_operand lvo s = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  not_local_ptr ce es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved = Var x ==> x <> dv) /\
  (!op. fp.jc_reserved op ==> op <> Var dv) ==>
  ?next. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK next) /\
    intcall_joint_res fp ce env es sa next /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
      p dst sz aa (if k = LENGTH vs then exit else bod) sa k es next /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x s) /\
    next.vs_allocas = s.vs_allocas /\ next.vs_alloca_next = s.vs_alloca_next /\
    next.vs_memory = s.vs_memory /\ next.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
   lookup_var idx s = SOME (n2w k)` by fs[array_loop_inv_def] >>
  `k < dimword (:256)` by (fs[array_loop_inv_def] >> decide_tac) >>
  `((n2w k:bytes32) = n2w (LENGTH vs)) = (k = LENGTH vs)` by
    simp[wordsTheory.n2w_11] >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
     (OK (jump_to (if (n2w k:bytes32) = n2w (LENGTH vs) then exit else bod)
       (update_var dv (bool_to_word ((n2w k:bytes32) = n2w (LENGTH vs))) s)))` by
    (irule eq_branch_zero_path >> simp[] >>
     qexistsl_tac [`i`, `j`, `Var idx`, `lvo`] >>
     simp[get_instruction_def, eval_operand_def]) >>
  `intcall_joint_res fp ce env es sa
     (jump_to (if k = LENGTH vs then exit else bod)
       (update_var dv (bool_to_word (k = LENGTH vs)) s))` by
    (simp[intcall_joint_res_jump_to] >>
     irule intcall_joint_res_update_var >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to (if k = LENGTH vs then exit else bod)
    (update_var dv (bool_to_word (k = LENGTH vs)) s)` >>
  gvs[] >>
  fs[array_loop_inv_def, intcall_joint_res_def, intcall_expr_res_def] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `saved` >> fs[eval_operand_def, lookup_var_def,
    jump_to_def, update_var_def, FLOOKUP_UPDATE]
QED

(* From where the body lands to the increment block (or the exit). *)
Theorem intcall_array_gen_route[local]:
  (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr] []] /\
     fn_has_code sb1 sj fp.jc_func) /\
  stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb1) /\
  intcall_joint_res fp ce env es sb1 t ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_joint_res fp ce env es sb1 u /\
    u = (if res = INL () then jump_to incr t else t) /\
    u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    (res = INR BreakException ==> u.vs_current_bb = exit) /\
    (res <> INR BreakException ==> u.vs_current_bb = incr)
Proof
  strip_tac >> Cases_on `res = INL ()`
  >- (qexists_tac `jump_to incr t` >>
      gvs[stmt_lands_def, intcall_joint_res_jump_to] >>
      conj_tac
      >- (irule gas_marked_path_from_mem >>
          irule emit_jump_zero_path_mem >> metis_tac[]) >>
      simp[jump_to_def]) >>
  qexists_tac `t` >> gvs[stmt_lands_def] >>
  irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]
QED

(* From where the body lands to the next condition test (or the exit). *)
Theorem intcall_array_gen_finish:
  lookup_block incr fp.jc_func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr] []] /\
     fn_has_code sb1 sj fp.jc_func) /\
  stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb1) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sb1 t /\
  not_local_ptr ce es.scopes idx /\ not_local_ptr ce es.scopes nv /\
  idx <> nv /\ (!op. fp.jc_reserved op ==> op <> Var idx /\ op <> Var nv) /\
  lookup_var idx t = SOME c ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_joint_res fp ce env es sb1 u /\ ~u.vs_halted /\
    u.vs_inst_idx = 0 /\
    (res = INR BreakException ==> u.vs_current_bb = exit) /\
    (res <> INR BreakException ==>
      u.vs_current_bb = cond /\ lookup_var idx u = SOME (c + 1w)) /\
    (!x. x <> idx /\ x <> nv ==> lookup_var x u = lookup_var x t) /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    u.vs_memory = t.vs_memory /\ u.vs_labels = t.vs_labels
Proof
  strip_tac >>
  qpat_x_assum `~block_is_terminated sb1 ==> _` assume_tac >>
  drule_all intcall_array_gen_route >> strip_tac >>
  `intcall_joint_res fp ce env es sb1 u /\
   lookup_var idx u = SOME c /\ u.vs_allocas = t.vs_allocas /\
   u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_memory = t.vs_memory /\ u.vs_labels = t.vs_labels /\
   (!x. lookup_var x u = lookup_var x t)` by
    (Cases_on `res = INL ()` >> gvs[jump_to_def, lookup_var_def]) >>
  Cases_on `res = INR BreakException`
  >- (qexists_tac `u` >> simp[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func u 0
    (OK (jump_to cond (update_var idx (c + 1w) (update_var nv (c + 1w) u)))) /\
   intcall_joint_res fp ce env es sb1
    (jump_to cond (update_var idx (c + 1w) (update_var nv (c + 1w) u)))` by
    (irule intcall_for_increment_resources >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to cond (update_var idx (c + 1w) (update_var nv (c + 1w) u))` >>
  conj_tac
  >- (qpat_assum `gas_marked_path _ _ _ t _ _`
        (mp_then Any mp_tac gas_marked_path_then) >>
      disch_then drule >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  Cases_on `res = INL ()` >>
  fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* One round from the body's start state s2: the body outcome Q becomes the
   round outcome at the next condition test. Every variable the loop holds
   (the element slot p, the length and base operands) survives the round. *)
Theorem intcall_array_gen_round_at_body:
  let entry = es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
                          value := v; popped := []|>)) :: es.scopes;
      Q = (\res ee t. ?ce'' env''.
        stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb1) /\
        cenv_top_ext bc ce'' ee.scopes /\
        intcall_joint_res fp ce'' env'' ee sb1 t /\
        (!x z. not_fresh_at sb0 x /\ lookup_var x s2 = SOME z ==>
               lookup_var x t = SOME z) /\
        (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        s2.vs_alloca_next <= t.vs_alloca_next);
      H = (\res ee u. ?broke. res = INL broke /\
        u.vs_inst_idx = 0 /\ ~u.vs_halted /\
        intcall_joint_res fp ce env ee sc u /\
        (!x z. not_fresh_at sc x /\ lookup_var x cc = SOME z ==>
               lookup_var x u = SOME z) /\
        (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
                 FLOOKUP u.vs_allocas aid = SOME b) /\
        cc.vs_alloca_next <= u.vs_alloca_next /\
        (broke ==> u.vs_current_bb = exit) /\
        (~broke ==>
          array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved
            arrbase p dst sz aa cond sc (k + 1) ee u /\
          eval_operand lvo u = SOME (n2w (LENGTH vs))))
  in
  lookup_block incr fp.jc_func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr] []] /\
     fn_has_code sb1 sj fp.jc_func) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc cc /\
  cenv_top_ext ce bc entry.scopes /\ local_ptrs_reserved ce sb1 /\
  (!scs. not_local_ptr ce scs idx /\ not_local_ptr ce scs nv) /\ idx <> nv /\
  (!op. fp.jc_reserved op ==> op <> Var idx /\ op <> Var nv) /\
  (!x. not_fresh_at sc x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  (!x. x = p \/ lvo = Var x \/ saved = Var x ==>
       not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  (!l. lvo <> Label l) /\ (!l. saved <> Label l) /\
  array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
    p dst sz aa cond sc k es cc /\
  eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\ k < LENGTH vs /\
  not_fresh_at sb0 idx /\ ~s2.vs_halted /\ lookup_var idx s2 = SOME (n2w k) /\
  (!x. not_fresh_at sc x \/ x = p \/ lvo = Var x \/ saved = Var x ==>
       lookup_var x s2 = lookup_var x cc) /\
  (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
           FLOOKUP s2.vs_allocas aid = SOME b) /\
  cc.vs_alloca_next <= s2.vs_alloca_next /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\ value_has_type tyv v /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b /\
  call_evaluation_safe fp.jc_cx (int_calls_stmts stmts) /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmts fp.jc_tops bindings stmts /\
  (!gs res ee. eval_stmts fp.jc_cx stmts (entry with gas_obs := gs) = (res,ee) /\
     ee.scopes <> [] ==> P (ee with scopes := TL ee.scopes)) /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_stmts fp.jc_cx stmts) (entry,s2) Q (intcall_stmt_exit fp) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (ignore_bind (push_scope_with_var id tyv v)
      (finally (try (ignore_bind (eval_stmts fp.jc_cx stmts) (return F))
                     handle_loop_exception) pop_scope))
    (es,s2) H (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qhdtm_assum `gas_outcome`
    (mp_then Any mp_tac intcall_for_round_outcome) >>
  disch_then irule >> simp[] >>
  conj_tac >- suspend "exit" >> suspend "normal"
QED
Resume intcall_array_gen_round_at_body[exit]:
  rpt gen_tac >> strip_tac >>
  `ee.scopes <> []` by
    (drule eval_stmts_preserves_scopes_len >>
     simp[] >> strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  drule intcall_stmt_exit_no_loop_control >> strip_tac >> gvs[]
QED
Resume intcall_array_gen_round_at_body[normal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  conj_asm1_tac >- fs[stmt_lands_def] >>
  `preserves_scopes_dom
     (es with <|scopes := (FEMPTY |+ (id,
       <|assignable := F; type := tyv; value := v; popped := []|>)) ::
       es.scopes; gas_obs := gs|>) ee` by
    metis_tac[eval_stmts_preserves_scopes_dom] >>
  `ee.scopes <> []` by fs[preserves_scopes_dom_def] >>
  `cenv_top_ext ce ce'' ee.scopes` by
    (irule cenv_top_ext_trans >> qexists_tac `bc` >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     fs[preserves_scopes_dom_def]) >>
  `lookup_scopes id es.scopes = NONE` by fs[array_loop_inv_def] >>
  `intcall_joint_res fp ce env (es with gas_obs := gs) sc cc` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_gas_obs] >>
     metis_tac[]) >>
  `intcall_joint_res fp ce env (ee with scopes := TL ee.scopes) sb1 t` by
    (irule (cj 2 intcall_for_body_pop_resources) >>
     simp[] >> reverse conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `P (ee with scopes := TL ee.scopes)` by
    (qpat_x_assum `!gs res ee. eval_stmts _ _ _ = _ /\ _ ==> _`
       (qspecl_then [`gs`, `res`, `ee`] mp_tac) >>
     fs[]) >>
  `lookup_scopes id (TL ee.scopes) = NONE` by
    (irule lookup_scopes_none_map_fdom >>
     qexists_tac `es.scopes` >> fs[preserves_scopes_dom_def]) >>
  `lookup_var idx t = SOME (n2w k)` by metis_tac[] >>
  `(res = INL () ==> ~block_is_terminated sb1)` by metis_tac[] >>
  `not_local_ptr ce (TL ee.scopes) idx /\ not_local_ptr ce (TL ee.scopes) nv`
    by simp[] >>
  mp_tac (Q.INST [`es` |-> `ee with scopes := TL ee.scopes`, `c` |-> `n2w k`]
    intcall_array_gen_finish) >>
  impl_tac >- simp[] >> strip_tac >>
  `intcall_joint_res fp ce env (ee with scopes := TL ee.scopes) sc u` by
    (`local_ptrs_reserved ce sc /\
      (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sc x)` by
       fs[intcall_joint_res_def, intcall_expr_res_def] >>
     irule intcall_joint_res_reentry >> simp[] >>
     qexists_tac `sb1` >> simp[]) >>
  `!x z. (not_fresh_at sc x \/ x = p \/ lvo = Var x \/ saved = Var x) /\
         lookup_var x cc = SOME z ==> lookup_var x u = SOME z` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sb0 x /\ x <> idx /\ x <> nv /\
      lookup_var x s2 = SOME z` by metis_tac[] >>
     metis_tac[]) >>
  `!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b` by metis_tac[] >>
  `cc.vs_alloca_next <= u.vs_alloca_next` by
    metis_tac[LESS_EQ_TRANS] >>
  simp[] >> qexists_tac `u` >> simp[] >>
  strip_tac >>
  `eval_operand lvo u = SOME (n2w (LENGTH vs))` by
    (Cases_on `lvo` >> fs[eval_operand_def] >> metis_tac[]) >>
  `lookup_var p u = SOME dst /\ eval_operand saved u = SOME arrbase /\
   FLOOKUP u.vs_allocas aa.inst_id = SOME (w2n dst,sz)` by
    (fs[array_loop_inv_def] >>
     Cases_on `saved` >> fs[eval_operand_def] >> metis_tac[]) >>
  fs[array_loop_inv_def, intcall_joint_res_def, intcall_expr_res_def,
     wordsTheory.word_add_n2w]
QED
Finalise intcall_array_gen_round_at_body

(* One round from the condition test: test, element copy (callback), the
   body by the joint induction hypothesis, increment. *)
Theorem intcall_array_gen_round:
  let entry = es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
                          value := EL k vs; popped := []|>)) :: es.scopes;
      H = (\res ee u. ?broke. res = INL broke /\
        u.vs_inst_idx = 0 /\ ~u.vs_halted /\
        intcall_joint_res fp ce env ee sc u /\
        (!x z. not_fresh_at sc x /\ lookup_var x cc = SOME z ==>
               lookup_var x u = SOME z) /\
        (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
                 FLOOKUP u.vs_allocas aid = SOME b) /\
        cc.vs_alloca_next <= u.vs_alloca_next /\
        (broke ==> u.vs_current_bb = exit) /\
        (~broke ==>
          array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved
            arrbase p dst sz aa cond sc (k + 1) ee u /\
          eval_operand lvo u = SOME (n2w (LENGTH vs))))
  in
  lookup_block cond fp.jc_func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  lookup_block incr fp.jc_func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr] []] /\
     fn_has_code sb1 sj fp.jc_func) /\
  stmts_env bc (InLoop exit incr)
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 =
    (ce_b,sb1) /\
  fn_has_code sb0 sb1 fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~block_is_terminated sb0 /\ local_ptrs_reserved ce sb1 /\
  intcall_stmts_producer fp stmts /\ intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sc cc /\
  array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
    p dst sz aa cond sc k es cc /\
  eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\
  (!scs. not_local_ptr ce scs idx /\ not_local_ptr ce scs dv /\
         not_local_ptr ce scs nv) /\
  ALL_DISTINCT [idx; dv; nv; p] /\
  (!op. fp.jc_reserved op ==> op <> Var idx /\ op <> Var dv /\ op <> Var nv) /\
  (!x. not_fresh_at sc x ==>
       not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
  (!x. x = p \/ lvo = Var x \/ saved = Var x ==>
       not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
  (!l. lvo <> Label l) /\ (!l. saved <> Label l) /\ not_fresh_at sb0 idx /\
  (!next.
     array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
       p dst sz aa bod sc k es next /\
     intcall_joint_res fp ce env es sc next ==>
     ?s2. gas_marked_path F fp.jc_ctx fp.jc_func next 0 (OK s2) /\
       intcall_joint_res fp bc (extend_local env id fty F) entry sb0 s2 /\
       s2.vs_current_bb = sb0.cs_current_bb /\
       s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
       (!x. not_fresh_at sc x \/ x = idx \/ x = p \/ lvo = Var x \/
            saved = Var x ==> lookup_var x s2 = lookup_var x next) /\
       (!aid b. FLOOKUP next.vs_allocas aid = SOME b ==>
                FLOOKUP s2.vs_allocas aid = SOME b) /\
       next.vs_alloca_next <= s2.vs_alloca_next) /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\
  value_has_type tyv (EL k vs) /\
  body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmts fp.jc_tops bindings stmts /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target fp.jc_tops) /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b /\
  IS_SOME (type_stmts ((extend_local env id fty F) with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmts) /\
  stmts_exprs_ok bc stmts /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts stmts) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmts stmts) /\
  (!gs res ee. eval_stmts fp.jc_cx stmts (entry with gas_obs := gs) = (res,ee) /\
     ee.scopes <> [] ==> P (ee with scopes := TL ee.scopes)) /\
  gas_admissible (eval_for fp.jc_cx tyv id stmts (MAP Value (DROP k vs)))
    (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (ignore_bind (push_scope_with_var id tyv (EL k vs))
      (finally (try (ignore_bind (eval_stmts fp.jc_cx stmts) (return F))
                     handle_loop_exception) pop_scope))
    (es,cc) H (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `lookup_scopes id es.scopes = NONE` by fs[array_loop_inv_def] >>
  `?next. gas_marked_path F fp.jc_ctx fp.jc_func cc 0 (OK next) /\
     intcall_joint_res fp ce env es sc next /\
     array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
       p dst sz aa (if k = LENGTH vs then exit else bod) sc k es next /\
     (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
     next.vs_allocas = cc.vs_allocas /\
     next.vs_alloca_next = cc.vs_alloca_next /\
     next.vs_memory = cc.vs_memory /\ next.vs_labels = cc.vs_labels` by
    (irule intcall_array_gen_condition >> fs[ALL_DISTINCT] >> metis_tac[]) >>
  `array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
     p dst sz aa bod sc k es next` by gvs[] >>
  qpat_x_assum `!next. array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ bod _ _ _ next /\ _ ==> _`
    drule_all >> strip_tac >>
  suspend "body"
QED
Resume intcall_array_gen_round[body]:
  `gas_admissible (eval_stmts fp.jc_cx stmts) (stmt_res_ok (InLoop exit incr))
     (es with scopes := (FEMPTY |+ (id,
       <|assignable := F; type := tyv; value := EL k vs; popped := []|>)) ::
       es.scopes)` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[Once rich_listTheory.DROP_CONS_EL] >>
     disch_then (mp_then Any mp_tac for_round_body_admissible) >> simp[]) >>
  `cenv_top_ext ce bc ((FEMPTY |+ (id,
     <|assignable := F; type := tyv; value := EL k vs; popped := []|>)) ::
     es.scopes)` by
    (drule cenv_top_ext_declare_local >> simp[]) >>
  `!x. not_fresh_at sc x \/ x = p \/ lvo = Var x \/ saved = Var x ==>
       lookup_var x s2 = lookup_var x cc` by
    (rpt strip_tac >> gvs[] >> fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_var idx s2 = SOME (n2w k)` by
    (fs[array_loop_inv_def, ALL_DISTINCT] >> metis_tac[]) >>
  `(!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
            FLOOKUP s2.vs_allocas aid = SOME b) /\
   cc.vs_alloca_next <= s2.vs_alloca_next` by metis_tac[] >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
     (eval_stmts fp.jc_cx stmts)
     (es with scopes := (FEMPTY |+ (id,
       <|assignable := F; type := tyv; value := EL k vs; popped := []|>)) ::
       es.scopes,s2)
     (\res ee t. ?ce'' env''.
        stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb1) /\
        cenv_top_ext bc ce'' ee.scopes /\
        intcall_joint_res fp ce'' env'' ee sb1 t /\
        (!x z. not_fresh_at sb0 x /\ lookup_var x s2 = SOME z ==>
               lookup_var x t = SOME z) /\
        (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        s2.vs_alloca_next <= t.vs_alloca_next)
     (intcall_stmt_exit fp)` by suspend "producer" >>
  irule gas_outcome_zero_prefix >> qexists_tac `next` >> simp[] >>
  irule gas_outcome_zero_prefix >> qexists_tac `s2` >> simp[] >>
  mp_tac (INST [``v:value`` |-> ``EL k (vs:value list)``]
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
      (INST_TYPE [alpha |-> ``:value``] intcall_array_gen_round_at_body)))) >>
  impl_tac >- (fs[ALL_DISTINCT] >> metis_tac[]) >>
  simp[]
QED
Resume intcall_array_gen_round[producer]:
  irule gas_outcome_post_mono >>
  qhdtm_x_assum `intcall_stmts_producer`
    (irule_at Any o SRULE [intcall_stmts_producer_def]) >>
  simp[] >>
  qhdtm_assum `stmts_env` (irule_at Any) >> simp[] >>
  qpat_assum `type_stmts _ _ _ = SOME env_b` (irule_at Any) >> simp[] >>
  qhdtm_assum `supported_stmts` (irule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `intcall_joint_res fp ce_end env_end ee sb1 t` >>
  qexistsl_tac [`ce_end`, `env_end`] >> simp[]
QED
Finalise intcall_array_gen_round

(* Finite counted iteration of rounds that keep the length operand. *)
Theorem intcall_array_gen_iterations:
  let Fr = (\s.
        (!x z. not_fresh_at sc x /\ lookup_var x origin = SOME z ==>
               lookup_var x s = SOME z) /\
        (!aid b. FLOOKUP origin.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        origin.vs_alloca_next <= s.vs_alloca_next);
      Inv = (\k es s.
        array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved
          arrbase p dst sz aa cond sc k es s /\
        eval_operand lvo s = SOME (n2w (LENGTH vs)) /\
        intcall_joint_res fp ce env es sc s /\ Fr s);
      Done = (\es s. s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\
        ~s.vs_halted /\ intcall_joint_res fp ce env es sc s /\ Fr s);
      H = (\k cc res ee u. ?broke. res = INL broke /\
        u.vs_inst_idx = 0 /\ ~u.vs_halted /\
        intcall_joint_res fp ce env ee sc u /\
        (!x z. not_fresh_at sc x /\ lookup_var x cc = SOME z ==>
               lookup_var x u = SOME z) /\
        (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
                 FLOOKUP u.vs_allocas aid = SOME b) /\
        cc.vs_alloca_next <= u.vs_alloca_next /\
        (broke ==> u.vs_current_bb = exit) /\
        (~broke ==>
          array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved
            arrbase p dst sz aa cond sc (k + 1) ee u /\
          eval_operand lvo u = SOME (n2w (LENGTH vs))))
  in
  (!k es cc. k < LENGTH vs /\ Inv k es cc /\
    gas_admissible (eval_for fp.jc_cx tyv id stmts (MAP Value (DROP k vs)))
      (stmt_res_ok lctx) es ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (ignore_bind (push_scope_with_var id tyv (EL k vs))
        (finally (try (ignore_bind (eval_stmts fp.jc_cx stmts) (return F))
                       handle_loop_exception) pop_scope))
      (es,cc) (H k cc)
      (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)) /\
  intcall_frame_ok fp /\
  lookup_block cond fp.jc_func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  LENGTH vs < dimword (:256) /\
  (!scs. not_local_ptr ce scs dv) /\ dv <> idx /\ dv <> p /\
  (!x. saved = Var x ==> x <> dv) /\
  (!op. fp.jc_reserved op ==> op <> Var dv) /\
  (!x. not_fresh_at sc x ==> x <> dv) ==>
  !k es s. k <= LENGTH vs /\ Inv k es s /\
    gas_admissible (eval_for fp.jc_cx tyv id stmts (MAP Value (DROP k vs)))
      (stmt_res_ok lctx) es ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_for fp.jc_cx tyv id stmts (MAP Value (DROP k vs))) (es,s)
      (\res ee t. res = INL () /\ Done ee t)
      (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)
Proof
  BasicProvers.LET_ELIM_TAC >>
  irule (eval_for_value_rounds |> SPEC_ALL |>
    Q.INST [`R` |-> `\ex ee r. intcall_stmt_exit fp (INR ex) ee r`] |>
    SRULE []) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`Inv`, `stmt_res_ok lctx`] >> simp[] >>
  conj_tac >- suspend "final" >> suspend "round"
QED
Resume intcall_array_gen_iterations[final]:
  rpt strip_tac >> rename1 `Inv (LENGTH vs) ee cc` >>
  fs[Abbr `Inv`] >>
  `?next. gas_marked_path F fp.jc_ctx fp.jc_func cc 0 (OK next) /\
     intcall_joint_res fp ce env ee sc next /\
     array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
       p dst sz aa (if LENGTH vs = LENGTH vs then exit else bod) sc
       (LENGTH vs) ee next /\
     (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
     next.vs_allocas = cc.vs_allocas /\
     next.vs_alloca_next = cc.vs_alloca_next /\
     next.vs_memory = cc.vs_memory /\ next.vs_labels = cc.vs_labels` by
    (irule intcall_array_gen_condition >> simp[] >> metis_tac[]) >>
  qexists_tac `next` >> fs[Abbr `Done`, array_loop_inv_def] >>
  conj_tac
  >- (fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_gas_obs] >>
      metis_tac[]) >>
  fs[Abbr `Fr`] >> metis_tac[]
QED
Resume intcall_array_gen_iterations[round]:
  rpt strip_tac >> rename1 `Inv kk ee cc` >>
  irule gas_outcome_post_mono >>
  qexists_tac `H kk cc` >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  fs[Abbr `H`, Abbr `Inv`, Abbr `Done`, Abbr `Fr`] >>
  rpt strip_tac >> qexists_tac `broke` >>
  simp[ADD1] >> metis_tac[LESS_EQ_TRANS]
QED
Finalise intcall_array_gen_iterations

(* The whole counted loop, from the first condition test to the exit: the
   iterator-specific parts are the element copy and the invariant P. *)
Theorem intcall_array_gen_loop:
  let Fr = (\s.
        (!x z. not_fresh_at sc x /\ lookup_var x origin = SOME z ==>
               lookup_var x s = SOME z) /\
        (!aid b. FLOOKUP origin.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        origin.vs_alloca_next <= s.vs_alloca_next);
      Inv = (\k es s.
        array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved
          arrbase p dst sz aa cond sc k es s /\
        eval_operand lvo s = SOME (n2w (LENGTH vs)) /\
        intcall_joint_res fp ce env es sc s /\ Fr s);
      Done = (\es s. s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\
        ~s.vs_halted /\ intcall_joint_res fp ce env es sc s /\ Fr s)
  in
  lookup_block cond fp.jc_func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  lookup_block incr fp.jc_func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr] []] /\
     fn_has_code sb1 sj fp.jc_func) /\
  stmts_env bc (InLoop exit incr)
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 =
    (ce_b,sb1) /\
  fn_has_code sb0 sb1 fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~block_is_terminated sb0 /\ local_ptrs_reserved ce sb1 /\
  intcall_stmts_producer fp stmts /\ intcall_frame_ok fp /\
  LENGTH vs < dimword (:256) /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\
  (!scs. not_local_ptr ce scs idx /\ not_local_ptr ce scs dv /\
         not_local_ptr ce scs nv) /\
  ALL_DISTINCT [idx; dv; nv; p] /\
  (!op. fp.jc_reserved op ==> op <> Var idx /\ op <> Var dv /\ op <> Var nv) /\
  (!x. not_fresh_at sc x ==>
       not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
  (!x. x = p \/ lvo = Var x \/ saved = Var x ==>
       not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
  (!l. lvo <> Label l) /\ (!l. saved <> Label l) /\ not_fresh_at sb0 idx /\
  (!k es next. k < LENGTH vs /\
     array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
       p dst sz aa bod sc k es next /\
     intcall_joint_res fp ce env es sc next ==>
     ?s2. gas_marked_path F fp.jc_ctx fp.jc_func next 0 (OK s2) /\
       intcall_joint_res fp bc (extend_local env id fty F)
         (es with scopes :=
           (FEMPTY |+ (id, <|assignable := F; type := tyv;
                             value := EL k vs; popped := []|>)) :: es.scopes)
         sb0 s2 /\
       s2.vs_current_bb = sb0.cs_current_bb /\
       s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
       (!x. not_fresh_at sc x \/ x = idx \/ x = p \/ lvo = Var x \/
            saved = Var x ==> lookup_var x s2 = lookup_var x next) /\
       (!aid b. FLOOKUP next.vs_allocas aid = SOME b ==>
                FLOOKUP s2.vs_allocas aid = SOME b) /\
       next.vs_alloca_next <= s2.vs_alloca_next) /\
  (!k es gs res ee. k < LENGTH vs /\ P es /\
     lookup_scopes id es.scopes = NONE /\
     eval_stmts fp.jc_cx stmts
       ((es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tyv;
                            value := EL k vs; popped := []|>)) :: es.scopes)
        with gas_obs := gs) = (res,ee) /\
     ee.scopes <> [] ==> P (ee with scopes := TL ee.scopes)) /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\
  (!k. k < LENGTH vs ==> value_has_type tyv (EL k vs)) /\
  body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmts fp.jc_tops bindings stmts /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target fp.jc_tops) /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b /\
  IS_SOME (type_stmts ((extend_local env id fty F) with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmts) /\
  stmts_exprs_ok bc stmts /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts stmts) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmts stmts) ==>
  !k es s. k <= LENGTH vs /\ Inv k es s /\
    gas_admissible (eval_for fp.jc_cx tyv id stmts (MAP Value (DROP k vs)))
      (stmt_res_ok lctx) es ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_for fp.jc_cx tyv id stmts (MAP Value (DROP k vs))) (es,s)
      (\res ee t. res = INL () /\ Done ee t)
      (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] intcall_array_gen_iterations)) >>
  impl_tac
  >- (conj_tac >- suspend "round" >>
      fs[ALL_DISTINCT] >> rpt conj_tac >> metis_tac[]) >>
  simp[]
QED
Resume intcall_array_gen_loop[round]:
  rpt strip_tac >>
  `!next.
     array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved arrbase
       p dst sz aa bod sc k es next /\
     intcall_joint_res fp ce env es sc next ==>
     ?s2. gas_marked_path F fp.jc_ctx fp.jc_func next 0 (OK s2) /\
       intcall_joint_res fp bc (extend_local env id fty F)
         (es with scopes :=
           (FEMPTY |+ (id, <|assignable := F; type := tyv;
                             value := EL k vs; popped := []|>)) :: es.scopes)
         sb0 s2 /\
       s2.vs_current_bb = sb0.cs_current_bb /\
       s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
       (!x. not_fresh_at sc x \/ x = idx \/ x = p \/ lvo = Var x \/
            saved = Var x ==> lookup_var x s2 = lookup_var x next) /\
       (!aid b. FLOOKUP next.vs_allocas aid = SOME b ==>
                FLOOKUP s2.vs_allocas aid = SOME b) /\
       next.vs_alloca_next <= s2.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_assum `!k es next. _ /\ array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ bod _ _ _ _ /\ _ ==> _`
       (qspecl_then [`k`, `es`, `next`] mp_tac) >> simp[]) >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] intcall_array_gen_round)) >>
  impl_tac
  >- (fs[ALL_DISTINCT] >> conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      qpat_x_assum `!k es gs res ee. _ ==> P _`
        (qspecl_then [`k`, `es`, `gs`, `res`, `ee`] mp_tac) >>
      fs[array_loop_inv_def]) >>
  simp[]
QED
Finalise intcall_array_gen_loop
