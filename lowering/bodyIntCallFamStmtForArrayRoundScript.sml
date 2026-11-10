(* Resource-preserving routing and iteration for array loops. *)
Theory bodyIntCallFamStmtForArrayRound
Ancestors
  bodyIntCallFamStmtForArrayResources bodyIntCallFamStmtForRange
  bodyIntCallJointContract bodyIntCallJointStmtJump stmtSimForArrayLoop
  stmtSimProps stmtSimDefs compileEnv fragGasMode fragGasPathMem
  venomState venomExecSemantics finite_map loweringPosts
  bodyIntCallFamStmtForRound bodySimDeclCases vyperEvalPreservesScopes
  vyperInterpreter vyperState exprSimWordArgs bodyIntCallFamStmtForTransport

Theorem intcall_array_body_route:
  array_for_code fp.jc_func ce bc ty stmts id et tv n stride saved
    p sz aa idx dv ov ep nv cond exit bod incr j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
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
          irule emit_jump_zero_path_mem >>
          fs[array_for_code_def] >> metis_tac[]) >>
      simp[jump_to_def]) >>
  qexists_tac `t` >> gvs[stmt_lands_def] >>
  irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]
QED

Theorem intcall_array_body_finish_resources:
  array_for_code fp.jc_func ce bc ty stmts id et tv n stride saved
    p sz aa idx dv ov ep nv cond exit bod incr j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb1) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sb1 t /\
  (!op. fp.jc_reserved op ==> op <> Var idx /\ op <> Var nv) /\
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
  strip_tac >> drule_all intcall_array_body_route >> strip_tac >>
  `intcall_joint_res fp ce env es sb1 u /\
   lookup_var idx u = SOME c /\ u.vs_allocas = t.vs_allocas /\
   u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_memory = t.vs_memory /\ u.vs_labels = t.vs_labels /\
   (!x. lookup_var x u = lookup_var x t)` by
    (Cases_on `res = INL ()` >>
     gvs[jump_to_def, lookup_var_def]) >>
  Cases_on `res = INR BreakException`
  >- (qexists_tac `u` >> simp[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func u 0
    (OK (jump_to cond (update_var idx (c + 1w) (update_var nv (c + 1w) u)))) /\
   intcall_joint_res fp ce env es sb1
    (jump_to cond (update_var idx (c + 1w) (update_var nv (c + 1w) u)))` by
    (irule intcall_for_increment_resources >> fs[array_for_code_def] >> metis_tac[]) >>
  qexists_tac `jump_to cond (update_var idx (c + 1w) (update_var nv (c + 1w) u))` >>
  conj_tac
  >- (qpat_assum `gas_marked_path _ _ _ t _ _`
        (mp_then Any mp_tac gas_marked_path_then) >>
      disch_then drule >> simp[]) >>
  fs[array_for_code_def, listTheory.ALL_DISTINCT] >>
  Cases_on `res = INL ()` >>
  fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* The source snapshot is recovered after every body outcome, including
   Continue, from the typed iterator-unmodified projection theorem. *)
Theorem intcall_array_round_at_body:
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
        intcall_joint_res fp ce env ee sa u /\
        lookup_scopes name ee.scopes = SOME snapshot /\
        (!x z. not_fresh_at sa x /\ lookup_var x cc = SOME z ==>
               lookup_var x u = SOME z) /\
        (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
                 FLOOKUP u.vs_allocas aid = SOME b) /\
        cc.vs_alloca_next <= u.vs_alloca_next /\
        (broke ==> u.vs_current_bb = exit) /\
        (~broke ==> u.vs_current_bb = cond /\ lookup_var idx u = SOME (c + 1w)))
  in
  array_for_code fp.jc_func ce bc ty stmts id et tv n stride saved
    p sz aa idx dv ov ep nv cond exit bod incr j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa cc /\
  cenv_top_ext ce bc entry.scopes /\
  local_ptrs_reserved ce sb1 /\
  (!op. fp.jc_reserved op ==> op <> Var idx /\ op <> Var nv) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ ~s2.vs_halted /\ lookup_var idx s2 = SOME c /\
  (!x z. not_fresh_at sa x /\ lookup_var x cc = SOME z ==>
         lookup_var x s2 = SOME z) /\
  (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==>
           FLOOKUP s2.vs_allocas aid = SOME b) /\
  cc.vs_alloca_next <= s2.vs_alloca_next /\
  id NOTIN FDOM env.var_types /\ lookup_scopes id es.scopes = NONE /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\ value_has_type tyv v /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b /\
  call_evaluation_safe fp.jc_cx (int_calls_stmts stmts) /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmts fp.jc_tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\ name <> id /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  lookup_scopes name es.scopes = SOME snapshot /\
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
Resume intcall_array_round_at_body[exit]:
  rpt gen_tac >> strip_tac >>
  `ee.scopes <> []` by
    (drule eval_stmts_preserves_scopes_len >>
     simp[] >> strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  drule intcall_stmt_exit_no_loop_control >> strip_tac >> gvs[]
QED
Resume intcall_array_round_at_body[normal]:
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
  `intcall_joint_res fp ce env (es with gas_obs := gs) sa cc` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_gas_obs] >>
     metis_tac[]) >>
  `intcall_joint_res fp ce env (ee with scopes := TL ee.scopes) sb1 t` by
    (irule (cj 2 intcall_for_body_pop_resources) >>
     simp[] >> reverse conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `lookup_scopes name (TL ee.scopes) = SOME snapshot` by
    (Cases_on `ee.scopes` >- gvs[] >>
     irule array_body_direct_snapshot >>
     qrefinel [`_`, `_`, `_`, `_`, `_`, `es with gas_obs := gs`] >>
     simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `lookup_var idx t = SOME c` by metis_tac[] >>
  `(res = INL () ==> ~block_is_terminated sb1)` by metis_tac[] >>
  drule_all intcall_array_body_finish_resources >> strip_tac >>
  `intcall_joint_res fp ce env (ee with scopes := TL ee.scopes) sa u` by
    (`local_ptrs_reserved ce sa /\
      (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x)` by
       fs[intcall_joint_res_def, intcall_expr_res_def] >>
     irule intcall_joint_res_reentry >> simp[] >>
     qexists_tac `sb1` >> simp[]) >>
  simp[] >> qexists_tac `u` >> simp[] >> metis_tac[]
QED
Finalise intcall_array_round_at_body
