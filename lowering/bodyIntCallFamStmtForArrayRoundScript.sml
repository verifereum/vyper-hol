(* Resource-preserving routing and iteration for array loops. *)
Theory bodyIntCallFamStmtForArrayRound
Ancestors
  bodyIntCallFamStmtForArrayResources bodyIntCallFamStmtForRange
  bodyIntCallJointContract bodyIntCallJointStmtJump stmtSimForArrayLoop
  stmtSimProps stmtSimDefs compileEnv fragGasMode fragGasPathMem
  venomState venomExecSemantics finite_map loweringPosts

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
