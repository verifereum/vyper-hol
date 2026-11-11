(* Finite counted iteration of resource-preserving Array rounds. *)
Theory bodyIntCallFamStmtForArrayIterations
Ancestors
  bodyIntCallFamStmtForArrayRound bodyIntCallFamStmtForArrayResources
  bodyIntCallJointContract stmtSimForArrayLoop stmtSimForRounds
  exprSimMemDefs exprSimWordArgs fragGasMode gasOutcome vyperInterpreter
  venomState venomExecSemantics venomInst finite_map list rich_list arithmetic

Theorem intcall_array_final:
  lookup_block cond fp.jc_func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst i EQ [Var idx; Lit (n2w n)] [dv];
       mk_inst j JNZ [Var dv; Label exit; Label bod] []]|> /\
  s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var idx s = SOME (n2w n) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s /\
  not_local_ptr ce es.scopes dv /\
  (!op. fp.jc_reserved op ==> op <> Var dv) /\
  (!x. not_fresh_at sc x ==> x <> dv) ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    intcall_joint_res fp ce env es sc t /\
    (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==>
           lookup_var x t = SOME z) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all intcall_array_condition_resources >>
  simp[LET_THM] >> strip_tac >>
  qexists_tac `jump_to exit (update_var dv (bool_to_word T) s)` >>
  simp[] >> metis_tac[]
QED

Theorem intcall_array_iterations:
  let K = (\s.
        (!x z. not_fresh_at sc x /\ lookup_var x origin = SOME z ==>
               lookup_var x s = SOME z) /\
        (!aid b. FLOOKUP origin.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        origin.vs_alloca_next <= s.vs_alloca_next);
      Inv = (\k es s.
        array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx saved
          arrbase p dst sz aa cond sc k es s /\
        intcall_joint_res fp ce env es sc s /\ K s);
      Done = (\es s. s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\
        ~s.vs_halted /\ intcall_joint_res fp ce env es sc s /\ K s);
      H = (\k s res ee u. ?broke. res = INL broke /\
        u.vs_inst_idx = 0 /\ ~u.vs_halted /\
        intcall_joint_res fp ce env ee sc u /\
        (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==>
               lookup_var x u = SOME z) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP u.vs_allocas aid = SOME b) /\
        s.vs_alloca_next <= u.vs_alloca_next /\
        (broke ==> u.vs_current_bb = exit) /\
        (~broke ==> array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id
          idx saved arrbase p dst sz aa cond sc (k+1) ee u))
  in
  intcall_frame_ok fp /\
  lookup_block cond fp.jc_func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst i EQ [Var idx; Lit (n2w (LENGTH vs))] [dv];
       mk_inst j JNZ [Var dv; Label exit; Label bod] []]|> /\
  (!es s. Inv (LENGTH vs) es s ==> not_local_ptr ce es.scopes dv) /\
  (!op. fp.jc_reserved op ==> op <> Var dv) /\
  (!x. not_fresh_at sc x ==> x <> dv) /\
  (!k es s. k < LENGTH vs /\ Inv k es s /\
    gas_admissible (eval_for fp.jc_cx tyv id stmts (DROP k vs)) ok es ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (ignore_bind (push_scope_with_var id tyv (EL k vs))
        (finally (try (ignore_bind (eval_stmts fp.jc_cx stmts) (return F))
                       handle_loop_exception) pop_scope))
      (es,s) (H k s)
      (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)) ==>
  !k es s. k <= LENGTH vs /\ Inv k es s /\
    gas_admissible (eval_for fp.jc_cx tyv id stmts (DROP k vs)) ok es ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_for fp.jc_cx tyv id stmts (DROP k vs)) (es,s)
      (\res ee t. res = INL () /\ Done ee t)
      (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)
Proof
  BasicProvers.LET_ELIM_TAC >>
  irule (eval_for_rounds |> SPEC_ALL |>
    Q.INST [`R` |-> `\ex ee r. intcall_stmt_exit fp (INR ex) ee r`] |>
    SRULE []) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`Inv`, `ok`] >> simp[] >>
  conj_tac >- suspend "final" >> suspend "round"
QED
Resume intcall_array_iterations[final]:
  rpt strip_tac >> rename1 `Inv (LENGTH vs) ee cc` >>
  `not_local_ptr ce ee.scopes dv` by metis_tac[] >>
  fs[Abbr `Inv`, array_loop_inv_def] >>
  drule_all (SRULE [] intcall_array_final) >> strip_tac >>
  qexists_tac `t` >> simp[Abbr `Done`] >>
  conj_tac
  >- (fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_gas_obs] >>
      metis_tac[]) >>
  fs[Abbr `K'`] >> metis_tac[]
QED
Resume intcall_array_iterations[round]:
  rpt strip_tac >> rename1 `Inv kk ee cc` >>
  irule gas_outcome_post_mono >>
  qexists_tac `H kk cc` >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  fs[Abbr `H`, Abbr `Inv`, Abbr `Done`, Abbr `K'`] >>
  rpt strip_tac >> qexists_tac `broke` >>
  simp[ADD1] >> metis_tac[LESS_EQ_TRANS]
QED
Finalise intcall_array_iterations
