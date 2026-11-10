(* Source-side boundaries for the checked range round. *)
Theory forPtrRangeSource
Ancestors forPtrRangePrepare forPtrRounds stmtSimForParts gasContext
  gasSummaryComposePtr
  vyperInterpreter vyperState loweringPosts stmtSimDefs rich_list
Libs monadsyntax

Theorem for_body_admissible:
  gas_admissible (eval_for cx tyv id stmts (v::vs))
    (stmt_res_ok lctx) es /\ lookup_scopes id es.scopes = NONE ==>
  gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl))
    (es with <| scopes :=
      (FEMPTY |+ (id, <| assignable := F; type := tyv;
                         value := v; popped := [] |>)) :: es.scopes;
                gas_obs := [] |>)
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts _ = (res, ee)` >>
  Cases_on `eval_for cx tyv id stmts (v::vs) (es with gas_obs := gs)` >>
  rename1 `_ = (lr, le)` >>
  `stmt_res_ok lctx lr` by
    (gvs[gas_admissible_def] >> metis_tac[]) >>
  drule eval_for_cons_cases >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[stmt_res_ok_def]
QED

Theorem for_range_body_admissible:
  k < LENGTH vs /\
  gas_admissible (eval_for cx tyv id stmts (DROP k vs))
    (stmt_res_ok lctx) es /\ lookup_scopes id es.scopes = NONE ==>
  gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl))
    (es with <| scopes :=
      (FEMPTY |+ (id, <| assignable := F; type := tyv;
                         value := EL k vs; popped := [] |>)) :: es.scopes;
                gas_obs := [] |>)
Proof
  strip_tac >> irule for_body_admissible >>
  drule rich_listTheory.DROP_CONS_EL >> disch_tac >>
  conj_tac >- simp[] >>
  qexistsl_tac [`lctx`, `DROP (SUC k) vs`] >> gvs[]
QED

Theorem for_push_scope_marked_ptr:
  gas_path_ptr D 0 ctx func PG G tn s 0 gf tf (OK t) ==>
  gas_marked_exec_ptr D (ctx,func) PG (push_scope_with_var id tyv v)
    (es,s,G,tn) [] (INL ())
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>))::es.scopes) gf tf (OK t)
Proof
  simp[gas_marked_exec_ptr_def, push_scope_with_var_def, return_def,
       evaluation_state_component_equality, combinTheory.o_DEF]
QED

Theorem for_prepared_ret_pc:
  ret_pc_ok cenv st s /\ bc.ce_return_pc = cenv.ce_return_pc /\
  st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x. x <> dv ==> lookup_var x s2 = lookup_var x s) ==>
  ret_pc_ok bc sb0 s2
Proof
  strip_tac >> irule stmtSimPropsTheory.ret_pc_ok_frame >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem for_body_outer_preserves:
  (!ei k obs r ee sc rest.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < N /\
    eval_stmts cx stmts
      (ei with <| scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
          value := IntV (n1 + &k); popped := []|>)) :: ei.scopes;
        gas_obs := obs |>) = (r,ee) /\
    (r = INL () \/ r = INR ContinueException) /\
    ee.scopes = sc :: rest ==> P (ee with scopes := rest)) /\
  P es /\ lookup_scopes id es.scopes = NONE /\ k < N /\
  eval_stmts cx stmts
    (es with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
        value := IntV (n1 + &k); popped := []|>)) :: es.scopes;
      gas_obs := obs |>) = (r,ee) /\
  (r = INL () \/ r = INR ContinueException) /\ ee.scopes = sc :: rest ==>
  P (ee with scopes := rest) /\ lookup_scopes id rest = NONE
Proof
  strip_tac >> conj_tac >- metis_tac[] >>
  drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom >>
  simp[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def] >> strip_tac >>
  metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom]
QED

(* Static callback obligations are transported from the original loop entry,
   not assumed at the fresh body compiler state.  Dynamic state/ghost facts
   are supplied separately by for_range_body_prepare_ptr. *)
Theorem for_range_callback_entry_ptr:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  ~cenv.ce_is_ctor /\ ret_pc_ok cenv st s /\
  st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==>
    not_fresh_at st x) /\
  (!x. x <> dv ==> lookup_var x s2 = lookup_var x s) /\
  s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\ ~s2.vs_halted ==>
  (?bc'. stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1)) /\
  ~bc.ce_is_ctor /\ ret_pc_ok bc sb0 s2 /\
  (!x q. bc.ce_return_buf = SOME (PtrVar (Var x) q) ==>
    not_fresh_at sb0 x) /\
  ~s2.vs_halted /\ s2.vs_current_bb = sb0.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> x <> dv)
Proof
  strip_tac >>
  `bc.ce_return_pc = cenv.ce_return_pc /\
   bc.ce_return_buf = cenv.ce_return_buf /\ bc.ce_is_ctor = cenv.ce_is_ctor` by
    (fs[stmtSimForLoopTheory.for_code_def,
        compileEnvTheory.compile_env_component_equality]) >>
  `ret_pc_ok bc sb0 s2` by (irule for_prepared_ret_pc >> metis_tac[]) >>
  conj_tac
  >- (irule stmtSimForArrayLoopTheory.array_body_compiler_env >>
      fs[stmtSimForLoopTheory.for_code_def]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at st x` by metis_tac[] >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  fs[stmtSimForLoopTheory.for_code_def] >> metis_tac[]
QED
