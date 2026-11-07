Theory bodyPtrPopStatementBoundary
Ancestors bodyPtrPopMutualBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopStatementSimpleBoundary bodyPtrPopStatementReasonBoundary
  bodyPtrPopStatementExitBoundary bodyPtrPopStatementFlowBoundary
  bodyPtrPopStatementLoopBoundary bodyPtrPopStatementControl
  supportedStmts stmtLowering vyperAST list compileEnv

(* This rephrases the generated compiler induction without its incidental
   let-bound variables. Environments for loop bodies and declaration tails
   remain universally quantified. It asserts no producer preservation. *)
Theorem pop_statement_boundary_induction:
  !P Q.
  (!(ce:compile_env) lc (ty:type) s.
    (case s of
       If c yes no => Q ce lc ty yes /\ Q ce lc ty no
     | For id fty it n loop_body => !ce' exit incr. Q ce' (InLoop exit incr) ty loop_body
     | _ => T) ==> P ce lc ty s) /\
  (!ce lc ty. Q ce lc ty []) /\
  (!ce lc ty s ss.
    (!cs ce'. ~block_is_terminated cs ==> P ce' lc ty s) /\
    (!cs ce'. ~block_is_terminated cs ==> Q ce' lc ty ss) ==> Q ce lc ty (s::ss)) ==>
  (!ce lc ty s. P ce lc ty s) /\ (!ce lc ty ss. Q ce lc ty ss)
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac compile_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  FIRST_PROVE [first_assum MATCH_ACCEPT_TAC,
    (qpat_x_assum `!ce lc ty s ss. _` irule >> metis_tac[]),
    (qpat_x_assum `!ce lc ty s. _` irule >> simp[] >> metis_tac[])]
QED

Theorem pop_stmts_cons_boundary:
  (!cs ce' s r t. ~block_is_terminated cs /\ pop_comp_boundary s /\
    compile_stmt ce' lc ty st s = (r,t) ==> pop_comp_boundary t) /\
  (!cs ce' s r t. ~block_is_terminated cs /\ pop_comp_boundary s /\
    compile_stmts ce' lc ty ss s = (r,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ compile_stmts ce lc ty (st::ss) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[Once compile_stmt_def, comp_ignore_bind_def,
       Once comp_bind_def, comp_get_def] >> rpt strip_tac >>
  Cases_on `block_is_terminated sa` >> gvs[comp_return_def] >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE [drule_all pop_declare_stmt_local_boundary >> simp[],
    (qpat_x_assum `!cs ce' s t. _ /\ _ /\ compile_stmt _ _ _ _ _ = _ ==> _`
       (qspec_then `sa` mp_tac) >> simp[] >> disch_then drule_all >> simp[]),
    (qpat_x_assum `!cs ce' s t. _ /\ _ /\ compile_stmts _ _ _ _ _ = _ ==> _`
       (qspec_then `sa` mp_tac) >> simp[] >> disch_then drule_all >> simp[])]
QED

Theorem pop_stmt_constructor_boundary:
  (case st of
     If c yes no =>
       (!s r t. pop_comp_boundary s /\ compile_stmts ce lc ty yes s = (r,t) ==> pop_comp_boundary t) /\
       (!s r t. pop_comp_boundary s /\ compile_stmts ce lc ty no s = (r,t) ==> pop_comp_boundary t)
   | For id fty it n loop_body =>
       !ce' exit incr s r t. pop_comp_boundary s /\
         compile_stmts ce' (InLoop exit incr) ty loop_body s = (r,t) ==> pop_comp_boundary t
   | _ => T) /\
  supported_stmt tops bindings st /\ pop_comp_boundary sa /\
  compile_stmt ce lc ty st sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Cases_on `st` >> simp[] >> rpt strip_tac >> FIRST_PROVE
    [drule_all pop_stmt_pass_boundary >> simp[],
     drule_all pop_stmt_break_boundary >> simp[],
     drule_all pop_stmt_continue_boundary >> simp[],
     drule_all pop_stmt_augassign_boundary >> simp[],
     (fs[supported_stmt_def] >> FIRST_PROVE
       [drule_all pop_stmt_expr_boundary >> simp[],
        drule_all pop_stmt_annassign_boundary >> simp[],
        drule_all pop_stmt_append_boundary >> simp[],
        drule_all pop_stmt_raise_boundary >> simp[],
        drule_all pop_stmt_assert_boundary >> simp[],
        drule_all pop_stmt_log_boundary >> simp[],
        (drule_at (Pat `compile_stmt _ _ _ _ _ = _`) pop_stmt_if_boundary >>
         disch_then irule >> simp[] >> rpt conj_tac >>
         FIRST_PROVE [first_assum MATCH_ACCEPT_TAC, metis_tac[]]),
        (Cases_on `a` >> gvs[] >> FIRST_PROVE
          [drule_all pop_stmt_base_assign_boundary >> simp[],
           drule_all pop_stmt_tuple_assign_boundary >> simp[]]),
        (Cases_on `o'` >> gvs[supported_stmt_def] >> FIRST_PROVE
          [drule_all pop_stmt_return_none_boundary >> simp[],
           drule_all pop_stmt_return_some_boundary >> simp[]]),
        (Cases_on `i` >> gvs[] >> FIRST_PROVE
          [(drule_at (Pat `compile_stmt _ _ _ _ _ = _`) pop_stmt_for_range_boundary >>
            disch_then irule >> simp[] >>
            (conj_tac >- first_assum MATCH_ACCEPT_TAC) >> qexists_tac `tops` >> simp[]),
           (drule_at (Pat `compile_stmt _ _ _ _ _ = _`) pop_stmt_for_array_boundary >>
            disch_then irule >> simp[] >>
            (conj_tac >- first_assum MATCH_ACCEPT_TAC) >> qexists_tac `tops` >> simp[])])])]
QED

Theorem pop_compile_statements_boundary:
  (!ce lc ty st tops bindings sa r sb.
    supported_stmt tops bindings st /\ pop_comp_boundary sa /\
    compile_stmt ce lc ty st sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!ce lc ty ss tops bindings sa r sb.
    supported_stmts tops bindings ss /\ pop_comp_boundary sa /\
    compile_stmts ce lc ty ss sa = (r,sb) ==> pop_comp_boundary sb)
Proof
  ho_match_mp_tac pop_statement_boundary_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      drule_at (Pat `compile_stmt _ _ _ _ _ = _`) pop_stmt_constructor_boundary >>
      disch_then irule >> simp[] >>
      (conj_tac >- (qexistsl [`bindings`, `tops`] >> simp[])) >>
      Cases_on `st` >> gvs[supported_stmt_def] >> rpt strip_tac >>
      first_x_assum drule_all >> simp[])
  >- (simp[compile_stmt_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def] >>
  drule_at (Pat `compile_stmts _ _ _ (_::_) _ = _`) pop_stmts_cons_boundary >>
  disch_then irule >> simp[] >> conj_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule_all >> simp[]
QED
