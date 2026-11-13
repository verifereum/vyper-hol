(* Interpreter congruence: only self-code slices observe transaction code. *)
Theory selfCodeFreeInterpreter
Ancestors
  selfCodeFreeInvariant selfCodeFreeStructural selfCodeFreeCalls
  selfCodeFreeBuiltins selfCodeFreeInternal selfCodeFreeContext selfCodeFreeSyntax
  vyperInterpreter vyperContext vyperState
  supportedStmtTraverse supportedExprTraverse e2eProducers exprLowering
Libs monadsyntax

val _ = Parse.hide "body";
val _ = monadsyntax.enable_monad "vyper_evaluation";

Theorem evaluate_self_code_free:
  (!cx s. !c.
    self_code_free_context cx /\
    ~supported_stmt_expr_exists is_self_code s ==>
    eval_stmt (cx with txn := (cx.txn with code := c)) s = eval_stmt cx s) /\
  (!cx ss. !c.
    self_code_free_context cx /\
    ~supported_stmts_expr_exists is_self_code ss ==>
    eval_stmts (cx with txn := (cx.txn with code := c)) ss = eval_stmts cx ss) /\
  (!cx it. !c.
    self_code_free_context cx /\
    ~supported_iterator_exists is_self_code it ==>
    eval_iterator (cx with txn := (cx.txn with code := c)) it = eval_iterator cx it) /\
  (!cx tyv nm body vs. !c.
    self_code_free_context cx /\
    ~supported_stmts_expr_exists is_self_code body ==>
    eval_for (cx with txn := (cx.txn with code := c)) tyv nm body vs = eval_for cx tyv nm body vs) /\
  (!cx e. !c.
    self_code_free_context cx /\
    ~supported_expr_exists is_self_code e ==>
    eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e) /\
  (!cx es. !c.
    self_code_free_context cx /\
    ~supported_exprs_exists is_self_code es ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) /\
  (!cx bt. !c.
    self_code_free_context cx /\
    ~supported_target_exists is_self_code bt ==>
    eval_base_place (cx with txn := (cx.txn with code := c)) bt = eval_base_place cx bt) /\
  (!cx bt. !c.
    self_code_free_context cx /\
    ~supported_target_exists is_self_code bt ==>
    eval_target_place (cx with txn := (cx.txn with code := c)) bt = eval_target_place cx bt) /\
  (!cx g v. !c.
    self_code_free_context cx /\
    ~supported_assignment_exists is_self_code g ==>
    assign_tuple_targets (cx with txn := (cx.txn with code := c)) g v = assign_tuple_targets cx g v) /\
  (!cx gs vs. !c.
    self_code_free_context cx /\
    ~supported_assignments_exists is_self_code gs ==>
    assign_tuple_target_list (cx with txn := (cx.txn with code := c)) gs vs = assign_tuple_target_list cx gs vs) /\
  (!cx es. !c.
    self_code_free_context cx /\
    ~supported_exprs_exists is_self_code es ==>
    eval_expr_results (cx with txn := (cx.txn with code := c)) es = eval_expr_results cx es)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac >>
  gvs[supported_stmt_expr_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_assignment_exists_def, supported_expr_exists_def] >>
  TRY (once_rewrite_tac[evaluate_def] >> simp[] >> NO_TAC)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (Raise (RaiseCustomError _)) = _ (* g *)`], irule self_code_free_raise_custom)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (Assert _ (AssertReason _)) = _ (* g *)`], irule self_code_free_assert_reason)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (Assert _ (AssertCustomError _)) = _ (* g *)`], irule self_code_free_assert_custom)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (Append _ _) = _ (* g *)`], irule self_code_free_append)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (Assign (BaseTarget _) _) = _ (* g *)`], irule self_code_free_assign)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (Assign (TupleTarget _) _) = _ (* g *)`], irule self_code_free_assign_tuple)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (AugAssign _ _ _ _) = _ (* g *)`], irule self_code_free_augassign)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (AnnAssign _ _ _) = _ (* g *)`], irule self_code_free_annassign)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (For _ _ _ _ _) = _ (* g *)`], irule self_code_free_for_stmt)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmt _ (If _ _ _) = _ (* g *)`], irule self_code_free_if_stmt)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_stmts _ (_::_) = _ (* g *)`], irule self_code_free_stmts_cons)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_iterator _ (Range _ _) = _ (* g *)`], irule self_code_free_iterator_range)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_for _ _ _ _ (_::_) = _ (* g *)`], irule self_code_free_for_cons)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr_results _ (_::_) = _ (* g *)`], irule self_code_free_expr_results_cons)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_exprs _ (_::_) = _ (* g *)`], irule self_code_free_exprs_cons)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`assign_tuple_target_list _ (_::_) (_::_) = _ (* g *)`], irule self_code_free_targets_cons)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`assign_tuple_targets _ (TupleTarget _) _ = _ (* g *)`], irule self_code_free_tuple_target)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_base_place _ (SubscriptTarget _ _) = _ (* g *)`], irule self_code_free_base_subscript)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (IfExp _ _ _ _) = _ (* g *)`], irule self_code_free_if_expr)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Subscript _ _ _) = _ (* g *)`], irule self_code_free_subscript)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (StructLit _ _ _) = _ (* g *)`], irule self_code_free_struct)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (TypeBuiltin _ _ _ _) = _ (* g *)`], irule self_code_free_type_builtin)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Builtin _ _ _) = _ (* g *)`], irule self_code_free_builtin)
  >~ [`eval_expr _ (Call _ (IntCall _) _ _) = _ (* g *)`] >- suspend "intcall"
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (Send _) _ _) = _ (* g *)`], irule self_code_free_send)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (RawCallTarget _) _ _) = _ (* g *)`], irule self_code_free_raw_call)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (RawCallCalldataTarget _) _ _) = _ (* g *)`], irule self_code_free_raw_call_calldata)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ RawLog _ _) = _ (* g *)`], irule self_code_free_raw_log)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ RawRevert _ _) = _ (* g *)`], irule self_code_free_raw_revert)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ SelfDestructTarget _ _) = _ (* g *)`], irule self_code_free_selfdestruct)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) = _ (* g *)`], irule self_code_free_ext_call)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (CreateTarget (CreateFromBlueprint _) _ _ _) _ _) = _ (* g *)`], irule self_code_free_create_blueprint)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (CreateTarget RawCreate _ _ _) _ _) = _ (* g *)`], irule self_code_free_raw_create)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (CreateTarget CreateMinimalProxy _ _ _) _ _) = _ (* g *)`], irule self_code_free_create_simple)
  >>> (fn (pats,tac) => SELECT_LT_THEN (Q.RENAME_TAC pats) tac) ([`eval_expr _ (Call _ (CreateTarget CreateCopyOf _ _ _) _ _) = _ (* g *)`], irule self_code_free_create_simple) >>
  pure_rewrite_tac[supported_exprs_exists_every, listTheory.EXISTS_NOT_EVERY, combinTheory.o_DEF] >>
  simp[] >> rpt strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE
    [supported_exprs_exists_every, listTheory.EXISTS_NOT_EVERY, combinTheory.o_DEF,
     NOT_CLAUSES]) >> simp[] >>
  suspend "continuations"
QED

Resume evaluate_self_code_free[continuations]:
  markerLib.RESUME_TAC
  >- (first_assum (drule_all_then (qspec_then `c` irule)) >> simp[]) >>
  suspend "more"
QED

Resume evaluate_self_code_free[more]:
  markerLib.RESUME_TAC
  >>~- ([`eval_stmts _ _ = _ (* g *)`], first_assum (drule_all_then (qspec_then `c` irule)) >> simp[]) >>
  suspend "rest1"
QED

Resume evaluate_self_code_free[rest1]:
  markerLib.RESUME_TAC
  >- (first_assum (drule_all_then (qspec_then `c` irule)) >> simp[]) >>
  suspend "rest2"
QED

Resume evaluate_self_code_free[intcall]:
  markerLib.RESUME_TAC >> irule self_code_free_int_call >> rpt conj_tac
  >- suspend "intbody"
  >- suspend "intdefaults" >>
  rpt strip_tac >>
  qpat_x_assum `!s1 t1 s2 ts t2 s3 tup t3 s4 t4. _` mp_tac >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def, raise_def]

QED

Resume evaluate_self_code_free[intdefaults]:
  rpt strip_tac >>
  qpat_x_assum `!s1 t1 s2 ts t2 s3 tup t3 s4 t4 s5 vs t5 s6 prev t6 s7 t7. _` mp_tac >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def, raise_def,
       get_scopes_def, set_scopes_def] >>
  disch_then (drule_then (qspec_then `c` mp_tac)) >>
  impl_tac >- (conj_tac
    >- (qpat_assum `self_code_free_context cx` mp_tac >>
        pure_rewrite_tac[self_code_free_context_def, get_module_code_def] >> simp[]) >>
    irule supported_exprs_exclusion_DROP >>
    drule_all self_code_free_context_callable >> simp[]) >>
  simp[]
QED

Resume evaluate_self_code_free[intbody]:
  rpt strip_tac >>
  qpat_x_assum `!s1 t1 s2 ts t2 s3 tup t3 s4 t4 s5 vs t5 s6 prev t6 s7 dvs t7 s8 env t8 s9 rtv t9 s10 t10 s11 cx1 t11. _` mp_tac >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def, raise_def,
       get_scopes_def, push_function_def] >>
  disch_then (drule_then mp_tac) >>
  simp[return_def] >>
  disch_then (qspec_then `u with scopes := prev` mp_tac) >> simp[] >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [arithmeticTheory.SUB_SUB]) >>
  disch_then (drule_at_then Any mp_tac) >> simp[return_def] >>
  `LENGTH dflts - (LENGTH args - LENGTH es) =
   LENGTH dflts + LENGTH es - LENGTH args` by decide_tac >>
  fs[] >>
  disch_then (drule_at_then Any mp_tac) >> simp[] >>
  simp[return_def] >> disch_then (qspec_then `c` irule) >>
  conj_tac
  >- (qpat_assum `self_code_free_context cx` mp_tac >>
      pure_rewrite_tac[self_code_free_context_def, get_module_code_def] >> simp[]) >>
  drule_all self_code_free_context_callable >> simp[]
QED

Resume evaluate_self_code_free[rest2]:
  markerLib.RESUME_TAC
  >- (qpat_x_assum `!s pv t u v w. _` mp_tac >>
      disch_then (drule_at_then Any mp_tac) >>
      disch_then (drule_at_then Any (qspec_then `c` irule))) >>
  suspend "rest3"
QED

Resume evaluate_self_code_free[rest3]:
  markerLib.RESUME_TAC
  >- metis_tac[] >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  suspend "rest4"
QED

Resume evaluate_self_code_free[rest4]:
  markerLib.RESUME_TAC
  >- (`~supported_expr_exists is_self_code (Builtin ty bt es)` by
        (pure_rewrite_tac[supported_expr_exists_def, supported_exprs_exists_every,
          listTheory.EXISTS_NOT_EVERY, combinTheory.o_DEF, NOT_CLAUSES] >> simp[]) >>
      drule_all self_code_free_slice_source >>
      simp[supported_exprs_exists_every] >> strip_tac >> metis_tac[]) >>
  suspend "rest5"
QED

Resume evaluate_self_code_free[rest5]:
  markerLib.RESUME_TAC
  >- (qpat_x_assum `!s target t. _` (drule_then (qspec_then `c` irule)) >>
      irule rich_listTheory.EVERY_TAKE >> irule rich_listTheory.EVERY_DROP >> simp[]) >>
  suspend "rest6"
QED

Resume evaluate_self_code_free[rest6]:
  markerLib.RESUME_TAC
  >- metis_tac[] >- metis_tac[] >- metis_tac[]
  >- (qpat_x_assum `!s target t u vs w. _` mp_tac >>
      disch_then (drule_at_then Any mp_tac) >>
      disch_then (drule_at_then Any (qspec_then `c` irule)) >>
      irule rich_listTheory.EVERY_DROP >> simp[])
  >- metis_tac[]
  >- (qpat_x_assum `supported_expr_exists _ _` mp_tac >>
      pure_rewrite_tac[supported_expr_exists_def, supported_exprs_exists_every,
        listTheory.EXISTS_NOT_EVERY, combinTheory.o_DEF, NOT_CLAUSES] >> simp[]) >>
  suspend "rest7"
QED

Resume evaluate_self_code_free[rest7]:
  markerLib.RESUME_TAC
  >- metis_tac[] >- metis_tac[] >- metis_tac[]
  >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  suspend "rest8"
QED

Resume evaluate_self_code_free[rest8]:
  markerLib.RESUME_TAC
  >- (qpat_x_assum `!s t. _ /\ bt = Len ==> _` (drule_then (qspec_then `c` irule)) >>
      qpat_x_assum `type_check _ _ _ = _` mp_tac >>
      Cases_on `es` >>
      gvs[type_check_def, assert_def, return_def, raise_def, builtin_args_length_ok_def]) >>
  suspend "rest9"
QED

Resume evaluate_self_code_free[rest9]:
  markerLib.RESUME_TAC
  >- metis_tac[] >- metis_tac[] >- metis_tac[]
  >- (first_assum (drule_then (qspec_then `c` irule)))
  >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  suspend "rest10"
QED

Resume evaluate_self_code_free[rest10]:
  markerLib.RESUME_TAC
  >- (qpat_x_assum `!s t ct addr. _` mp_tac >>
      disch_then (drule_then mp_tac) >> simp[] >>
      disch_then (qspec_then `c` irule) >> Cases_on `es` >> gvs[])
  >- metis_tac[]
  >- (qpat_x_assum `!c. EVERY _ (TAKE 1 es) ==> _` (qspec_then `c` irule) >>
      irule rich_listTheory.EVERY_TAKE >> simp[]) >>
  Cases_on `kind` >> gvs[] >> suspend "create"
QED

Resume evaluate_self_code_free[create]:
  markerLib.RESUME_TAC
  >~ [`eval_expr _ (Call _ (CreateTarget (CreateFromBlueprint _) _ _ _) _ _) = _ (* g *)`]
  >- (irule self_code_free_create_blueprint >> rpt strip_tac >>
      pure_rewrite_tac[supported_exprs_exists_every, listTheory.EXISTS_NOT_EVERY,
        combinTheory.o_DEF, NOT_CLAUSES] >>
      metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP])
  >~ [`eval_expr _ (Call _ (CreateTarget RawCreate _ _ _) _ _) = _ (* g *)`]
  >- (irule self_code_free_raw_create >> rpt strip_tac >>
      `LENGTH (DROP 2 es) - (if has_salt then 1 else 0) =
       LENGTH es - ((if has_salt then 1 else 0) + 2)` by
        (rewrite_tac[listTheory.LENGTH_DROP] >> decide_tac) >>
      qpat_x_assum `LENGTH (DROP 2 es) - _ = _`
        (fn th => rule_assum_tac (PURE_REWRITE_RULE[th]) >> pure_rewrite_tac[th]) >>
      pure_rewrite_tac[supported_exprs_exists_every, listTheory.EXISTS_NOT_EVERY,
        combinTheory.o_DEF, NOT_CLAUSES] >>
      all_tac
      >- (qpat_x_assum `!s prefix t ss results tt sss args ttt. _`
            (drule_at_then Any mp_tac) >>
          disch_then (drule_at_then Any mp_tac) >>
          disch_then (drule_at_then Any (qspec_then `c` irule)) >>
          irule rich_listTheory.EVERY_DROP >> irule rich_listTheory.EVERY_DROP >> simp[])
      >- (first_assum (drule_then (qspec_then `c` irule)) >>
          irule rich_listTheory.EVERY_TAKE >> irule rich_listTheory.EVERY_DROP >> simp[]) >>
      first_assum (qspec_then `c` irule) >>
      irule rich_listTheory.EVERY_TAKE >> simp[]) >>
  irule self_code_free_create_simple >> simp[]
QED

Finalise evaluate_self_code_free

Theorem eval_expr_self_code_free:
  !cx e c. self_code_free_context cx /\
    ~supported_expr_exists is_self_code e ==>
    eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e
Proof
  metis_tac[evaluate_self_code_free]
QED

Theorem eval_exprs_self_code_free:
  !cx es c. self_code_free_context cx /\
    ~supported_exprs_exists is_self_code es ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es
Proof
  metis_tac[evaluate_self_code_free]
QED

Theorem eval_stmt_self_code_free:
  !cx s c. self_code_free_context cx /\
    ~supported_stmt_expr_exists is_self_code s ==>
    eval_stmt (cx with txn := (cx.txn with code := c)) s = eval_stmt cx s
Proof
  metis_tac[evaluate_self_code_free]
QED

Theorem eval_stmts_self_code_free:
  !cx ss c. self_code_free_context cx /\
    ~supported_stmts_expr_exists is_self_code ss ==>
    eval_stmts (cx with txn := (cx.txn with code := c)) ss = eval_stmts cx ss
Proof
  metis_tac[evaluate_self_code_free]
QED
