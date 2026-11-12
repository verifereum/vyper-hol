(* Statement preservation assembled from expression and constructor boundaries. *)
Theory ctorCallFreeStmt
Ancestors
  ctorCallFreeStmtAssign ctorCallFreeStmtEffects ctorCallFreeStmtControl
  stmtLowering exprLowering supportedExprTraverse supportedStmtTraverse
  e2eDeployDefs loweringShapeDefs loweringShapeProps venomInst
  ctorCallFreeRules ctorCallFreeStmtStorage list pair context emitHelper


Theorem call_free_stmt_stmts_size[local]:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !n.
  (!s. 2 * stmt_size s + 2 <= n ==> !ce lc ty st.
    ~supported_stmt_expr_exists constructor_call_root s /\
    ~supported_stmt_expr_exists expr_shape_root s ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmt ce lc ty s st)))) /\
  (!ss. 2 * list_size stmt_size ss + 1 <= n ==> !ce lc ty st.
    ~supported_stmts_expr_exists constructor_call_root ss /\
    ~supported_stmts_expr_exists expr_shape_root ss ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce lc ty ss st))))
Proof
  strip_tac >> completeInduct_on `n` >> conj_tac
  >- suspend "stmt"
  >> suspend "stmts"
QED

Resume call_free_stmt_stmts_size[stmt]:
  gen_tac >> strip_tac >> Cases_on `s`
  >~ [`compile_stmt _ _ _ Pass`] >- simp[Once compile_stmt_def, every_state_insts_return]
  >~ [`compile_stmt _ _ _ Continue`] >- (rpt gen_tac >> Cases_on `lc` >>
    simp[Once compile_stmt_def, call_free_emit_inst, every_state_insts_ignore_bind, every_state_insts_return])
  >~ [`compile_stmt _ _ _ Break`] >- (rpt gen_tac >> Cases_on `lc` >>
    simp[Once compile_stmt_def, call_free_emit_inst, every_state_insts_ignore_bind, every_state_insts_return])
  >~ [`compile_stmt _ _ _ (AnnAssign _ _ _)`] >- (rpt strip_tac >> irule call_free_stmt_annassign >> simp[])
  >~ [`compile_stmt _ _ _ (Assign _ _)`] >- suspend "assign"
  >~ [`compile_stmt _ _ _ (AugAssign _ _ _ _)`] >- (rpt strip_tac >> irule call_free_stmt_augassign >> simp[])
  >~ [`compile_stmt _ _ _ (Append _ _)`] >- (rpt strip_tac >> irule call_free_stmt_append >> simp[])
  >~ [`compile_stmt _ _ _ (Assert _ _)`] >- (rpt strip_tac >> irule call_free_stmt_assert >> simp[])
  >~ [`compile_stmt _ _ _ (Raise _)`] >- (rpt strip_tac >> irule call_free_stmt_raise >> simp[])
  >~ [`compile_stmt _ _ _ (Return _)`] >- suspend "return"
  >~ [`compile_stmt _ _ _ (Log _ _)`] >- (rpt strip_tac >> irule call_free_stmt_log >> simp[])
  >~ [`compile_stmt _ _ _ (If _ _ _)`] >- suspend "if"
  >~ [`compile_stmt _ _ _ (For _ _ _ _ _)`] >- suspend "for"
  >> suspend "expr"
QED

Resume call_free_stmt_stmts_size[stmts]:
  Cases_on `ss` >- simp[Once compile_stmt_def, every_state_insts_return] >>
  rename1 `h::tl` >> simp[list_size_def] >> strip_tac >>
  qpat_x_assum `!m. _` (qspec_then `n-1` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  `2 * stmt_size h + 2 <= n-1` by decide_tac >>
  `2 * list_size stmt_size tl + 1 <= n-1` by decide_tac >>
  first_x_assum (drule_then assume_tac) >>
  first_x_assum (drule_then assume_tac) >>
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  qid_spec_tac `st` >> simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[every_state_insts_get] >> gen_tac >> IF_CASES_TAC
  >- simp[every_state_insts_return] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_declare_stmt_local] >> gen_tac >>
  ho_match_mp_tac every_state_insts_ignore_bind >> simp[]
QED

Resume call_free_stmt_stmts_size[expr]:
  rpt gen_tac >> simp[supported_stmt_expr_exists_def] >> strip_tac >>
  qid_spec_tac `st` >> simp[Once compile_stmt_def] >>
  ho_match_mp_tac every_state_insts_ignore_bind >> simp[every_state_insts_return]
QED

Resume call_free_stmt_stmts_size[assign]:
  rename1 `Assign target e` >> Cases_on `target`
  >- (rpt strip_tac >> irule call_free_stmt_assign_base >> simp[]) >>
  rpt strip_tac >> irule call_free_stmt_assign_tuple >> simp[]
QED

Resume call_free_stmt_stmts_size[return]:
  rename1 `Return eo` >> Cases_on `eo`
  >- simp[call_free_stmt_return_none] >>
  rpt strip_tac >> irule call_free_stmt_return_some >> simp[]
QED

Resume call_free_stmt_stmts_size[if]:
  rename1 `If cond b1 b2` >>
  `0 < n` by gvs[vyperASTTheory.stmt_size_def] >>
  qpat_x_assum `!m. _` (qspec_then `n-1` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  `2 * list_size stmt_size b1 + 1 <= n-1` by gvs[vyperASTTheory.stmt_size_def] >>
  `2 * list_size stmt_size b2 + 1 <= n-1` by gvs[vyperASTTheory.stmt_size_def] >>
  rpt strip_tac >>
  irule call_free_stmt_if >> simp[] >>
  gvs[supported_stmt_expr_exists_def] >> conj_tac >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume call_free_stmt_stmts_size[for]:
  qmatch_asmsub_rename_tac `stmt_size (For loop_ident loop_type loop_iterator loop_bound loop_body)` >>
  `0 < n` by gvs[vyperASTTheory.stmt_size_def] >>
  qpat_x_assum `!m. _` (qspec_then `n-1` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  `2 * list_size stmt_size loop_body + 1 <= n-1` by gvs[vyperASTTheory.stmt_size_def] >>
  Cases_on `loop_iterator`
  >- (rpt strip_tac >> irule call_free_stmt_for_array >> simp[] >>
    gvs[supported_stmt_expr_exists_def] >>
    rpt strip_tac >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> irule call_free_stmt_for_range >> simp[] >>
  gvs[supported_stmt_expr_exists_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Finalise call_free_stmt_stmts_size

Theorem compile_stmt_stmts_call_free_from_expr:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  (!ce lc ty s st.
    ~supported_stmt_expr_exists constructor_call_root s /\
    ~supported_stmt_expr_exists expr_shape_root s ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmt ce lc ty s st)))) /\
  (!ce lc ty ss st.
    ~supported_stmts_expr_exists constructor_call_root ss /\
    ~supported_stmts_expr_exists expr_shape_root ss ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce lc ty ss st))))
Proof
  strip_tac >> drule call_free_stmt_stmts_size >> strip_tac >> conj_tac
  >- (rpt gen_tac >> first_x_assum (qspec_then `2 * stmt_size s + 2` mp_tac) >>
    simp[] >> strip_tac >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> first_x_assum (qspec_then `2 * list_size stmt_size ss + 1` mp_tac) >>
  simp[] >> strip_tac >> first_x_assum irule >> simp[]
QED

Theorem compile_stmt_call_free_from_expr:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty s st.
    ~supported_stmt_expr_exists constructor_call_root s /\
    ~supported_stmt_expr_exists expr_shape_root s /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmt ce lc ty s st)))
Proof
  strip_tac >> drule compile_stmt_stmts_call_free_from_expr >> strip_tac >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem compile_stmts_call_free_from_expr:
  (!ce ty e st.
    ~supported_expr_exists constructor_call_root e /\
    ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !ce lc ty ss st.
    ~supported_stmts_expr_exists constructor_call_root ss /\
    ~supported_stmts_expr_exists expr_shape_root ss /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_stmts ce lc ty ss st)))
Proof
  strip_tac >> drule compile_stmt_stmts_call_free_from_expr >> strip_tac >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED
