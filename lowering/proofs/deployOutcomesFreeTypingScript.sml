Theory deployOutcomesFreeTyping
Ancestors
  vyperTypeSystem supportedExprTraverse supportedStmtTraverse list option

Theorem outcomes_free_typed_subscript_children:
  (well_typed_expr env (Subscript ty b i) \/
   (?vt. type_place_expr env (Subscript ty b i) = SOME vt)) /\
  ~supported_expr_exists p (Subscript ty b i) ==>
  (well_typed_expr env b \/ (?vt. type_place_expr env b = SOME vt)) /\
  ~supported_expr_exists p b /\ well_typed_expr env i /\
  ~supported_expr_exists p i
Proof
  rw[well_typed_expr_def, supported_expr_exists_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem outcomes_free_typed_attribute_child:
  (well_typed_expr env (Attribute ty e id) \/
   (?vt. type_place_expr env (Attribute ty e id) = SOME vt)) /\
  ~supported_expr_exists p (Attribute ty e id) ==>
  well_typed_expr env e /\ ~supported_expr_exists p e
Proof
  simp[well_typed_expr_def, supported_expr_exists_def] >> metis_tac[]
QED

Theorem outcomes_free_typed_pop_target:
  (well_typed_expr env (Pop ty t) \/
   (?vt. type_place_expr env (Pop ty t) = SOME vt)) /\
  ~supported_expr_exists p (Pop ty t) ==>
  (?vt. type_place_target env t = SOME vt) /\
  ~supported_target_exists p t
Proof
  simp[well_typed_expr_def, supported_expr_exists_def] >> metis_tac[]
QED

Theorem outcomes_free_typed_subscript_target:
  type_place_target env (SubscriptTarget t i) = SOME vt /\
  ~supported_target_exists p (SubscriptTarget t i) ==>
  (?bt. type_place_target env t = SOME bt) /\
  ~supported_target_exists p t /\ well_typed_expr env i /\
  ~supported_expr_exists p i
Proof
  rw[well_typed_expr_def, supported_expr_exists_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem outcomes_free_typed_attribute_target:
  type_place_target env (AttributeTarget t id) = SOME vt /\
  ~supported_target_exists p (AttributeTarget t id) ==>
  (?bt. type_place_target env t = SOME bt) /\
  ~supported_target_exists p t
Proof
  rw[well_typed_expr_def, supported_expr_exists_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem outcomes_free_typed_exprs_every:
  well_typed_exprs env es <=> EVERY (well_typed_expr env) es
Proof
  Induct_on `es` >> simp[well_typed_expr_def]
QED

Theorem outcomes_free_typed_fields_every:
  well_typed_named_exprs env fields <=>
  EVERY (\kv. well_typed_expr env (SND kv)) fields
Proof
  Induct_on `fields` >> simp[well_typed_expr_def] >>
  gen_tac >> PairCases_on `h` >> simp[well_typed_expr_def]
QED

Theorem outcomes_free_typed_stmts_cons:
  type_stmts env ret (s::ss) = SOME out ==>
  ?mid. type_stmt env ret s = SOME mid /\ type_stmts mid ret ss = SOME out
Proof
  simp[type_stmt_def, AllCaseEqs()]
QED

Theorem outcomes_free_typed_expr_stmt:
  type_stmt env ret (Expr e) = SOME out ==> well_typed_expr env e
Proof
  simp[type_stmt_def, AllCaseEqs()]
QED

Theorem outcomes_free_typed_return:
  type_stmt env ret (Return (SOME e)) = SOME out ==> well_typed_expr env e
Proof
  simp[type_stmt_def, AllCaseEqs()]
QED

Theorem outcomes_free_typed_annassign:
  type_stmt env ret (AnnAssign id ty e) = SOME out ==>
  well_typed_expr env e /\ out = extend_local env id ty T
Proof
  simp[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem outcomes_free_typed_assign:
  type_stmt env ret (Assign tgt e) = SOME out ==>
  well_typed_expr env e /\ atarget_accepts env tgt (expr_type e)
Proof
  simp[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem outcomes_free_typed_base_assignment:
  atarget_accepts env (BaseTarget tgt) ty ==>
  ?vt. type_place_target env tgt = SOME vt
Proof
  Cases_on `type_place_target env tgt` >> simp[atarget_accepts_def]
QED

Theorem outcomes_free_typed_tuple_assignment:
  atarget_accepts env (TupleTarget tgts) ty ==>
  EVERY (\tgt. ?t. well_typed_atarget env tgt t) tgts
Proof
  simp[atarget_accepts_def, well_typed_atarget_def] >>
  rpt strip_tac >> gvs[EVERY_MEM, LIST_REL_EL_EQN] >>
  rpt strip_tac >> gvs[MEM_EL] >> metis_tac[]
QED

Theorem outcomes_free_typed_base_atarget:
  well_typed_atarget env (BaseTarget tgt) ty ==>
  type_place_target env tgt = SOME (Type ty)
Proof
  simp[well_typed_atarget_def, well_typed_target_def]
QED

Theorem outcomes_free_typed_augassign:
  type_stmt env ret (AugAssign ty tgt bop e) = SOME out ==>
  well_typed_expr env e /\ type_place_target env tgt = SOME (Type ty)
Proof
  simp[type_stmt_def, well_typed_target_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem outcomes_free_typed_append:
  type_stmt env ret (Append tgt e) = SOME out ==>
  well_typed_expr env e /\ (?vt. type_place_target env tgt = SOME vt)
Proof
  rw[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem outcomes_free_typed_if:
  type_stmt env ret (If e yes no) = SOME out ==>
  well_typed_expr env e /\
  (?yes_env. type_stmts env ret yes = SOME yes_env) /\
  (?no_env. type_stmts env ret no = SOME no_env)
Proof
  simp[type_stmt_def, AllCaseEqs(), IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem outcomes_free_typed_for:
  type_stmt env ret (For id ty it n ss) = SOME out ==>
  well_typed_iterator env ty it /\
  ?body_env. type_stmts (extend_local env id ty F) ret ss = SOME body_env
Proof
  simp[type_stmt_def, AllCaseEqs(), IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem outcomes_free_typed_array_iterator:
  well_typed_iterator env ty (Array e) ==> well_typed_expr env e
Proof
  simp[well_typed_iterator_def]
QED

Theorem outcomes_free_typed_range_iterator:
  well_typed_iterator env ty (Range lo hi) ==>
  well_typed_expr env lo /\ well_typed_expr env hi
Proof
  simp[well_typed_iterator_def]
QED

Theorem outcomes_free_typed_log:
  type_stmt env ret (Log id es) = SOME out ==>
  EVERY (well_typed_expr env) es
Proof
  rw[type_stmt_def, AllCaseEqs()] >>
  gvs[outcomes_free_typed_exprs_every]
QED

Theorem outcomes_free_typed_raise_reason:
  type_stmt env ret (Raise (RaiseReason e)) = SOME out ==>
  well_typed_expr env e
Proof
  simp[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem outcomes_free_typed_raise_custom:
  type_stmt env ret (Raise (RaiseCustomError err)) = SOME out ==>
  EVERY (well_typed_expr env) (custom_error_exprs err)
Proof
  simp[type_stmt_def, well_typed_custom_error_def,
       outcomes_free_typed_exprs_every, AllCaseEqs()]
QED

Theorem outcomes_free_typed_assert:
  type_stmt env ret (Assert e reason) = SOME out ==> well_typed_expr env e
Proof
  Cases_on `reason` >> simp[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem outcomes_free_typed_assert_reason:
  type_stmt env ret (Assert e (AssertReason msg)) = SOME out ==>
  well_typed_expr env msg
Proof
  simp[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem outcomes_free_typed_assert_custom:
  type_stmt env ret (Assert e (AssertCustomError err)) = SOME out ==>
  EVERY (well_typed_expr env) (custom_error_exprs err)
Proof
  simp[type_stmt_def, well_typed_custom_error_def,
       outcomes_free_typed_exprs_every, AllCaseEqs()] >> metis_tac[]
QED
