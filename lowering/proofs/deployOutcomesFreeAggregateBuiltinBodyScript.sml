Theory deployOutcomesFreeAggregateBuiltinBody
Ancestors
  deployOutcomesFreeSelectors deployOutcomesFreeExprBody
  deployOutcomesFreeGenerators exprLowering list

Theorem outcomes_free_builtin_environment:
  (!item st. Q st ==> Q (SND (compile_env_var item st))) /\
  (!st. Q st ==> Q (SND (compile_builtin_calldatasize st))) /\
  ((?item. bi = Env item) \/ bi = CalldataLen) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >> Cases_on `bi` >> gvs[] >>
  simp[compile_builtin_dispatch_body_def, outcomes_free_as_stack_val]
QED

Theorem outcomes_free_builtin_remaining_unary:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v ity st. Q st ==> Q (SND (compile_invert v ity ce st))) /\
  (!ops st. Q st ==> Q (SND (emit_op ISZERO ops st))) /\
  (!e item st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (compile_acc f ce e item st))) /\
  (!v loc st. Q st ==>
     Q (SND (compile_builtin_len ce.ce_is_ctor ce.ce_imm_alloca v loc st))) /\
  (!v m d st. Q st ==> Q (SND (compile_as_wei_value_decimal v m d st))) /\
  (!v m sg st. Q st ==> Q (SND (compile_as_wei_value_int v m sg st))) /\
  (!ity lit st. Q st ==> Q (SND (compile_literal_vv ity lit st))) /\
  (!ity v fixed st. Q st ==> Q (SND (compile_method_id_runtime ity v fixed st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ty bi (MAP expr_type args) /\
  (bi = Not \/ (?item. bi = Acc item) \/ bi = Len \/
   (?denom. bi = AsWeiValue denom) \/ bi = MethodId) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >>
  `LENGTH args = 1` by metis_tac[outcomes_free_builtin_arities] >>
  `well_typed_expr env (HD args) /\
   ~supported_expr_exists constructor_call_root (HD args)` by
    (drule_all outcomes_free_typed_children >> strip_tac >>
     `args <> []` by (strip_tac >> gvs[]) >>
     drule_all outcomes_free_head >> simp[]) >>
  `!ity st. Q st ==> Q (SND (lower_value f ce ity (HD args) st))` by
    (rpt strip_tac >> irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
  Cases_on `bi` >> gvs[] >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[outcomes_free_as_stack_val, outcomes_free_as_ptr_val]) >>
  rpt IF_CASES_TAC >> gvs[outcomes_free_as_stack_val, outcomes_free_as_ptr_val, AllCaseEqs()]
  >~ [`Q (SND (emit_op ISZERO [v] st1))`]
  >- (qpat_x_assum `!ops st. Q st ==> Q (SND (emit_op ISZERO ops st))`
     (qspecl_then [`[v]`, `st1`] mp_tac) >>
   qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
     (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >> gvs[])
  >~ [`Q (SND (compile_invert v ity ce st1))`]
  >- (qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
        (qspecl_then [`ity`, `s`] mp_tac) >>
      gvs[] >> strip_tac >> simp[])
  >~ [`Q (SND (compile_builtin_len _ _ _ _ st1))`]
  >- (qpat_x_assum `!e ity st. _`
        (qspecl_then [`HD args`, `ty`, `s`] mp_tac) >>
      gvs[] >> strip_tac >> simp[])
  >~ [`Q (SND (compile_as_wei_value_decimal _ _ _ st1))`]
  >- (qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
        (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >>
      gvs[] >> strip_tac >> simp[])
  >~ [`Q (SND (compile_as_wei_value_int _ _ _ st1))`]
  >- (qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
        (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >>
      gvs[] >> strip_tac >> simp[]) >>
  qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
    (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >>
  gvs[] >> strip_tac >> Cases_on `method_id_literal (HD args)` >>
  simp[outcomes_free_as_stack_val, outcomes_free_as_ptr_val]
QED
