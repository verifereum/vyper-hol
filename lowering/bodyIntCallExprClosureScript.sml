(* Support closure used by expression compiler callback boundaries.
   Pure-call exclusion and member-size bounds are reused from
   supported_pure_no_internal_call and expr_list_member_bound. *)
Theory bodyIntCallExprClosure
Ancestors
  bodyIntCallExprLabels supportedExprTraverse supportedExprs exprCallBounds list

Theorem supported_closure_subscript:
  (supported_pure_expr tops (Subscript ann base_e key) \/
   supported_place_expr tops (Subscript ann base_e key) \/
   supported_effect_expr tops (Subscript ann base_e key) \/
   supported_effect_place_expr tops (Subscript ann base_e key)) /\
  ~expr_has_internal_call (Subscript ann base_e key) ==>
  ((supported_pure_expr tops base_e \/ supported_place_expr tops base_e \/
    supported_effect_expr tops base_e \/ supported_effect_place_expr tops base_e) /\
   ~expr_has_internal_call base_e) /\
  ((supported_pure_expr tops key \/ supported_place_expr tops key \/
    supported_effect_expr tops key \/ supported_effect_place_expr tops key) /\
   ~expr_has_internal_call key)
Proof
  simp[supported_pure_expr_def, supported_effect_expr_def,
       expr_has_internal_call_def, supported_expr_exists_def,
       expr_internal_call_root_def] >> metis_tac[]
QED

Theorem supported_closure_attribute:
  (supported_pure_expr tops (Attribute ann base_e fld) \/
   supported_place_expr tops (Attribute ann base_e fld) \/
   supported_effect_expr tops (Attribute ann base_e fld) \/
   supported_effect_place_expr tops (Attribute ann base_e fld)) /\
  ~expr_has_internal_call (Attribute ann base_e fld) ==>
  (supported_pure_expr tops base_e \/ supported_place_expr tops base_e \/
   supported_effect_expr tops base_e \/ supported_effect_place_expr tops base_e) /\
  ~expr_has_internal_call base_e
Proof
  simp[supported_pure_expr_def, supported_effect_expr_def,
       expr_has_internal_call_def, supported_expr_exists_def,
       expr_internal_call_root_def] >> metis_tac[]
QED

Theorem supported_closure_pure_member:
  MEM e args /\ EVERY (supported_pure_expr tops) args ==>
  (supported_pure_expr tops e \/ supported_place_expr tops e \/
   supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
  ~expr_has_internal_call e
Proof
  simp[EVERY_MEM] >> metis_tac[supported_pure_no_internal_call]
QED

(* Property transport is independent of support and of the particular
   block-tail/reservation postcondition.  Keeping it polymorphic avoids
   repeating the same wrapper argument for every compiler invariant. *)
Theorem expr_child_callback_property:
  expr_size e < n ==>
  (P (expr_child_callback n f cenv ty e) <=> P (f cenv ty e))
Proof
  strip_tac >>
  `expr_child_callback n f cenv ty e = f cenv ty e` by
    simp[FUN_EQ_THM, expr_child_callback_def] >> simp[]
QED

Theorem builtin_child_callback_property:
  list_size expr_size args < n ==>
  (P (builtin_child_callback n f cenv ann ty bi args) <=>
   P (f cenv ann ty bi args))
Proof
  strip_tac >>
  `builtin_child_callback n f cenv ann ty bi args = f cenv ann ty bi args` by
    simp[FUN_EQ_THM, builtin_child_callback_def] >> simp[]
QED

Theorem type_child_callback_property:
  list_size expr_size args < n ==>
  (P (type_child_callback n f cenv ann ty tb rt args) <=>
   P (f cenv ann ty tb rt args))
Proof
  strip_tac >>
  `type_child_callback n f cenv ann ty tb rt args = f cenv ann ty tb rt args` by
    simp[FUN_EQ_THM, type_child_callback_def] >> simp[]
QED
