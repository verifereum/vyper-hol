(* Compiler-internal structural recursion boundary. The bound is derived from
   the parent AST (or dispatcher argument list), never from external fuel.
   Invalid callback inputs have an explicit INVALID result. *)
Theory exprCallBounds
Ancestors
  emitHelper compileEnv context vyperAST list basicSize

Definition invalid_expr_call_def:
  invalid_expr_call ty st =
    (let (_, st') = emit_inst INVALID [] [] st in
     (StackValue ty (Lit 0w), st'))
End

Definition expr_child_callback_def[simp]:
  expr_child_callback bound cfn cenv ty e st =
    if expr_size e < bound then cfn cenv ty e st
    else invalid_expr_call (expr_type e) st
End

Theorem expr_child_callback_cong[defncong]:
  bound = bound' ∧
  (∀cenv ty e st. expr_size e < bound' ⇒ f cenv ty e st = g cenv ty e st) ⇒
  expr_child_callback bound f = expr_child_callback bound' g
Proof
  rpt strip_tac >> gvs[FUN_EQ_THM, expr_child_callback_def] >> rw[] >> simp[]
QED

Definition builtin_child_callback_def[simp]:
  builtin_child_callback bound dispatch cenv ret_ty ty bi args st =
    if list_size expr_size args < bound then dispatch cenv ret_ty ty bi args st
    else invalid_expr_call ret_ty st
End

Theorem builtin_child_callback_cong[defncong]:
  bound = bound' ∧
  (∀cenv ret_ty ty bi args st. list_size expr_size args < bound' ⇒
     f cenv ret_ty ty bi args st = g cenv ret_ty ty bi args st) ⇒
  builtin_child_callback bound f = builtin_child_callback bound' g
Proof
  rpt strip_tac >> gvs[FUN_EQ_THM, builtin_child_callback_def] >> rw[] >> simp[]
QED

Definition type_child_callback_def[simp]:
  type_child_callback bound dispatch cenv vv_ty ty tb ret_ty args st =
    if list_size expr_size args < bound then dispatch cenv vv_ty ty tb ret_ty args st
    else invalid_expr_call vv_ty st
End

Theorem type_child_callback_cong[defncong]:
  bound = bound' ∧
  (∀cenv vv_ty ty tb ret_ty args st. list_size expr_size args < bound' ⇒
     f cenv vv_ty ty tb ret_ty args st = g cenv vv_ty ty tb ret_ty args st) ⇒
  type_child_callback bound f = type_child_callback bound' g
Proof
  rpt strip_tac >> gvs[FUN_EQ_THM, type_child_callback_def] >> rw[] >> simp[]
QED

Theorem expr_child_callback_valid:
  expr_size e < bound ⇒
  expr_child_callback bound cfn cenv ty e st = cfn cenv ty e st
Proof
  simp[expr_child_callback_def]
QED

Theorem expr_child_callback_invalid:
  bound ≤ expr_size e ⇒
  expr_child_callback bound cfn cenv ty e st = invalid_expr_call (expr_type e) st
Proof
  simp[expr_child_callback_def]
QED

Theorem expr_list_member_bound:
  ∀es e. MEM e es ⇒ expr_size e < list_size expr_size es
Proof
  Induct >> simp[list_size_def] >> rpt strip_tac >>
  gvs[] >> res_tac >> simp[]
QED

Theorem expr_ifexp_child_bounds:
  expr_size cond < expr_size (IfExp ann cond then_e else_e) ∧
  expr_size then_e < expr_size (IfExp ann cond then_e else_e) ∧
  expr_size else_e < expr_size (IfExp ann cond then_e else_e)
Proof
  simp[expr_size_def]
QED

Theorem expr_subscript_child_bounds:
  expr_size base_e < expr_size (Subscript ann base_e idx) ∧
  expr_size idx < expr_size (Subscript ann base_e idx)
Proof
  simp[expr_size_def]
QED

Theorem expr_attribute_child_bound:
  expr_size base_e < expr_size (Attribute ann base_e field_name)
Proof
  simp[expr_size_def]
QED

Theorem expr_list_size_eq[simp]:
  ∀es. expr4_size es = list_size expr_size es
Proof
  Induct >> simp[expr_size_def, list_size_def]
QED

Theorem expr_builtin_dispatch_bound:
  list_size expr_size args < expr_size (Builtin ann bi args) ∧
  list_size expr_size args < expr_size (TypeBuiltin ann tb ret_ty args)
Proof
  simp[expr_size_def]
QED

Theorem expr_call_arg_bound:
  MEM child args ⇒ expr_size child < expr_size (Call ann target args default_ret)
Proof
  strip_tac >> drule expr_list_member_bound >> simp[expr_size_def]
QED

Theorem expr_call_default_bound:
  expr_size child < expr_size (Call ann target args (SOME child))
Proof
  simp[expr_size_def]
QED

Theorem expr_fields_size_eq[simp]:
  ∀fields. expr1_size fields =
    list_size (pair_size (list_size char_size) expr_size) fields
Proof
  Induct >> simp[expr_size_def, list_size_def] >>
  Cases_on `h` >> simp[expr_size_def, pair_size_def]
QED

Theorem expr_struct_field_bound:
  ∀fields name child.
    MEM (name,child) fields ⇒ expr_size child < expr_size (StructLit ann nsid fields)
Proof
  Induct >> simp[expr_size_def] >>
  Cases_on `h` >> simp[expr_size_def, list_size_def, pair_size_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> simp[]
QED
