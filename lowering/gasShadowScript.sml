(* Proof-only shadow compilation distinguishes explicit source GAS from
   generated GAS without changing the compiler or either runtime. *)
Theory gasShadow
Ancestors
  vyperAST list pair option basicSize

Definition gas_shadow_builtin_def:
  gas_shadow_builtin bi =
    if bi = Env MsgGas then Env GasPrice else bi
End

Definition gas_shadow_expr_def:
  gas_shadow_expr (Name ty name) = Name ty name /\
  gas_shadow_expr (TopLevelName ty name) = TopLevelName ty name /\
  gas_shadow_expr (FlagMember ty name member) = FlagMember ty name member /\
  gas_shadow_expr (Literal ty lit) = Literal ty lit /\
  gas_shadow_expr (IfExp ty test yes no) =
    IfExp ty (gas_shadow_expr test) (gas_shadow_expr yes) (gas_shadow_expr no) /\
  gas_shadow_expr (StructLit ty name fields) =
    StructLit ty name (MAP (I ## gas_shadow_expr) fields) /\
  gas_shadow_expr (Subscript ty arr idx) =
    Subscript ty (gas_shadow_expr arr) (gas_shadow_expr idx) /\
  gas_shadow_expr (Attribute ty obj name) = Attribute ty (gas_shadow_expr obj) name /\
  gas_shadow_expr (Builtin ty bi args) =
    Builtin ty (gas_shadow_builtin bi) (MAP gas_shadow_expr args) /\
  gas_shadow_expr (TypeBuiltin ty bi result_ty args) =
    TypeBuiltin ty bi result_ty (MAP gas_shadow_expr args) /\
  gas_shadow_expr (Call ty target args fallback) =
    Call ty target (MAP gas_shadow_expr args) (OPTION_MAP gas_shadow_expr fallback) /\
  gas_shadow_expr (Pop ty target) = Pop ty (gas_shadow_target target) /\
  gas_shadow_target (NameTarget name) = NameTarget name /\
  gas_shadow_target (TopLevelNameTarget name) = TopLevelNameTarget name /\
  gas_shadow_target (AttributeTarget target name) =
    AttributeTarget (gas_shadow_target target) name /\
  gas_shadow_target (SubscriptTarget target idx) =
    SubscriptTarget (gas_shadow_target target) (gas_shadow_expr idx)
End

Definition gas_shadow_assignment_def:
  gas_shadow_assignment (BaseTarget target) = BaseTarget (gas_shadow_target target) /\
  gas_shadow_assignment (TupleTarget targets) =
    TupleTarget (MAP gas_shadow_assignment targets)
End

Definition gas_shadow_iterator_def:
  gas_shadow_iterator (Array arr) = Array (gas_shadow_expr arr) /\
  gas_shadow_iterator (Range lo hi) = Range (gas_shadow_expr lo) (gas_shadow_expr hi)
End

Definition gas_shadow_custom_error_def:
  gas_shadow_custom_error (CustomError name args kwargs) =
    CustomError name (MAP gas_shadow_expr args) (MAP (I ## gas_shadow_expr) kwargs)
End

Definition gas_shadow_assert_reason_def:
  gas_shadow_assert_reason AssertBare = AssertBare /\
  gas_shadow_assert_reason AssertUnreachable = AssertUnreachable /\
  gas_shadow_assert_reason (AssertReason e) = AssertReason (gas_shadow_expr e) /\
  gas_shadow_assert_reason (AssertCustomError err) =
    AssertCustomError (gas_shadow_custom_error err)
End

Definition gas_shadow_raise_reason_def:
  gas_shadow_raise_reason RaiseBare = RaiseBare /\
  gas_shadow_raise_reason RaiseUnreachable = RaiseUnreachable /\
  gas_shadow_raise_reason (RaiseReason e) = RaiseReason (gas_shadow_expr e) /\
  gas_shadow_raise_reason (RaiseCustomError err) =
    RaiseCustomError (gas_shadow_custom_error err)
End

Definition gas_shadow_stmt_def:
  gas_shadow_stmt Pass = Pass /\
  gas_shadow_stmt Continue = Continue /\
  gas_shadow_stmt Break = Break /\
  gas_shadow_stmt (Expr e) = Expr (gas_shadow_expr e) /\
  gas_shadow_stmt (For name ty iter bound body) =
    For name ty (gas_shadow_iterator iter) bound (MAP gas_shadow_stmt body) /\
  gas_shadow_stmt (If test yes no) =
    If (gas_shadow_expr test) (MAP gas_shadow_stmt yes) (MAP gas_shadow_stmt no) /\
  gas_shadow_stmt (Assert test reason) =
    Assert (gas_shadow_expr test) (gas_shadow_assert_reason reason) /\
  gas_shadow_stmt (Log name args) = Log name (MAP gas_shadow_expr args) /\
  gas_shadow_stmt (Raise reason) = Raise (gas_shadow_raise_reason reason) /\
  gas_shadow_stmt (Return result) = Return (OPTION_MAP gas_shadow_expr result) /\
  gas_shadow_stmt (Assign target rhs) =
    Assign (gas_shadow_assignment target) (gas_shadow_expr rhs) /\
  gas_shadow_stmt (AugAssign ty target op rhs) =
    AugAssign ty (gas_shadow_target target) op (gas_shadow_expr rhs) /\
  gas_shadow_stmt (Append target rhs) =
    Append (gas_shadow_target target) (gas_shadow_expr rhs) /\
  gas_shadow_stmt (AnnAssign name ty rhs) = AnnAssign name ty (gas_shadow_expr rhs)
End

Definition gas_shadow_mutability_def:
  gas_shadow_mutability (Constant e) = Constant (gas_shadow_expr e) /\
  gas_shadow_mutability mut = mut
End

Definition gas_shadow_toplevel_def:
  gas_shadow_toplevel
    (FunctionDecl vis mut lock raw name args defaults result_ty body) =
    FunctionDecl vis mut lock raw name args (MAP gas_shadow_expr defaults)
      result_ty (MAP gas_shadow_stmt body) /\
  gas_shadow_toplevel (VariableDecl vis mut name ty slot) =
    VariableDecl vis (gas_shadow_mutability mut) name ty slot /\
  gas_shadow_toplevel top = top
End

Theorem gas_shadow_expr_type[simp]:
  expr_type (gas_shadow_expr e) = expr_type e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, expr_type_def]
QED

Theorem gas_shadow_builtin_size[simp]:
  builtin_size (gas_shadow_builtin bi) = builtin_size bi
Proof
  rw[gas_shadow_builtin_def] >> simp[builtin_size_def, env_item_size_def]
QED

Theorem shadow_list_size_map[local]:
  (!x. MEM x xs ==> s (f x) = s x) ==>
  list_size s (MAP f xs) = list_size s xs
Proof
  Induct_on `xs` >>
  simp_tac bool_ss [MAP, list_size_def, MEM] >> metis_tac[]
QED

Theorem shadow_field_size_map[local]:
  (!k e. MEM (k,e) fields ==> s (f e) = s e) ==>
  list_size (pair_size ks s) (MAP (I ## f) fields) =
  list_size (pair_size ks s) fields
Proof
  strip_tac >> irule shadow_list_size_map >>
  Cases >> simp[pair_size_def] >> metis_tac[]
QED

Theorem shadow_option_size_map[local]:
  (!e. opt = SOME e ==> s (f e) = s e) ==>
  option_size s (OPTION_MAP f opt) = option_size s opt
Proof
  Cases_on `opt` >> simp[]
QED

Theorem gas_shadow_expr_size:
  (!e. expr_size (gas_shadow_expr e) = expr_size e) /\
  (!target. base_assignment_target_size (gas_shadow_target target) =
            base_assignment_target_size target)
Proof
  ho_match_mp_tac expr_induction >>
  rpt conj_tac >> rpt gen_tac >> rpt disch_tac >>
  asm_simp_tac bool_ss [gas_shadow_expr_def, expr_size_def,
    gas_shadow_builtin_size, shadow_list_size_map,
    shadow_field_size_map, shadow_option_size_map]
  >- (`!k e. MEM (k,e) l ==>
         expr_size (gas_shadow_expr e) = expr_size e` by
        (rpt strip_tac >> first_x_assum irule >>
         qexists_tac `(k,e)` >> simp[]) >>
      `list_size (pair_size (list_size char_size) expr_size)
         (MAP (I ## gas_shadow_expr) l) =
       list_size (pair_size (list_size char_size) expr_size) l` by
        (irule shadow_field_size_map >> asm_rewrite_tac []) >>
      asm_rewrite_tac []) >>
  rename1 `OPTION_MAP gas_shadow_expr fallback` >>
  Cases_on `fallback` >> gvs[]
QED
