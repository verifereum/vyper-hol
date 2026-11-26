Theory s1PrefixNamedConstRow
Ancestors
  s1PrefixNamedConst s1PrefixPreds vyperAST vyperContext vyperState list

Theorem named_const_size_row:
  !cx ann xs.
    (!a. expr_size a < expr_size (Builtin ann NamedConst xs) ==>
         body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann NamedConst xs)
Proof
  rpt strip_tac >> irule named_const_expr_prefix_ok >> rpt strip_tac >>
  `LENGTH xs = 1` by fs[type_check_def, assert_def, builtin_args_length_ok_def] >>
  fs[LENGTH_EQ_1, body_exprs_prefix_ok_def] >>
  first_x_assum irule >> simp[expr_size_def, list_size_def]
QED
