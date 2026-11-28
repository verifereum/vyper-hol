Theory s1PrefixNamedConstRow
Ancestors
  s1PrefixNamedConst s1PrefixPreds vyperAST vyperContext vyperState vyperTypeCallGraph list

Theorem named_const_size_row:
  !cx ann xs.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Builtin ann NamedConst xs))) /\
    (!a. expr_size a < expr_size (Builtin ann NamedConst xs) /\
         (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
           EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
             (vyperTypeCallGraph$int_calls_expr a)) ==>
         body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann NamedConst xs)
Proof
  rpt strip_tac >> irule named_const_expr_prefix_ok >> rpt strip_tac >>
  `LENGTH xs = 1` by fs[type_check_def, assert_def, builtin_args_length_ok_def] >>
  fs[LENGTH_EQ_1, body_exprs_prefix_ok_def] >>
  first_x_assum irule >> fs[expr_size_def, list_size_def, int_calls_expr_def, EVERY_APPEND]
QED
