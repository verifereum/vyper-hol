Theory exprNamedConstResult
Ancestors
  exprLowering exprSimHypsDefs compileEnv context vyperAST namesBuiltinExclusions
Libs
  pairLib

Theorem named_const_nonword_compile_shape:
  ~is_word_type ann /\
  compile_expr cenv ty (Builtin ann NamedConst args) sa = (vv,sb) ==>
  ?op. vv = LocatedValue ann (mk_ptr op LocMemory)
Proof
  simp[compile_expr_builtin_dispatch, names_builtin_exclusions] >>
  simp[Once compile_builtin_dispatch_component_eq] >>
  pairarg_tac >> simp[as_ptr_val_def] >>
  strip_tac >> gvs[] >>
  rename1 `lower_value _ _ _ _ _ = (raw,_)` >>
  qexists `case raw of Label _ => Lit 0w | _ => raw` >> simp[]
QED
