(* For-only typing and support projections for the full body proof. *)
Theory bodyFullForFacts
Ancestors
  vyperTypeSystem supportedStmts finite_map

val _ = Parse.hide "body";

Theorem type_stmt_for_projection:
  type_stmt env ret_ty (For id typ it n body) = SOME env' ==>
  env' = env /\
  assignable_type env.type_defs typ /\
  well_typed_iterator env typ it /\
  id NOTIN FDOM env.var_types /\
  iterator_unmodified it body /\
  IS_SOME (type_stmts (extend_local env id typ F) ret_ty body)
Proof
  simp[Once type_stmt_def] >> IF_CASES_TAC >> gvs[]
QED

Theorem supported_stmt_for_projection:
  supported_stmt tops bindings (For id typ it n body) ==>
  supported_iterator tops typ it n
Proof
  simp[Once supported_stmt_def]
QED
