(* Runtime write safety reuses the type system's writes_ok traversals.
   Only mutation roots are restricted; immutable reads remain legal. *)
Theory vyperRuntimeWriteSafety
Ancestors
  list pair option vyperAST vyperContext vyperMisc vyperState
  vyperInterpreter vyperTypeSystem vyperLookupStorage

Definition runtime_write_root_def:
  runtime_write_root R (NameTarget id) = T /\
  runtime_write_root R (TopLevelNameTarget (sid,id)) = R sid id /\
  runtime_write_root R (SubscriptTarget tgt e) = runtime_write_root R tgt /\
  runtime_write_root R (AttributeTarget tgt id) = runtime_write_root R tgt
End

(* M is explicit so closure is independent of the evaluation stack/state. *)
Definition runtime_callable_writes_ok_def:
  runtime_callable_writes_ok M R <=>
    !sid fn ts mut nr args dflts ret body.
      M sid = SOME ts /\
      lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) body
End

Definition runtime_write_roots_resolve_def:
  runtime_write_roots_resolve cx R <=>
    !sid id. R sid id ==>
      ?ts decl. get_module_code cx sid = SOME ts /\
                find_var_decl_by_name id ts = SOME decl
End

Theorem runtime_callable_writes_ok_lookup_cong:
  (!sid. M sid = N sid) ==>
  (runtime_callable_writes_ok M R <=> runtime_callable_writes_ok N R)
Proof
  strip_tac >> simp[runtime_callable_writes_ok_def]
QED

(* Both internal defaults and push_function update only stk in the context. *)
Theorem runtime_write_safety_stk:
  runtime_callable_writes_ok (get_module_code (cx with stk := stk)) R =
    runtime_callable_writes_ok (get_module_code cx) R /\
  runtime_write_roots_resolve (cx with stk := stk) R =
    runtime_write_roots_resolve cx R
Proof
  simp[runtime_callable_writes_ok_def, runtime_write_roots_resolve_def,
       get_module_code_stk]
QED

(* A small probe: the root classifier does not swallow the index traversal. *)
Theorem runtime_pop_subscript_writes_ok:
  expr_writes_ok (runtime_write_root R) (Pop ty (SubscriptTarget tgt idx)) =
    (runtime_write_root R tgt /\
     target_writes_ok (runtime_write_root R) tgt /\
     expr_writes_ok (runtime_write_root R) idx)
Proof
  simp[expr_writes_ok_def, runtime_write_root_def]
QED
