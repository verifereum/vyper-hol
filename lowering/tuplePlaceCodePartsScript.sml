(* Compiler boundary retains the original value location and lowered layout. *)
Theory tuplePlaceCodeParts
Ancestors
  tupleAssignParts exprSimUnwrap exprOperandVar stmtLoweringMono
Libs monadsyntax

Theorem tuple_place_compile_parts:
  compile_stmt cenv lctx ty (Assign (TupleTarget gs) e) sa = ((),sf) ==>
  ?vv sm op su.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    unwrap_value cenv vv sm = (op,su) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
    compile_tuple_unpack cenv (lowered_value_type cenv e)
      (is_memory_view e /\ vv_location vv = SOME LocMemory) gs op su = ((),sf)
Proof
  simp[Once stmtLoweringTheory.compile_stmt_def, compileEnvTheory.comp_bind_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `_ = (vv,sm)` >>
  Cases_on `unwrap_value cenv vv sm` >>
  rename1 `_ = (op,su)` >>
  simp[exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def]
QED

Theorem tuple_place_compile_parts_frames:
  compile_stmt cenv lctx ty (Assign (TupleTarget gs) e) sa = ((),sf) /\
  fn_has_code sa sf func /\ local_ptrs_reserved cenv sa ==>
  ?vv sm op su.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    unwrap_value cenv vv sm = (op,su) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
    compile_tuple_unpack cenv (lowered_value_type cenv e)
      (is_memory_view e /\ vv_location vv = SOME LocMemory) gs op su = ((),sf) /\
    cs_extends sa sm /\ cs_extends sm su /\ cs_extends su sf /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\ fn_has_code su sf func /\
    sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id /\
    local_ptrs_reserved cenv su /\
    (!x. op = Var x ==> not_fresh_at su x)
Proof
  strip_tac >> drule tuple_place_compile_parts >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  `cs_extends su sf` by
    (mp_tac (cj 4 ci_mono_return_helpers) >>
     disch_then (qspecl_then [`cenv`, `lowered_value_type cenv e`,
       `is_memory_view e /\ vv_location vv = SOME LocMemory`, `gs`, `op`, `su`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sf func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sm su func /\ fn_has_code su sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `local_ptrs_reserved cenv su` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  metis_tac[compile_lower_value_var]
QED
