(* Compiler slices for a tuple source which cannot alias its targets. *)
Theory tupleUnstagedParts
Ancestors
  tupleAssignParts tupleAssignCode stmtSimDefs stmtSimProps stmtLowering
  exprLowering exprLoweringProps exprSimUnwrap compileEnv fragExec loweringPosts stmtSimReturn

Theorem assign_tuple_unstaged_decompose[local]:
  !ce lctx ty gs e src_tys sa sf c.
    stmt_env ce lctx ty (Assign (TupleTarget gs) e) sa = (c,sf) /\
    lowered_value_type ce e = TupleT src_tys /\ ~is_memory_view e ==>
    c = ce /\
    ?vv sc op su elems ss.
      compile_expr ce (expr_type e) e sa = (vv,sc) /\
      unwrap_value ce vv sc = (op,su) /\
      compile_tuple_load_all ce op src_tys 0 su = (elems,ss) /\
      compile_tuple_store_all ce src_tys gs elems ss = ((),sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
     compile_tuple_unpack_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sc)` >>
  Cases_on `unwrap_value ce vv sc` >>
  rename1 `unwrap_value _ _ _ = (op,su)` >> simp[] >>
  Cases_on `compile_tuple_load_all ce op src_tys 0 su` >>
  rename1 `compile_tuple_load_all _ _ _ _ _ = (elems,ss)` >> simp[] >>
  Cases_on `compile_tuple_store_all ce src_tys gs elems ss` >>
  rename1 `compile_tuple_store_all _ _ _ _ _ = (u,sf1)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[]
QED

Theorem assign_tuple_unstaged_parts:
  !ce lctx ty gs e src_tys sa sf c func.
    stmt_env ce lctx ty (Assign (TupleTarget gs) e) sa = (c,sf) /\
    lowered_value_type ce e = TupleT src_tys /\ ~is_memory_view e /\
    fn_has_code sa sf func ==>
    c = ce /\
    ?op su elems ss.
      lower_value compile_expr ce (expr_type e) e sa = (op,su) /\
      compile_tuple_load_all ce op src_tys 0 su = (elems,ss) /\
      compile_tuple_store_all ce src_tys gs elems ss = ((),sf) /\
      cs_extends sa su /\ cs_extends su ss /\ cs_extends ss sf /\
      fn_has_code sa su func /\ fn_has_code su ss func /\
      fn_has_code ss sf func /\
      sa.cs_next_var <= su.cs_next_var /\
      su.cs_next_var <= ss.cs_next_var /\ ss.cs_next_var <= sf.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_unstaged_decompose >> strip_tac >>
  qpat_x_assum `c = ce` SUBST_ALL_TAC >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_tuple_load_all_grows >> strip_tac >>
  drule tuple_target_stores_growth >> strip_tac >>
  `cs_extends su sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func /\ fn_has_code su sf func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code su ss func /\ fn_has_code ss sf func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[]
QED
