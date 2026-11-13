(* Memory-safe body induction leaf for the uint2str digit buffer. *)
Theory bodyMemBiUint2Str
Ancestors
  bodyMemoryPreds bodyMemBiUint2StrCompose bodyExprForceMemory
  exprSimUint2Str exprSimSource exprSimHypsDefs vyperTyping
  vyperContext vyperAST exprSimMemDefs compileEnv exprLowering

Theorem body_builtin_uint2str_mem:
  !cx ty n es.
    (builtin_args_length_ok (Uint2Str n) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Uint2Str n) es)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Builtin ty (Uint2Str n) es)` by fs[expr_body_pre_def] >>
  drule uint2str_expr_types >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> fs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx ty' e es'` by
    (fs[builtin_args_length_ok_def, body_exprs_mem_ok_def, body_expr_mem_ok_def] >>
     metis_tac[]) >>
  `expr_vv_sim_mem ctx func cenv cx ty' (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es'` by
    (irule compile_uint2str_typed_vv_sim_mem >> metis_tac[]) >>
  simp[] >>
  match_mp_tac body_expr_sim_mem_of_vv_sim_mem >>
  qexists_tac `env` >>
  rpt conj_tac
  >- simp[]
  >- metis_tac[]
  >- metis_tac[] >>
  rpt gen_tac >> rewrite_tac[compile_uint2str_singleton] >>
  Cases_on `lower_value compile_expr cenv ty' e sa` >> simp[] >>
  rename1 `compile_uint2str v n sz sm` >>
  Cases_on `compile_uint2str v n sz sm` >> simp[as_ptr_val_def]
QED
