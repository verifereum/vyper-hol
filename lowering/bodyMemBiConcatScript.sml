(* Memory case of the body induction for concat. *)
Theory bodyMemBiConcat
Ancestors
  bodyMemoryPreds bodyMemBiConcatFragments bodyMemBiConcatPrefix bodyMemBiConcatBounds bodyMemBiConcatArms bodyMemBiConcatArgs bodyMemBiConcatResult
  bodyExprForceMemory exprSimConcatResult exprSimHypsDefs vyperTyping

Theorem body_builtin_concat_mem:
  !cx ty n es.
    (builtin_args_length_ok (Concat n) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Concat n) es)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `builtin_args_length_ok (Concat n) (LENGTH es)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.well_typed_builtin_app_def,
          vyperContextTheory.builtin_args_length_ok_def] >> metis_tac[]) >>
  `body_exprs_mem_ok cx es` by metis_tac[] >>
  `expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (Concat n) es) es'` by
    (irule concat_result_vv_sim_mem >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule body_expr_sim_mem_of_vv_sim_mem >>
  conj_tac
  >- (rpt strip_tac >> drule concat_compile_shape >> simp[]) >>
  conj_tac >- (qexists_tac `env` >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
