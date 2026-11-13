(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: floor, as_wei_value, uint256_addmod, uint256_mulmod and
   pow_mod256 (S1: exprSimWordBuiltins' word_builtin_case). *)
Theory bodyMemBiWord
Ancestors
  bodyMemoryPreds bodyMemBiWordCases exprSimMemoryStack exprSimWordBuiltins
  exprSimSource bodyArgsMemory exprSimHypsDefs exprSimDefs
    vyperTypeSystem vyperTyping exprLowering list rich_list vyperContext
  compileEnv exprLoweringProps

Theorem body_builtin_word_mem:
  !cx ty bt es.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/ bt = AddMod \/ bt = MulMod \/
     bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >> rpt gen_tac >> strip_tac >>
  `well_typed_builtin_app ty bt (MAP expr_type es)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (gvs[well_typed_builtin_app_def, builtin_args_length_ok_def,
         MAP_EQ_CONS, LENGTH_EQ_NUM_compute]) >>
  `body_exprs_mem_ok cx es` by metis_tac[] >>
  `EVERY (\e. word_value_type (expr_type e)) es` by
    (irule word_builtin_operand_types >> metis_tac[]) >>
  `!arg_ty. typed_args_ready_mem ctx func cenv cx arg_ty
      (expr_sim_inv cenv cx env) es` by
    (gen_tac >> irule typed_args_ready_mem_of_body >>
     reverse conj_tac >- metis_tac[] >>
     rpt gen_tac >> strip_tac >>
     conj_tac
     >- (irule expr_body_pre_builtin_arg >> simp[] >>
         qexistsl_tac [`ty`, `es`, `bt`, `es'`] >> simp[] >>
         disj1_tac >> rpt strip_tac >> gvs[]) >>
     qpat_x_assum `EVERY _ es` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >>
     disch_then (mp_tac o MATCH_MP word_value_type_word) >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty' (Builtin ty bt es) es'` by
    (gvs[well_typed_builtin_app_def, MAP_EQ_CONS, LENGTH_EQ_NUM_compute] >>
     metis_tac[compile_floor_typed_sim_mem, compile_as_wei_value_typed_sim_mem,
               compile_modular_typed_sim_mem, compile_pow_mod256_typed_sim_mem]) >>
  `is_word_type (expr_type (Builtin ty bt es))` by
    gvs[well_typed_builtin_app_def, is_word_type_def, vyperASTTheory.expr_type_def] >>
  simp[] >> irule body_expr_vv_sim_mem_stack_word >>
  simp[] >>
  simp[] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty' (Builtin ty bt es) sa` >>
      drule_at Any compile_word_builtin_stack >> simp[] >>
      impl_tac
      >- gvs[well_typed_builtin_app_def, MAP_EQ_CONS, LENGTH_EQ_NUM_compute] >>
      metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]
QED
