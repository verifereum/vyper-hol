(* Memory case of the body induction for extract32: a dynamic Bytes source
   with an unsigned start (the S1 case compile_extract32_ready_sim covers),
   and the rest, held in bodyMemTbExtract32Held. *)
Theory bodyMemTbExtract32
Ancestors
  exprSimMemoryStack exprSimHypsDefs exprSimConvert bodyMemTbExtract32Cuts
  vyperTypeSystem vyperAST vyperState vyperInterpreter vyperContext vyperValue compileEnv
  bodyMemoryPreds bodyMemTbExtract32Held bodyMemTbExtract32Load
  bodyMemTbExtract32Action bodyMemTbExtract32TypedSuffix bodyMemTbExtract32Bind bodyMemTbExtract32Compose

Theorem body_type_builtin_extract32_ready_mem_case:
  !cx v11 typ src off m k.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Extract32) 2)
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx [src; off]) /\
    expr_type src = BaseT (BytesT (Dynamic m)) /\
    expr_type off = BaseT (UintT k) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Extract32) typ [src; off])
Proof
  rpt gen_tac >> strip_tac >>
  `body_exprs_mem_ok cx [src;off]` by
    (first_x_assum (qspecl_then [`ARB`, `()`, `ARB`] mp_tac) >>
     simp[type_check_def, type_builtin_args_length_ok_def,
          vyperStateTheory.assert_def, return_def]) >>
  rw[body_expr_mem_ok_def] >>
  `expr_sim_mem ctx func cenv cx ty (TypeBuiltin v11 Extract32 typ [src;off]) es` by
    (irule compile_extract32_sim_mem >> simp[] >> metis_tac[]) >>
  simp[] >> drule extract32_body_result_type >> strip_tac >> gvs[] >>
  `is_word_type (BaseT bt)` by
    (Cases_on `bt` >> gvs[extract32_result_base_ok_def, expr_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[extract32_result_base_ok_def, is_word_type_def] >>
     fs[expr_body_pre_def, well_typed_expr_def, well_formed_type_def, evaluate_type_def]) >>
  irule body_expr_vv_sim_mem_stack_word >> simp[expr_type_def] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) sa` >>
      drule extract32_compile_equations >> strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[eval_expr_type_builtin_value]
QED

Theorem body_type_builtin_extract32_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Extract32) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Extract32) typ es)
Proof
  rpt strip_tac >>
  Cases_on `?src off m k. es = [src; off] /\
              expr_type src = BaseT (BytesT (Dynamic m)) /\
              expr_type off = BaseT (UintT k)`
  >- (gvs[] >> irule body_type_builtin_extract32_ready_mem_case >>
      gvs[] >> metis_tac[]) >>
  irule body_type_builtin_extract32_other_mem_case >> simp[] >> metis_tac[]
QED
