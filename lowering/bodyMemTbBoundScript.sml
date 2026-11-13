(* Memory case of the body induction for max_value, min_value and epsilon:
   a Lit of the bound, no code and no state change. *)
Theory bodyMemTbBound
Ancestors
  bodyMemoryPreds exprSimMemDefs exprSimMemoryValues exprSimMemoryStack
  exprSimAggregates exprSimConvert exprSimHyps gasNormalPrefix gasContext
  fragGasPathMem fragGasMode gasSummary loweringPosts exprLoweringProps exprLowering
  exprSimHypsDefs exprSimDefs valueEncoding vyperTypeSystem vyperContext
  vyperValueOperation vyperValue vyperInterpreter vyperState vyperAST
  compileEnv venomState exprSimProps

(* well_typed_expr gives no operands and a numeric bound type; admissibility
   rules out the TypeError results of evaluate_max_value/min_value. *)
Theorem bound_builtin_eval[local]:
  MEM tb [MaxValue; MinValue; Epsilon] /\
  expr_body_pre cenv cx env (TypeBuiltin ann tb t args) es /\
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann tb t args))
                       (read_result cx)) expr_res_ok es ==>
  args = [] /\ ann = t /\
  ((?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT) /\
  ?v. evaluate_type_builtin cx tb t [] [] = INL v /\
      !s. bind (eval_expr cx (TypeBuiltin ann tb t args)) (read_result cx) s =
          (INL v, s)
Proof
  strip_tac >>
  Cases_on `bind (eval_expr cx (TypeBuiltin ann tb t args)) (read_result cx) es` >>
  rename1 `_ = (res, es')` >>
  `expr_res_ok res` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  qspecl_then [`cx`, `ann`, `tb`, `t`, `args`, `es`, `res`, `es'`] mp_tac
    eval_expr_bound_builtin >>
  impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_rewrite_tac[]) >>
  strip_tac >> gvs[] >>
  `ann = t /\ ((?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
               t = BaseT DecimalT)` by
    (gvs[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
         well_typed_type_builtin_args_def] >>
     Cases_on `ann` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  simp[] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, lift_sum_def,
       type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def, read_result_def] >>
  gvs[return_def, read_result_def]
QED

Theorem bound_builtin_mem_prefix[local]:
  MEM tb [MaxValue; MinValue; Epsilon] /\
  expr_body_pre cenv cx env (TypeBuiltin ann tb t args) es /\
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann tb t args))
                       (read_result cx)) expr_res_ok es /\
  lower_value compile_expr cenv ty (TypeBuiltin ann tb t args) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v ee t'. gas_value_prefix T (ctx,func,cenv,cx) (ty,TypeBuiltin ann tb t args)
        (sa,sb,op) (es,s0) [] (v,ee,t')
Proof
  strip_tac >> drule_all bound_builtin_eval >> strip_tac >> gvs[] >>
  qexistsl_tac [`v`, `es`, `s0`] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
                 mp_tac) >> simp[NoAsms]) >>
  `gas_path_mem ctx func s0 0 (OK s0)` by metis_tac[gas_path_mem_rules] >>
  fs[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def] >>
  gvs[lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def,
      type_bounds_def, type_bits_def, is_signed_type_def] >>
  gvs[evaluate_type_builtin_def, evaluate_max_value_def,
      evaluate_min_value_def] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       eval_operand_def, is_word_type_def, locals_kept_mem] >>
  simp[integerTheory.INT_SUB] >> rw[evaluate_type_def] >>
  (* Keep symbolic signed bounds opaque to word arithmetic conversions. *)
  PURE_REWRITE_TAC
    [typed_val_to_w256_def, val_to_w256_def,
     integer_wordTheory.i2w_0, integer_wordTheory.i2w_pos] >>
  REFL_TAC
QED

Theorem body_type_builtin_bound_mem_case:
  !cx v11 tb typ es.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    body_expr_mem_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_mem ctx func cenv cx ty (TypeBuiltin v11 tb typ es) es'` by
    (irule expr_sim_mem_word_values >> reverse conj_tac
     >- (`!t. is_int_type t ==> is_word_type t` by
           (Cases >> simp[is_word_type_def] >>
            rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def]) >>
         Cases_on `tb` >> gvs[] >>
         gvs[expr_body_pre_def, well_typed_expr_def,
          type_builtin_result_ok_def, well_typed_type_builtin_args_def,
          vyperASTTheory.expr_type_def, is_word_type_def]) >>
     rpt gen_tac >> strip_tac >>
     qexists_tac `[]` >> irule bound_builtin_mem_prefix >> metis_tac[]) >>
  simp[] >> `is_word_type (expr_type (TypeBuiltin v11 tb typ es))` by
    (`!t. is_int_type t ==> is_word_type t` by
        (Cases >> simp[is_word_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def]) >>
      Cases_on `tb` >> gvs[] >>
      gvs[expr_body_pre_def, well_typed_expr_def,
          type_builtin_result_ok_def, well_typed_type_builtin_args_def,
          vyperASTTheory.expr_type_def, is_word_type_def]) >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  simp[] >> rpt conj_tac
  >~ [`eval_expr`] >- metis_tac[eval_expr_type_builtin_value] >>
  gvs[] >> rpt gen_tac >>
  simp[compile_expr_type_builtin_dispatch, Once compile_expr_def] >>
  Cases_on `type_bounds typ` >> simp[]
QED
