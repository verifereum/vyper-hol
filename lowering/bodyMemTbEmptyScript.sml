(* Memory case of the body induction for empty(T): of a word type, the
   literal 0 with no code and no state change; of any other type, a fresh
   zeroed buffer (bodyMemTbEmptyMemory). *)
Theory bodyMemTbEmpty
Ancestors
  bodyMemoryPreds bodyMemTbEmptyMemory exprSimMemDefs exprSimMemoryValues
  exprSimMemoryStack exprSimAggregates exprSimConvert exprSimHyps
  gasNormalPrefix gasContext fragGasPathMem fragGasMode gasSummary
  loweringPosts exprLoweringProps exprLowering exprSimHypsDefs exprSimDefs
  exprSimProps valueEncoding vyperTypeSystem vyperContext vyperValue
  vyperInterpreter vyperState vyperAST compileEnv venomState

(* well_typed_expr gives no operands and the result type t; admissibility
   rules out the TypeError of an unknown type. *)
Theorem empty_eval[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Empty t args) es /\
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Empty t args))
                       (read_result cx)) expr_res_ok es ==>
  args = [] /\ ann = t /\
  ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
       !s. bind (eval_expr cx (TypeBuiltin ann Empty t args))
             (read_result cx) s = (INL (default_value tv), s)
Proof
  strip_tac >>
  `args = [] /\ ann = t` by
    gvs[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
  gvs[] >> Cases_on `evaluate_type (get_tenv cx) ann` >> simp[]
  >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
      simp[gas_admissible_def, Once evaluate_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, lift_sum_def, raise_def,
           type_builtin_args_length_ok_def, evaluate_type_builtin_def] >>
      simp[Once evaluate_def, bind_def, return_def, expr_res_ok_def]) >>
  gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, lift_sum_def,
       type_builtin_args_length_ok_def, evaluate_type_builtin_def] >>
  simp[Once evaluate_def, bind_def, return_def, read_result_def]
QED

Theorem empty_word_mem_prefix[local]:
  is_word_type t /\
  expr_body_pre cenv cx env (TypeBuiltin ann Empty t args) es /\
  gas_admissible (bind (eval_expr cx (TypeBuiltin ann Empty t args))
                       (read_result cx)) expr_res_ok es /\
  lower_value compile_expr cenv ty (TypeBuiltin ann Empty t args) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx func cenv cx es s0 /\ alloca_history func s0 /\
  storage_well_formed_on cx es (FST H) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v. gas_value_prefix H T (ctx,func,cenv,cx) (ty,TypeBuiltin ann Empty t args)
        (sa,sb,op) (es,s0) [] (v,es,s0)
Proof
  strip_tac >> drule_all empty_eval >> strip_tac >> gvs[] >>
  qexists_tac `default_value tv` >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
     simp[]) >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
                 mp_tac) >> simp[NoAsms]) >>
  `gas_path_mem ctx func s0 0 (OK s0)` by metis_tac[gas_path_mem_rules] >>
  fs[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def] >>
  gvs[lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       eval_operand_def, locals_kept_mem] >>
  metis_tac[typed_val_to_w256_default_word]
QED

Theorem body_type_builtin_empty_word_mem_case:
  !cx v11 typ es.
    is_word_type typ ==>
    body_expr_mem_ok cx (TypeBuiltin v11 Empty typ es)
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_mem ctx func cenv cx ty (TypeBuiltin v11 Empty typ es) es'` by
    (irule expr_sim_mem_word_values >> reverse conj_tac
     >- gvs[expr_body_pre_def, well_typed_expr_def,
            type_builtin_result_ok_def, vyperASTTheory.expr_type_def] >>
     rpt gen_tac >> strip_tac >>
     drule_all empty_eval >>
     disch_then (strip_assume_tac o CONJUNCT2 o CONJUNCT2) >>
     qexistsl_tac [`[]`, `default_value tv`, `es'`, `s0`] >> conj_tac
     >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> _`
       (qspec_then `H` (fn th =>
         qpat_assum `valid_horizon cx st0 H es'.storage_trace`
           (strip_assume_tac o MATCH_MP th))) >>
     drule_all empty_word_mem_prefix >> strip_tac >>
     gvs[gas_value_prefix_def, gas_marked_exec_def]) >>
  simp[] >> `is_word_type (expr_type (TypeBuiltin v11 Empty typ es))` by
    gvs[expr_body_pre_def, well_typed_expr_def,
         type_builtin_result_ok_def, vyperASTTheory.expr_type_def] >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  simp[] >> rpt conj_tac
  >~ [`eval_expr`] >- metis_tac[eval_expr_type_builtin_value] >>
  rpt gen_tac >>
  simp[compile_expr_type_builtin_dispatch, Once compile_expr_def]
QED

Theorem body_type_builtin_empty_mem_case:
  !cx v11 typ es. body_expr_mem_ok cx (TypeBuiltin v11 Empty typ es)
Proof
  rpt gen_tac >> Cases_on `is_word_type typ`
  >- simp[body_type_builtin_empty_word_mem_case] >>
  simp[body_type_builtin_empty_memory_mem_case]
QED
