(* MethodId's runtime consumer and literal-family assembly. *)
Theory bodyPtrEnvBuiltinsMethodCase
Ancestors bodyPtrEnvBuiltinsMethodRuntime bodyPtrEnvBuiltinsMethodSource
  bodyPtrEnvBuiltinsMethodTyping bodyPtrEnvBuiltinsDynamicLiteral
  bodyPtrEnvBuiltinsMethodShape bodyPtrEnvBuiltinsBoundary
  exprSimHash exprSimSource exprSimHypsDefs exprSimHyps exprSimProps
  exprLowering exprLoweringProps exprSimDefs exprSimWordArgs exprOperandVar
  bodyPtrDefs bodyPtrPreds gasSummaryComposePtr gasSummary fragGasPathPtr
  compileEnv context freshWrites vyperAST vyperValue vyperContext
  vyperInterpreter vyperState venomState finite_map list fragExec

Theorem method_id_runtime_compile:
  method_id_literal e = NONE /\
  compile_expr cenv ty
    (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e]) sa =
    (vv,sb) ==>
  ?arg sm op. lower_value compile_expr cenv (expr_type e) e sa = (arg,sm) /\
    compile_method_id_runtime (expr_type e) arg fixed sm = (op,sb) /\
    vv = (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
      LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory))
Proof
  strip_tac >> gvs[compile_method_id_singleton_runtime] >>
  pairarg_tac >> Cases_on `compile_method_id_runtime (expr_type e) v fixed sm` >>
  Cases_on `fixed` >> gvs[as_stack_val_def, as_ptr_val_def, mk_ptr_def]
QED

Theorem method_id_runtime_sim_ptr:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e]) es /\
  method_id_literal e = NONE /\
  expr_sim_ptr d ctx PG fn cenv cx (expr_type e) e es ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e]) es
Proof
  strip_tac >> drule method_id_operand_pre >> strip_tac >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all method_id_runtime_compile >> strip_tac >> gvs[] >>
  `cs_appends (compile_method_id_runtime (BaseT bty) arg fixed)` by
    simp[cj 5 hash_suffix_appends] >>
  fs[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `arg`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      suspend "summary") >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule method_id_exempt >> simp[]
QED

Resume method_id_runtime_sim_ptr[summary]:
  gvs[gas_summary_ptr_at_marked]
  >- suspend "normal" >>
  Cases_on `res` >- fs[expr_exit_def] >>
  drule method_id_marked_ptr_exception >>
  disch_then (qspec_then `BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))` assume_tac) >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >> simp[] >> gvs[oneline expr_exit_def, AllCaseEqs()]
QED

Resume method_id_runtime_sim_ptr[normal]:
  rpt strip_tac >>
  drule_all method_id_marked_operand_facts >> strip_tac >>
  `!x. arg = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  `sa.cs_next_var <= sm.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[cs_extends_def]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[cs_extends_def]) >>
  drule method_id_runtime_vv_suffix >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `builtin_result cx es_end.accounts
     (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [expr_type e] [v] = INL r` by
    simp[] >>
  drule_all method_id_marked_ptr_normal >> strip_tac >>
  qexistsl_tac [`INL (Value r)`, `es_end`, `G''`, `tn''`, `OK t'`] >>
  simp[] >> strip_tac >> simp[] >>
  Cases_on `fixed` >> gvs[expr_type_def, is_word_type_def, mk_ptr_def]
  >- (irule vv_post_pointer_cong >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[ptr_vv_ok_def, ptr_mem_ok_def, mk_ptr_def]
QED
Finalise method_id_runtime_sim_ptr

Theorem body_method_runtime_ptr_case:
  method_id_literal e = NONE /\ body_expr_ptr_ok cx e ==>
  body_expr_ptr_ok cx (Builtin ann MethodId [e])
Proof
  strip_tac >> irule body_expr_ptr_of_vv >> rpt gen_tac >> strip_tac >>
  drule method_id_builtin_pre_shape >> strip_tac >> gvs[]
  >- (irule (Q.INST [`fixed` |-> `F`] method_id_runtime_sim_ptr |> SRULE []) >>
      simp[] >> (conj_tac >- (qexists_tac `env` >> simp[])) >>
      irule body_expr_ptr_sim >> goal_assum (drule_at Any) >>
      (conj_tac >- (qexists_tac `tops` >> simp[])) >>
      qexists_tac `env` >> drule method_id_operand_pre >> simp[]) >>
  irule (Q.INST [`fixed` |-> `T`] method_id_runtime_sim_ptr |> SRULE []) >>
  simp[] >> (conj_tac >- (qexists_tac `env` >> simp[])) >>
  irule body_expr_ptr_sim >> goal_assum (drule_at Any) >>
  (conj_tac >- (qexists_tac `tops` >> simp[])) >>
  qexists_tac `env` >> drule method_id_operand_pre >> simp[]
QED

Theorem body_method_singleton_ptr_case:
  body_expr_ptr_ok cx e ==> body_expr_ptr_ok cx (Builtin ann MethodId [e])
Proof
  strip_tac >> Cases_on `method_id_literal e`
  >- (irule body_method_runtime_ptr_case >> simp[]) >>
  `?la l. e = Literal la l` by
    (Cases_on `e` >> gvs[method_id_literal_def]) >> gvs[] >>
  irule body_method_literal_ptr_case >> simp[]
QED

Theorem body_method_id_ptr_case:
  (!s'' x t.
     type_check (builtin_args_length_ok MethodId (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ==> body_exprs_ptr_ok cx es) ==>
  body_expr_ptr_ok cx (Builtin ann MethodId es)
Proof
  strip_tac >> irule body_expr_ptr_of_vv >> rpt gen_tac >> strip_tac >>
  drule method_id_builtin_pre_shape >> disch_then (assume_tac o CONJUNCT1) >>
  Cases_on `es` >> gvs[] >>
  `body_exprs_ptr_ok cx [h]` by
    (first_x_assum (qspecl_then [`es'`, `es'`] mp_tac) >>
     simp[builtin_args_length_ok_def, type_check_def, assert_def, return_def]) >>
  `body_expr_ptr_ok cx (Builtin ann MethodId [h])` by
    (irule body_method_singleton_ptr_case >>
     metis_tac[body_exprs_ptr_head]) >>
  irule body_expr_ptr_vv_sim >> goal_assum (drule_at Any) >>
  metis_tac[]
QED
