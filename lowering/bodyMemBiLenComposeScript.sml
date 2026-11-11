(* Counted operand/suffix composition for len. *)
Theory bodyMemBiLenCompose
Ancestors
  bodyMemBiLenPath exprSimLen exprSimSource exprSimProps exprSimHypsDefs
  exprSimDefs loweringPosts list fragExec exprSimHyps exprSimWordBuiltins
  exprBopLowering exprLowering exprLoweringProps builtinSimple emitHelper
  compileEnv accountsRelProps valueEncoding venomExecSemantics venomInst
  venomState vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeBuiltins vyperValue vyperTyping vyperStorage builtinProps
  vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap exprSimCopy vyperTypeExprResult vyperTypeExprSoundness
  vyperExprNoControl gasContext gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath exprSimMemDefs exprSimMemUnwrap
  fragGasPathMem

Theorem compile_len_singleton_sim_mem:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_mem ctx func cenv cx ty e es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_sized_type (expr_type e)` by (drule len_pre_args >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> fs[expr_body_pre_def]) >>
  drule post_type_evaluates >> disch_then (qx_choose_then `ptv` assume_tac) >>
  `type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` by
    (irule post_value_type_widens >>
     fs[expr_body_pre_def] >> metis_tac[]) >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  gvs[compile_expr_len] >> pairarg_tac >> gvs[] >>
  rename1 `compile_expr cenv ty e sa = (evv, sm)` >>
  Cases_on `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand evv)
    (case vv_location evv of SOME l => l | NONE => LocMemory) sm` >>
  gvs[as_stack_val_def] >>
  drule_all len_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  rename1 `compile_builtin_len _ _ _ _ _ = (lop, lsb)` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e)` by
    (qpat_assum `env.type_defs = get_tenv cx` (fn th =>
       qpat_assum `type_widens_to env.type_defs _ _`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[len_operand_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`evv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      strip_tac
      >- (gvs[] >>
          rename1 `gas_marked_exec _ _ _ _ marks (INL tv) fe (OK t)` >>
          `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL tv, fe with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`e`,
                    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                    `tv`,`fe with gas_obs := []`] expr_body_pre_runtime_typed) >>
          simp[] >> strip_tac >>
          mp_tac (Q.SPECL [`env`,`ctx`,`func`,`cenv`,`cx`,`e`,`es`,`sa`,`sm`,`lsb`,`s0`,
                    `fe with gas_obs := []`,`tv`,`evv`,`lop`,`tvt`,`t`,`ptv`] len_vv_path_mem) >>
          (impl_tac >- simp[]) >> strip_tac >>
          `!tail. result_array_length cx tv (fe with gas_obs := tail) =
                  (INL n, fe with gas_obs := tail)` by
            (gen_tac >> drule len_ral_gas_obs >>
             disch_then (qspec_then `tail` mp_tac) >> simp[]) >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL (Value (IntV (&n)))`, `fe`, `OK t'`] >>
          conj_tac
          >- (rewrite_tac[len_source] >>
              irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                       |> REWRITE_RULE [APPEND_NIL]) >>
              qexistsl_tac [`fe`,`t`,`tv`] >> simp[] >>
              simp[gas_marked_exec_def, gas_marked_path_def, bind_def, return_def,
                   gas_explicit_def]) >>
          simp[vv_store_bound_stack_word, expr_type_def, is_word_type_def] >>
          metis_tac[]) >>
      Cases_on `res` >- gvs[] >>
      simp[gas_summary_at_def] >>
      rename1 `gas_marked_exec _ _ _ _ marks (INR exn) fe fr` >>
      qexistsl_tac [`INR exn`,`fe`,`fr`] >>
      simp[] >> conj_tac
      >- (rewrite_tac[len_source] >> irule gas_marked_exec_bind_exception >> simp[]) >>
      gvs[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule len_exempt_cert >> simp[]
QED

Theorem compile_len_singleton_forced_sim_mem:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_mem ctx func cenv cx ty e es ==>
    expr_sim_mem ctx func cenv cx ty (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt strip_tac >> irule expr_sim_mem_of_vv_sim_mem >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def] >>
  irule compile_len_singleton_sim_mem >> metis_tac[]
QED
