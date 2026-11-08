(* Coherent singleton-owner variant; the old negative diagnostic is unchanged. *)
Theory immutableDeployEmptyStacked
Ancestors
  immutableDeployEmptySource immutableDeployEmptyDeployment
  bodySim vyperContext vyperTypeCallStackSoundness vyperTypeCallGraph

Definition empty_immutable_stacked_cx_def:
  empty_immutable_stacked_cx = empty_immutable_cx with stk := [(NONE,"__init__")]
End

Theorem empty_immutable_stacked_metadata:
  get_module_code empty_immutable_stacked_cx NONE = SOME empty_immutable_tops /\
  get_tenv empty_immutable_stacked_cx = type_env empty_immutable_tops /\
  current_module empty_immutable_stacked_cx = NONE
Proof
  mp_tac empty_immutable_cx_metadata >>
  simp[empty_immutable_stacked_cx_def, get_module_code_def, get_tenv_def,
       current_module_def]
QED

Theorem empty_immutable_stacked_body_inv:
  body_inv empty_immutable_tops empty_immutable_unit.cu_context
    empty_immutable_ce empty_immutable_stacked_cx
Proof
  mp_tac empty_immutable_body_inv >>
  simp[body_inv_def, empty_immutable_stacked_cx_def, get_module_code_def,
       get_tenv_def]
QED

Theorem empty_immutable_stacked_calls_safe:
  call_evaluation_safe empty_immutable_stacked_cx
    (int_calls_expr empty_immutable_expr)
Proof
  simp[call_evaluation_safe_def, empty_immutable_stacked_cx_def,
       empty_immutable_expr_def, int_calls_expr_def] >>
  qexists `[]` >>
  EVAL_TAC >> simp[] >>
  conj_tac
  >- (simp[relationTheory.irreflexive_def] >>
      metis_tac[relationTheory.TC_CASES1, vyperTypeCallGraphSoundnessTheory.call_edge_rel_def, listTheory.MEM]) >>
  simp[vyperInterpreterTheory.lookup_function_def] >>
  simp[int_calls_expr_def, function_int_calls_def,
    int_calls_stmt_def]
QED

Theorem empty_immutable_stacked_pre_boundary:
  expr_body_pre empty_immutable_ce empty_immutable_stacked_cx empty_immutable_env
    empty_immutable_expr empty_immutable_es <=>
  expr_sim_inv empty_immutable_ce empty_immutable_stacked_cx empty_immutable_env
    empty_immutable_es
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def,
       empty_immutable_stacked_calls_safe] >>
  `well_typed_expr empty_immutable_env empty_immutable_expr` by (EVAL_TAC >> simp[]) >>
  `byte_widths_expr empty_immutable_expr /\
   alloc_limits_expr empty_immutable_ce empty_immutable_expr` by EVAL_TAC >>
  simp[] >>
  `~expr_has_evm_run empty_immutable_expr /\
   ~supported_expr_exists call_operands_effect_root empty_immutable_expr /\
   int_calls_expr empty_immutable_expr = [] /\
   (!target. ~supported_expr_exists (expr_abi_decode_target_root target)
      empty_immutable_expr)` by (EVAL_TAC >> simp[]) >>
  simp[] >>
  simp[gasContextTheory.cx_tops_def, empty_immutable_stacked_metadata]
QED

Theorem empty_immutable_stacked_env_consistent:
  env_consistent empty_immutable_env empty_immutable_stacked_cx empty_immutable_es
Proof
  simp[vyperTypeInvariantsTheory.env_consistent_def] >>
  conj_tac
  >- (EVAL_TAC >>
      simp[vyperInterpreterTheory.lookup_function_def,
           vyperTypeContractTheory.function_live_def,
           vyperStateTheory.lookup_flag_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE,
      vyperStateTheory.find_var_decl_by_name_def]
QED

Theorem empty_immutable_stacked_state_typed:
  state_well_typed empty_immutable_es /\
  accounts_well_typed empty_immutable_es.accounts /\
  context_well_typed empty_immutable_stacked_cx
Proof
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[]
QED

Theorem empty_immutable_stacked_functions_typed:
  functions_well_typed empty_immutable_stacked_cx
Proof
  rewrite_tac[vyperTypeInvariantsTheory.functions_well_typed_def] >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `get_module_code _ _ = SOME _` mp_tac >>
  simp[empty_immutable_stacked_cx_def, empty_immutable_cx_def,
       get_module_code_def, empty_evaluation_context_def,
       empty_call_txn_def] >> strip_tac >>
  qpat_x_assum `lookup_callable_function _ _ _ = SOME _` mp_tac >>
  simp[vyperInterpreterTheory.lookup_callable_function_def,
       vyperInterpreterTheory.lookup_function_def,
       immutableDeployEmptyFixtureTheory.empty_immutable_tops_def] >>
  strip_tac >> gvs[] >>
  qexists `empty_immutable_env with
    <|type_defs := get_tenv empty_immutable_stacked_cx;
      fn_sigs := fn_sigs; bare_globals := bare_globals;
      bare_global_assignable := bare_global_assignable;
      toplevel_vtypes := toplevel_vtypes; flag_members := flag_members|>` >>
  simp[empty_immutable_env_def, empty_immutable_stacked_cx_def,
       empty_immutable_cx_def, empty_evaluation_context_def, empty_call_txn_def,
       immutableDeployEmptyFixtureTheory.empty_immutable_tops_def,
       vyperTypeSystemTheory.type_stmt_def,
       vyperTypeSystemTheory.well_typed_expr_def] >> EVAL_TAC >> simp[]
QED

Theorem empty_immutable_stacked_sim_inv:
  expr_sim_inv empty_immutable_ce empty_immutable_stacked_cx empty_immutable_env
    empty_immutable_es
Proof
  simp[exprSimHypsDefsTheory.expr_sim_inv_def,
       empty_immutable_stacked_env_consistent,
       empty_immutable_stacked_state_typed,
       empty_immutable_stacked_functions_typed] >>
  simp[empty_immutable_env_def] >>
  conj_tac >- (rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
    EVAL_TAC >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `get_module_code _ _ = SOME _` mp_tac >>
    simp[empty_immutable_stacked_cx_def, empty_immutable_cx_def,
         get_module_code_def, empty_evaluation_context_def, empty_call_txn_def] >>
    strip_tac >> gvs[immutableDeployEmptyFixtureTheory.empty_immutable_tops_def,
                    vyperStateTheory.lookup_flag_def]) >>
  conj_tac >- (simp[empty_immutable_stacked_metadata] >> EVAL_TAC >>
    rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  conj_tac >- simp[empty_immutable_ce_def, compileVyperTheory.build_compile_env_def,
                          empty_immutable_stacked_metadata,
                          compileVyperTheory.build_flag_info_def,
                          compileVyperTheory.allocate_args_def,
                          immutableDeployEmptyFixtureTheory.empty_immutable_tops_def] >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[AllCaseEqs(), vyperStateTheory.find_var_decl_by_name_def]) >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `get_module_code _ _ = SOME _` mp_tac >>
    simp[empty_immutable_stacked_cx_def, empty_immutable_cx_def,
         get_module_code_def, empty_evaluation_context_def, empty_call_txn_def] >>
    strip_tac >> gvs[immutableDeployEmptyFixtureTheory.empty_immutable_tops_def,
                    vyperStateTheory.find_var_decl_by_name_def]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >> EVAL_TAC) >>
  conj_tac >- (rpt strip_tac >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
    EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[wordsTheory.dimword_def, valueEncodingTheory.type_memory_size_def]) >>
  EVAL_TAC >> rpt strip_tac >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
  EVAL_TAC >> simp[compileEnvTheory.regions_disjoint_def,
                   valueEncodingTheory.type_memory_size_def] >>
  gvs[immutableDeployEmptyProbeTheory.empty_struct_evaluated_probe]
QED

Theorem empty_immutable_stacked_body_pre:
  expr_body_pre empty_immutable_ce empty_immutable_stacked_cx empty_immutable_env
    empty_immutable_expr empty_immutable_es
Proof
  simp[empty_immutable_stacked_pre_boundary, empty_immutable_stacked_sim_inv]
QED
