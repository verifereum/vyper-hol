Theory sourceMeaningExample
Ancestors
  sourceMeaningExampleDefs sourceMeaningProgram sourceMeaningProgramDefs
  sourceMeaningStmt sourceMeaningStmtDefs sourceMeaningDefs sourceMeaningConst
  sourceModuleDecl sourceModuleEnv sourceModuleDefs sourceModuleStmt sourceSyntax
  sourceResolveModules sourceResolve sourceExprDefs sourceConstAST sourceConstAnnotation
  sourceConstEnv sourceConstEval sourceConstValue vyperInterpreter vyperTypeSystem
  vyperState vyperContext vyperAST vyperValue finite_map alist list
Libs
  intLib wordsLib

Theorem source_meaning_example_flag:
  source_meaning_source source_meaning_example_ytypes
    source_meaning_example_yctx.sm_scopes source_meaning_example_yctx.sm_table
    source_meaning_example_yctx.sm_constants (BaseT BoolT) (SX_Name "flag")
    (SM_Name (BaseT BoolT) ["main";"f";"flag"])
Proof
  irule sourceMeaningDefsTheory.name >> simp[source_expr_path_def] >>
  rewrite_tac [source_meaning_example_yctx_fields, source_meaning_example_fctx_fields,
    source_meaning_example_ctx_fields] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_meaning_example_names:
  !ty name path.
    ALOOKUP source_meaning_example_ytypes path = SOME ty /\
    source_resolve_name source_meaning_example_yctx.sm_scopes
      source_meaning_example_yctx.sm_table [name] = SOME (path,SR_Dynamic) ==>
    source_meaning_source source_meaning_example_ytypes
      source_meaning_example_yctx.sm_scopes source_meaning_example_yctx.sm_table
      source_meaning_example_yctx.sm_constants ty (SX_Name name) (SM_Name ty path)
Proof
  rpt strip_tac >> irule sourceMeaningDefsTheory.name >> simp[source_expr_path_def] >>
  simp[source_meaning_stage_def, source_resolve_candidate_def,
    source_constant_candidate_def, source_resolve_expr_def,
    source_resolve_atom_def, source_meaning_const_def]
QED

Theorem source_meaning_example_N:
  source_meaning_source source_meaning_example_ytypes
    source_meaning_example_yctx.sm_scopes source_meaning_example_yctx.sm_table
    source_meaning_example_yctx.sm_constants (BaseT (UintT 256)) (SX_Name "N")
    (SM_Literal (BaseT (UintT 256)) (IntL 3)) /\
  source_meaning_source source_meaning_example_types
    source_meaning_example_fctx.sm_scopes source_meaning_example_fctx.sm_table
    source_meaning_example_fctx.sm_constants (BaseT (UintT 256)) (SX_Name "N")
    (SM_Literal (BaseT (UintT 256)) (IntL 3))
Proof
  conj_tac >> irule sourceMeaningDefsTheory.constant >> qexists_tac `SCV_Int 3` >>
  simp[source_const_value_literal_def, source_meaning_stage_def] >>
  qexists_tac `SCE_Name ["main";"N"]` >> conj_tac >>
  rewrite_tac [source_meaning_example_yctx_fields, source_meaning_example_fctx_fields,
    source_meaning_example_ctx_fields] >> EVAL_TAC
QED

Theorem source_meaning_example_add:
  source_meaning_source source_meaning_example_ytypes
    source_meaning_example_yctx.sm_scopes source_meaning_example_yctx.sm_table
    source_meaning_example_yctx.sm_constants (BaseT (UintT 256))
    (SX_Binary SCB_Add (SX_Name "x") (SX_Name "N"))
    (SM_Binary (BaseT (UintT 256)) SCB_Add
      (SM_Name (BaseT (UintT 256)) ["main";"f";"x"])
      (SM_Literal (BaseT (UintT 256)) (IntL 3)))
Proof
  irule sourceMeaningDefsTheory.binary >> simp[] >> rpt conj_tac
  >- (EVAL_TAC >> simp[] >> EVAL_TAC)
  >- (rewrite_tac [source_meaning_example_yctx_fields, source_meaning_example_fctx_fields,
        source_meaning_example_ctx_fields] >> EVAL_TAC >> simp[] >> EVAL_TAC)
  >- (irule source_meaning_example_names >> EVAL_TAC) >>
  simp[source_meaning_example_N]
QED

Theorem source_meaning_example_assignment_list:
  source_meaning_source source_meaning_example_ytypes
    source_meaning_example_yctx.sm_scopes source_meaning_example_yctx.sm_table
    source_meaning_example_yctx.sm_constants (BaseT (UintT 256)) e em ==>
  source_meaning_bodies source_meaning_example_ytypes source_meaning_example_yctx ret
    [SS_Assign (SX_Name "y") e] [SBM_Assign "y" em]
    source_meaning_example_ytypes source_meaning_example_yctx
Proof
  strip_tac >> irule sourceMeaningStmtDefsTheory.cons >>
  qexistsl_tac [`source_meaning_example_yctx`,`source_meaning_example_ytypes`] >> reverse conj_tac
  >- (irule (SIMP_RULE (srw_ss()) [] (Q.INST
        [`path` |-> `["main";"f";"y"]`, `ty` |-> `BaseT (UintT 256)`]
        (SPEC_ALL sourceMeaningStmtDefsTheory.assign))) >> simp[] >>
      conj_tac >> EVAL_TAC) >>
  irule sourceMeaningStmtDefsTheory.empty
QED

Theorem source_meaning_example_source:
  source_meaning_bodies source_meaning_example_types source_meaning_example_fctx
    (BaseT (UintT 256)) source_meaning_example_body source_meaning_example_terms
    source_meaning_example_ytypes source_meaning_example_yctx
Proof
  simp[source_meaning_example_body_def, source_meaning_example_terms_def] >>
  irule sourceMeaningStmtDefsTheory.cons >>
  qexistsl_tac [`source_meaning_example_yctx`,`source_meaning_example_ytypes`] >> reverse conj_tac
  >- (simp[source_meaning_example_ytypes_context, source_meaning_example_yctx_def] >>
      irule sourceMeaningStmtDefsTheory.declare_local >> rpt conj_tac
      >- EVAL_TAC >- EVAL_TAC >> simp[source_meaning_example_N]) >>
  irule sourceMeaningStmtDefsTheory.cons >>
  qexistsl_tac [`source_meaning_example_yctx`,`source_meaning_example_ytypes`] >> reverse conj_tac
  >- (irule sourceMeaningStmtDefsTheory.branch >> reverse (rpt conj_tac)
      >- simp[source_meaning_example_flag] >>
      qexistsl_tac [`source_meaning_example_yctx`,`source_meaning_example_ytypes`] >>
      irule source_meaning_example_assignment_list >>
      simp[source_meaning_example_add, source_meaning_example_N]) >>
  irule sourceMeaningStmtDefsTheory.cons >>
  qexistsl_tac [`source_meaning_example_yctx`,`source_meaning_example_ytypes`] >> reverse conj_tac
  >- (irule sourceMeaningStmtDefsTheory.return_value >>
      irule source_meaning_example_names >> EVAL_TAC) >>
  irule sourceMeaningStmtDefsTheory.empty
QED

Theorem source_meaning_example_build:
  source_module_statements 12 source_meaning_example_fctx (BaseT (UintT 256))
    source_meaning_example_body = SM_Ok (source_meaning_example_code,source_meaning_example_yctx)
Proof
  EVAL_TAC
QED

Theorem source_meaning_example_execution_transport:
  get_tenv cx = FEMPTY ==>
  !st. eval_stmts cx source_meaning_example_code st =
    source_meaning_execute cx source_meaning_example_terms st
Proof
  strip_tac >>
  assume_tac source_meaning_example_source >> assume_tac source_meaning_example_build >>
  assume_tac source_meaning_example_local_context >>
  `(source_meaning_example_fctx).sm_env.type_defs = FEMPTY` by EVAL_TAC >>
  `get_tenv cx = source_meaning_example_fctx.sm_env.type_defs` by simp[] >>
  drule_all (CONJUNCT2 source_meaning_body_transport) >> simp[source_meaning_execute_def]
QED
