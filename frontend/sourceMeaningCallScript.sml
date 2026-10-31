Theory sourceMeaningCall
Ancestors
  sourceMeaningCallDefs sourceMeaningProgram sourceMeaningProgramDefs sourceMeaningStmt
  sourceMeaningStmtDefs sourceMeaningDefs sourceMeaningValue sourceMeaningRuntime sourceModuleDecl
  sourceModuleDefs sourceTypeDefs sourceSyntax vyperInterpreter vyperState
  vyperContext vyperAST vyperValue finite_map alist list rich_list pair option

(* A transport relation, NOT a source meaning definition. It records uniform
   evaluation at every matching context and state, hence covers defaults staged
   before the argument scope is installed as well as body execution afterwards. *)
Definition source_meaning_decl_code_def:
  source_meaning_decl_code tenv
    (SDM_Function fv mut nr raw name args dms ret bms) tl =
      (?ds ss. tl = FunctionDecl fv mut nr raw name args ds ret ss /\
        (!cx. get_tenv cx = tenv ==>
          LIST_REL (\m e. eval_expr cx e =
            source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) dms ds /\
          eval_stmts cx ss = source_meaning_execute cx bms)) /\
  source_meaning_decl_code tenv (SDM_Constant name ty lit) tl =
      (?e. tl = VariableDecl Private (Constant e) name ty NONE /\
        (!cx. get_tenv cx = tenv ==> eval_expr cx e = return (Value (evaluate_literal lit)))) /\
  source_meaning_decl_code tenv (SDM_Aggregate name ty sv) tl =
      (?e v. tl = VariableDecl Private (Constant e) name ty NONE /\
        source_meaning_value tenv ty sv = SOME v /\
        (!cx. get_tenv cx = tenv ==> eval_expr cx e = return (Value v)))
End

Theorem source_meaning_defaults_transport:
  !ms es. LIST_REL (\m e. eval_expr cx e =
    source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) ms es ==>
  evaluate_defaults cx am es = source_meaning_defaults cx am ms
Proof
  Induct >> Cases_on `es` >> simp[source_meaning_defaults_def,
    evaluate_defaults_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `source_meaning_defaults cx am ms` >> simp[]
QED

Theorem source_meaning_defaults_drop:
  LIST_REL (\m e. eval_expr cx e =
    source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) ms es ==>
  evaluate_defaults cx am (DROP n es) = source_meaning_defaults cx am (DROP n ms)
Proof
  strip_tac >> irule source_meaning_defaults_transport >>
  irule EVERY2_DROP >> simp[]
QED

Theorem source_meaning_globals_transport:
  !ms ts. LIST_REL (source_meaning_decl_code (get_tenv cx)) ms ts ==>
  !acc. constants_env cx am addr src ts acc =
    source_meaning_globals (get_tenv cx) ms acc
Proof
  Induct >> Cases_on `ts` >>
  simp[constants_env_def, source_meaning_globals_def] >>
  gen_tac >> strip_tac >> rename1 `source_meaning_decl_code _ m tl` >>
  Cases_on `m` >> gvs[source_meaning_decl_code_def] >> gen_tac >>
  simp[constants_env_def, source_meaning_globals_def, bind_def,
       read_result_def, return_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem source_meaning_set_current_tenv:
  get_tenv (set_current_module cx src) = get_tenv cx
Proof
  simp[set_current_module_def, get_tenv_def]
QED

Theorem source_meaning_install_transport:
  LIST_REL (source_meaning_decl_code (get_tenv cx)) meanings ts ==>
  evaluate_all_constants cx am cx.txn.target [(NONE,ts)] =
    source_meaning_install cx am meanings
Proof
  strip_tac >>
  `LIST_REL (source_meaning_decl_code (get_tenv (set_current_module cx NONE)))
    meanings ts` by simp[source_meaning_set_current_tenv] >>
  drule source_meaning_globals_transport >>
  disch_then (qspecl_then [`NONE`,`am`,`cx.txn.target`,`FEMPTY`] mp_tac) >>
  simp[source_meaning_set_current_tenv] >> strip_tac >>
  simp[evaluate_all_constants_def, constants_order_def,
    evaluate_module_constants_def, source_meaning_install_def] >>
  Cases_on `source_meaning_globals (get_tenv cx) meanings FEMPTY` >> simp[]
QED

Theorem source_meaning_lookup_transport:
  !ms ts. LIST_REL (source_meaning_decl_code tenv) ms ts ==>
  !name vis. OPTREL
    (\(mut,nr,args,dms,ret,bms) (mut',nr',args',ds,ret',ss).
      mut = mut' /\ nr = nr' /\ args = args' /\ ret = ret' /\
      !cx. get_tenv cx = tenv ==>
        LIST_REL (\m e. eval_expr cx e =
          source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) dms ds /\
        eval_stmts cx ss = source_meaning_execute cx bms)
    (source_meaning_lookup name vis ms) (lookup_function NONE name vis ts)
Proof
  Induct >> Cases_on `ts` >> simp[]
  >- (rpt gen_tac >> Cases_on `vis` >>
      simp[OPTREL_def, source_meaning_lookup_def, lookup_function_def,
        source_meaning_execute_def, source_meaning_run_def, Once evaluate_def]) >>
  gen_tac >> strip_tac >> rename1 `source_meaning_decl_code _ m tl` >>
  Cases_on `m` >> gvs[source_meaning_decl_code_def] >> rpt gen_tac >>
  simp[source_meaning_lookup_def, lookup_function_def] >>
  TRY (IF_CASES_TAC >> simp[]) >>
  Cases_on `vis` >> simp[lookup_function_def]
QED

Theorem source_meaning_result_eta:
  (\(r,a,q). (r,a,q)) result = result
Proof
  PairCases_on `result` >> simp[]
QED

(* Full call protocol: argument arity/default suffix, runtime parameter binding,
   global constant installation for deployment, locks/value transfer, source
   body, return casting, rollback and requests. No bytecode claim is made. *)
Theorem source_meaning_invoke_transport:
  LIST_REL (source_meaning_decl_code (get_tenv cx)) meanings ts /\
  LIST_REL (\m e. eval_expr cx e =
    source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) dms ds /\
  eval_stmts cx ss = source_meaning_execute cx bms ==>
  call_external_function orc am cx nr mut ts [(NONE,ts)] args ds vals ss ret =
    source_meaning_invoke orc am cx meanings nr mut [(NONE,ts)] args dms vals bms ret
Proof
  strip_tac >> drule LIST_REL_LENGTH >> strip_tac >>
  drule source_meaning_defaults_drop >> strip_tac >>
  drule source_meaning_install_transport >> strip_tac >>
  fs[call_external_function_def, source_meaning_invoke_def, source_meaning_result_eta]
QED
