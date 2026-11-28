(* Reachability of calls in checked single-file bodies. *)
Theory bodyCallLiveness
Ancestors
  linkedBodyLoopCalls constSubstMods vyperTypeContract
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperTypeContractSoundness
  vyperTypeContractGetter vyperTypeContractStaticMaps vyperInterpreter
  vyperTypeContractModes vyperTypeCallStackSoundness vyperReadOnlyEval
  bodyFullPreds constSubstCorrect list option

Theorem singleton_decl_calls_live:
  MEM (FunctionDecl vis mut nr raw name args ds ret ss) tops /\
  (vis = External \/ vis = Deploy \/
   MEM (NONE,name) (linked_live_functions [(NONE,tops)] [])) ==>
  EVERY (\k. MEM k (linked_live_functions [(NONE,tops)] []))
    (function_int_calls ds ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qsuff_tac `MEM (NONE,name) (linked_live_functions [(NONE,tops)] [])`
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      `call_edge_rel (contract_call_edges [(NONE:num option,tops)]) (NONE,name) k` by
        (rewrite_tac[call_edge_rel_def] >>
         irule contract_call_edges_function >>
         qexistsl [`args`, `ss`, `ds`, `mut`, `nr`, `raw`, `ret`, `tops`, `vis`] >>
         simp[]) >>
      qpat_x_assum `MEM (NONE,name) (linked_live_functions _ _)` mp_tac >>
      PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def,
                        LET_THM] >> BETA_TAC >> strip_tac >>
      irule (CONJUNCT2 call_closure_from_roots) >>
      qexists_tac `(NONE:num option,name)` >> asm_rewrite_tac[]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >>
  PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def,
                    LET_THM] >> BETA_TAC >>
  irule (CONJUNCT1 call_closure_from_roots) >>
  simp[linked_main_roots_def, linked_export_roots_def, contract_keys_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  TRY (disj1_tac >>
       qexists_tac `FunctionDecl External mut nr raw name args ds ret ss` >>
       simp[external_name_keys_toplevel_def] >> NO_TAC) >>
  disj2_tac >>
  qexists_tac `FunctionDecl Deploy mut nr raw name args ds ret ss` >> simp[]
QED

Theorem singleton_external_body_calls_live:
  lookup_function NONE name External tops = SOME (mut,nr,args,ds,ret,ss) ==>
  EVERY (\k. MEM k (linked_live_functions [(NONE,tops)] []))
    (int_calls_stmts ss)
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (drule singleton_decl_calls_live >>
      simp[function_int_calls_def, EVERY_APPEND]) >>
  drule_all selected_public_getter_body_int_calls_empty >> simp[]
QED

Theorem singleton_deploy_body_calls_live:
  lookup_function NONE name Deploy tops = SOME (mut,nr,args,ds,ret,ss) ==>
  EVERY (\k. MEM k (linked_live_functions [(NONE,tops)] []))
    (int_calls_stmts ss)
Proof
  strip_tac >> drule lookup_function_Deploy_SOME_cases >> strip_tac
  >- gvs[int_calls_stmt_def] >>
  drule singleton_decl_calls_live >>
  simp[function_int_calls_def, EVERY_APPEND]
QED

Theorem singleton_callable_calls_live:
  lookup_callable_function in_deploy name tops = SOME (mut,nr,args,ds,ret,ss) /\
  MEM (NONE,name) (linked_live_functions [(NONE,tops)] []) ==>
  EVERY (\k. MEM k (linked_live_functions [(NONE,tops)] []))
    (function_int_calls ds ss)
Proof
  strip_tac >> drule lookup_callable_function_SOME_decompose >> strip_tac
  >- simp[function_int_calls_def, int_calls_stmt_def, int_calls_expr_def] >>
  drule singleton_decl_calls_live >> simp[]
QED

Theorem checked_singleton_subst_int_calls:
  check_contract mode layouts addr [(NONE,tops)] = SOME art ==>
  (!e. int_calls_expr (subst_consts_expr (module_consts_env tops []) e) =
       int_calls_expr e) /\
  (!ss. int_calls_stmts (subst_consts_stmts (module_consts_env tops []) ss) =
        int_calls_stmts ss)
Proof
  strip_tac >> drule checked_subst_consts_int_calls_mods >>
  simp[consts_env_mods_singleton, subst_consts_mods_singleton]
QED

Theorem callable_compiled_calls_live:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  lookup_callable_function in_deploy name tops = SOME (mut,nr,args,ds,ret,ss) /\
  MEM (NONE,name) (linked_live_functions [(NONE,tops)] []) ==>
  EVERY (\k. MEM k (linked_live_functions [(NONE,tops)] []))
    (int_calls_stmts (subst_consts_stmts (module_consts_env tops []) ss)) /\
  !n. EVERY (\k. MEM k (linked_live_functions [(NONE,tops)] []))
    (int_calls_exprs
      (DROP n (subst_consts_exprs (module_consts_env tops []) ds)))
Proof
  strip_tac >> drule_all singleton_callable_calls_live >>
  simp[function_int_calls_def, EVERY_APPEND] >> strip_tac >>
  drule_then strip_assume_tac checked_singleton_subst_int_calls >>
  simp[int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP,
       subst_consts_exprs_map, GSYM MAP_DROP, combinTheory.o_DEF] >>
  fs[int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP] >>
  gen_tac >> qspecl_then [`n`, `ds`] mp_tac TAKE_DROP >>
  disch_then (fn th => qpat_x_assum `EVERY _ ds` (mp_tac o ONCE_REWRITE_RULE [GSYM th])) >>
  simp[EVERY_APPEND]
QED

Theorem body_const_cells_agree_runtime_check:
  body_const_cells_agree mods cx env es ==>
  IS_SOME (check_contract F cx.layouts cx.txn.target mods)
Proof
  simp[body_const_cells_agree_def, IS_SOME_EXISTS] >> strip_tac >>
  Cases_on `cx.in_deploy` >> gvs[] >>
  drule_then ACCEPT_TAC check_contract_deploy_implies_runtime
QED
