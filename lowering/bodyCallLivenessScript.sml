(* Reachability of calls in checked bodies. *)
Theory bodyCallLiveness
Ancestors
  linkedBodyLoopCalls constSubstMods vyperTypeContract
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperTypeContractSoundness
  vyperTypeContractGetter vyperTypeContractStaticMaps vyperInterpreter
  vyperTypeContractModes vyperTypeCallStackSoundness vyperReadOnlyEval
  bodyFullPreds constSubstCorrect alist list option rich_list

Theorem linked_decl_calls_live[local]:
  MEM (src,tops) mods /\
  MEM (FunctionDecl vis mut nr raw name args ds ret ss) tops /\
  MEM (src,name) (linked_live_functions mods exps) ==>
  EVERY (\k. MEM k (linked_live_functions mods exps))
    (function_int_calls ds ss)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  `call_edge_rel (contract_call_edges mods) (src,name) k` by
    (rewrite_tac[call_edge_rel_def] >>
     drule_all_then ACCEPT_TAC contract_call_edges_function) >>
  qpat_x_assum `MEM (src,name) (linked_live_functions _ _)` mp_tac >>
  PURE_REWRITE_TAC[linked_live_functions_def, linked_live_functions_from_def,
                   LET_THM] >> BETA_TAC >> strip_tac >>
  irule (CONJUNCT2 call_closure_from_roots) >>
  qexists_tac `(src,name)` >> asm_rewrite_tac[]
QED

Theorem singleton_decl_calls_live:
  MEM (FunctionDecl vis mut nr raw name args ds ret ss) tops /\
  (vis = External \/ vis = Deploy \/
   MEM (NONE,name) (linked_live_functions [(NONE,tops)] [])) ==>
  EVERY (\k. MEM k (linked_live_functions [(NONE,tops)] []))
    (function_int_calls ds ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qsuff_tac `MEM (NONE,name) (linked_live_functions [(NONE,tops)] [])`
  >- (strip_tac >> irule linked_decl_calls_live >>
      qexistsl_tac [`args`,`mut`,`name`,`nr`,`raw`,`ret`,`NONE`,`tops`,`vis`] >>
      simp[]) >>
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

Theorem callable_compiled_calls_live_mods:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  lookup_callable_function in_deploy name tops = SOME (mut,nr,args,ds,ret,ss) /\
  MEM (src,name) (linked_live_functions mods exps) ==>
  EVERY (\k. MEM k (linked_live_functions mods exps))
    (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
  !n. EVERY (\k. MEM k (linked_live_functions mods exps))
    (int_calls_exprs (DROP n (subst_consts_exprs_mods (consts_env_mods mods) ds)))
Proof
  strip_tac >>
  `EVERY (\k. MEM k (linked_live_functions mods exps))
    (function_int_calls ds ss)` by
    (drule lookup_callable_function_SOME_decompose >> strip_tac
     >- simp[function_int_calls_def, int_calls_stmt_def, int_calls_expr_def] >>
     drule_then assume_tac ALOOKUP_MEM >>
     drule_all_then ACCEPT_TAC linked_decl_calls_live) >>
  drule_then strip_assume_tac checked_subst_consts_int_calls_mods >>
  fs[function_int_calls_def, EVERY_APPEND] >>
  `!es. int_calls_exprs (subst_consts_exprs_mods (consts_env_mods mods) es) =
        int_calls_exprs es` by
    (Induct >> simp[subst_consts_expr_mods_def, int_calls_expr_def]) >>
  gen_tac >>
  `EVERY (\k. MEM k (linked_live_functions mods exps))
    (int_calls_exprs (subst_consts_exprs_mods (consts_env_mods mods) ds))` by simp[] >>
  simp_tac bool_ss [int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP] >>
  pop_assum (fn live =>
    MATCH_ACCEPT_TAC (MATCH_MP EVERY_DROP
      (SIMP_RULE bool_ss [int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP] live)))
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
  strip_tac >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`, `exps` |-> `[]`]
    callable_compiled_calls_live_mods) >>
  asm_rewrite_tac[ALOOKUP_def, consts_env_mods_singleton, subst_consts_mods_singleton]
QED

Theorem body_const_cells_agree_runtime_check:
  body_const_cells_agree mods cx env es ==>
  IS_SOME (check_contract F cx.layouts cx.txn.target mods)
Proof
  simp[body_const_cells_agree_def, IS_SOME_EXISTS] >> strip_tac >>
  Cases_on `cx.in_deploy` >> gvs[] >>
  drule_then ACCEPT_TAC check_contract_deploy_implies_runtime
QED
