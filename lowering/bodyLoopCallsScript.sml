(* Preserve the checker's loop call guard when the compiler inlines constants. *)
Theory bodyLoopCalls
Ancestors
  constSubstStmtsPreserve constSubstCorrect constSubst
  vyperTypeContract vyperTypeContractGetter vyperTypeContractStaticMaps
  vyperGetter vyperTypeSystem vyperAST alist list

Theorem checked_function_loop_calls_ok:
  check_contract mode layouts addr mods = SOME artifact /\
  MEM (src,tops) mods /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
  stmts_loop_calls_ok mods ss
Proof
  strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x mods ==> check_module _ _ _ _ _ _ x` drule >>
  simp[check_module_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x tops ==> check_toplevel_decl _ _ _ x` drule >>
  simp[check_toplevel_decl_def]
QED

(* A closed constant in a single module cannot introduce an iterator place. *)
Theorem closed_constant_no_iterator_place[local]:
  !e. constant_expr [(NONE,tops)] e /\ const_local_refs e = [] ==>
      loop_iterator_place e = NONE
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  simp[constant_expr_def, const_local_refs_def, loop_iterator_place_def] >>
  rpt strip_tac >>
  rename1 `constant_expr _ (TopLevelName _ nid)` >>
  PairCases_on `nid` >>
  gvs[constant_expr_def, declared_constant_def, const_local_refs_def]
QED

Theorem subst_iterator_place_access[local]:
  !e p.
    (!id r. ALOOKUP E id = SOME r ==> loop_iterator_place r = NONE) /\
    loop_iterator_place (subst_consts_expr E e) = SOME p ==>
    ?q. loop_iterator_place e = SOME q /\
        !attrs. place_access p attrs = place_access q attrs
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  simp[subst_consts_expr_def, loop_iterator_place_def, AllCaseEqs()] >>
  rpt strip_tac
  >~ [`TopLevelName`]
  >- (rename1 `subst_consts_expr E (TopLevelName ty nid)` >>
      PairCases_on `nid` >> Cases_on `nid0` >>
      gvs[subst_consts_expr_def, loop_iterator_place_def, AllCaseEqs()] >>
      Cases_on `ALOOKUP E nid1` >> gvs[loop_iterator_place_def] >>
      res_tac >> fs[]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[place_access_def] >> metis_tac[]
QED

Theorem callee_writes_ok_same_access[local]:
  place_access p [] = place_access q [] ==>
  callee_writes_ok mods p = callee_writes_ok mods q
Proof
  strip_tac >>
  `callee_write_ok p = callee_write_ok q` by
    (simp[FUN_EQ_THM, callee_write_ok_def, place_contains_def]) >>
  rw[FUN_EQ_THM, callee_writes_ok_def] >>
  qpat_assum `callee_write_ok p = callee_write_ok q` SUBST1_TAC >> simp[]
QED

Theorem subst_consts_loop_calls_ok[local]:
  (!E s.
    (!id r. ALOOKUP E id = SOME r ==>
       loop_iterator_place r = NONE /\ int_calls_expr r = []) /\
    stmt_loop_calls_ok mods s ==>
    stmt_loop_calls_ok mods (subst_consts_stmt E s)) /\
  (!E ss.
    (!id r. ALOOKUP E id = SOME r ==>
       loop_iterator_place r = NONE /\ int_calls_expr r = []) /\
    stmts_loop_calls_ok mods ss ==>
    stmts_loop_calls_ok mods (subst_consts_stmts E ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, stmt_loop_calls_ok_def] >>
  rpt strip_tac >> res_tac >>
  Cases_on `it` >> gvs[subst_consts_iter_def] >>
  Cases_on `loop_iterator_place (subst_consts_expr E e)` >> simp[] >>
  qspecl_then [`e`, `x`] mp_tac subst_iterator_place_access >>
  impl_tac >- metis_tac[] >>
  disch_then (qx_choose_then `p` strip_assume_tac) >> fs[] >>
  `int_calls_stmts (subst_consts_stmts E ss) = int_calls_stmts ss` by
    (irule (cj 2 subst_consts_stmt_int_calls) >> metis_tac[]) >>
  `callee_writes_ok mods x = callee_writes_ok mods p` by
    (irule callee_writes_ok_same_access >> simp[]) >>
  simp[]
QED

Theorem checked_subst_consts_loop_calls_ok:
  check_contract mode layouts addr [(NONE,tops)] = SOME artifact /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  stmts_loop_calls_ok [(NONE,tops)] ss ==>
  stmts_loop_calls_ok [(NONE,tops)] (subst_consts_stmts (module_consts_env tops []) ss)
Proof
  strip_tac >> irule (cj 2 subst_consts_loop_calls_ok) >> simp[] >>
  rpt gen_tac >> disch_tac >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`]
    checked_module_consts_env_replacement) >>
  impl_tac >- simp[] >>
  strip_tac >> conj_tac
  >- (irule closed_constant_no_iterator_place >> simp[] >> qexists_tac `tops` >> simp[])
  >- (irule (cj 1 constant_expr_no_internal_calls) >>
      qexists_tac `[(NONE,tops)]` >> simp[])
QED

Theorem checked_module_loop_calls_ok:
  check_contract mode layouts addr [(NONE,tops)] = SOME artifact ==>
  !vis mut nr raw fn args dflts ret ss.
    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
    stmts_loop_calls_ok [(NONE,tops)] ss
Proof
  rpt strip_tac >>
  drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)
    checked_function_loop_calls_ok >>
  disch_then (drule_at (Pat `check_contract _ _ _ _ = _`)) >> simp[]
QED

Theorem checked_external_body_loop_calls_ok:
  check_contract mode layouts addr [(NONE,tops)] = SOME artifact /\
  lookup_function NONE fn External tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  stmts_loop_calls_ok [(NONE,tops)] ss
Proof
  strip_tac >> drule checked_module_loop_calls_ok >> strip_tac >>
  drule lookup_function_External_cases >> strip_tac
  >- metis_tac[] >>
  Cases_on `decl` >> fs[is_public_getter_decl_def] >>
  Cases_on `v` >> gvs[is_public_getter_decl_def, external_getter_tuple_def,
                      getter_def, AllCaseEqs()] >>
  gvs[stmt_loop_calls_ok_def] >>
  qpat_x_assum `(\(args,ret,exp). _) (build_getter _ _ _ _) = _` mp_tac >>
  pairarg_tac >> strip_tac >> gvs[stmt_loop_calls_ok_def]
QED

Theorem checked_deploy_body_loop_calls_ok:
  check_contract mode layouts addr [(NONE,tops)] = SOME artifact /\
  lookup_function NONE fn Deploy tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  stmts_loop_calls_ok [(NONE,tops)] ss
Proof
  strip_tac >> drule checked_module_loop_calls_ok >> strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >>
  gvs[stmt_loop_calls_ok_def] >> metis_tac[]
QED
