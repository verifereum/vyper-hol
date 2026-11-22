(* Constant inlining preserves the loop call guard across module namespaces. *)
Theory linkedBodyLoopCalls
Ancestors
  constSubstMods constSubst constSubstCorrect constSubstStmtsPreserve
  bodyLoopCalls vyperTypeConstantCells vyperTypeContractStaticMaps
  vyperTypeContractContext vyperTypeInitialState vyperInterpreter option
  vyperTypeContract vyperTypeCallGraph vyperTypeSystem vyperContext vyperAST
  alist list finite_map

Triviality fold_const_expr_no_iterator_place:
  !e. loop_iterator_place e = NONE ==>
      loop_iterator_place (fold_const_expr e) = NONE
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  simp[loop_iterator_place_def, fold_const_expr_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `b` >>
  simp[fold_const_builtin_def, loop_iterator_place_def] >>
  Cases_on `fold_const_exprs l` >> simp[loop_iterator_place_def] >>
  rename1 `fold_const_exprs l = arg::args` >>
  Cases_on `args` >> simp[loop_iterator_place_def] >>
  Cases_on `arg` >> simp[loop_iterator_place_def] >>
  rename1 `Literal aty lit` >> Cases_on `lit` >> simp[loop_iterator_place_def]
QED

Triviality subst_qualified_constant_expr:
  (!key r. ALOOKUP E key = SOME r ==> constant_expr mods r) ==>
  (!e. constant_expr mods e ==> constant_expr mods (subst_consts_expr_mods E e)) /\
  (!es. EVERY (constant_expr mods) es ==>
    EVERY (constant_expr mods) (subst_consts_exprs_mods E es)) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    EVERY (constant_expr mods) (MAP SND (subst_consts_fields_mods E fs)))
Proof
  strip_tac >> ho_match_mp_tac const_local_refs_ind >>
  simp[subst_consts_expr_mods_def, constant_expr_def, SF ETA_ss] >>
  rpt strip_tac >> rename1 `TopLevelName _ nid` >> PairCases_on `nid` >>
  simp[subst_consts_expr_mods_def] >>
  Cases_on `ALOOKUP E (nid0,nid1)` >> simp[constant_expr_def] >>
  first_assum (drule_then ACCEPT_TAC)
QED

Triviality evaluated_constant_subst_no_iterator_place:
  !e v.
    (!src id. declared_constant mods src id /\
         IS_SOME (FLOOKUP (get_source_immutables src imms) id) ==>
       IS_SOME (ALOOKUP E (src,id))) /\
    (!key r. ALOOKUP E key = SOME r ==> loop_iterator_place r = NONE) /\
    constant_expr mods e /\ constant_value mods imms e = SOME v ==>
    loop_iterator_place (subst_consts_expr_mods E e) = NONE
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  simp[subst_consts_expr_mods_def, constant_expr_def, loop_iterator_place_def] >>
  rpt strip_tac
  >~ [`TopLevelName`]
  >- (rename1 `TopLevelName _ nid` >> PairCases_on `nid` >>
      gvs[constant_value_def, constant_expr_def, subst_consts_expr_mods_def,
          AllCaseEqs()] >>
      first_x_assum drule >> simp[] >>
      Cases_on `ALOOKUP E (nid0,nid1)` >> simp[] >>
      first_assum (drule_then ACCEPT_TAC)) >>
  gvs[constant_value_def, AllCaseEqs()] >>
  metis_tac[]
QED

Triviality checked_qualified_const_loop_replacements:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP (consts_env_mods mods) key = SOME r ==>
  loop_iterator_place r = NONE /\ int_calls_expr r = []
Proof
  strip_tac >>
  qabbrev_tac `covers = \(E:((num option # string) # expr) list) imms. !src id.
    declared_constant mods src id /\
    IS_SOME (FLOOKUP (get_source_immutables src imms) id) ==>
    IS_SOME (ALOOKUP E (src,id))` >>
  qabbrev_tac `closed = \(E:((num option # string) # expr) list). !key r. ALOOKUP E key = SOME r ==>
    constant_expr mods r /\ loop_iterator_place r = NONE` >>
  `!unused imms src ts acc.
      unused = mods ==> !E out.
      constants_fold_module mods imms src ts acc = SOME out /\
      (!vis e id ty init. MEM (VariableDecl vis (Constant e) id ty init) ts ==>
        constant_expr mods e) /\
      covers E (merge_constant_imms src acc imms) /\ closed E ==>
      covers (module_consts_env_mods src ts E) (merge_constant_imms src out imms) /\
      closed (module_consts_env_mods src ts E)` by
    (ho_match_mp_tac constants_fold_module_ind >>
     simp[constants_fold_module_def, module_consts_env_mods_def, AllCaseEqs()] >>
     rpt (gen_tac ORELSE disch_then strip_assume_tac) >> gvs[]
     >~ [`fold_const_expr (subst_consts_expr_mods _ _)`] >- (
     `constant_expr mods e` by
       (qpat_assum `!vis e id ty init. _ ==> constant_expr mods e`
         (qspecl_then [`v0`, `e`, `id`, `typ`, `imms'`] mp_tac) >> simp[]) >>
     qabbrev_tac `replacement = fold_const_expr (subst_consts_expr_mods E e)` >>
     `constant_expr mods replacement` by
       (simp[Abbr `replacement`] >>
        irule (cj 1 fold_const_expr_constant) >>
        `!key r. ALOOKUP E key = SOME r ==> constant_expr mods r` by
          (fs[Abbr `closed`] >> rpt strip_tac >> first_assum (drule_then (ACCEPT_TAC o cj 1))) >>
        drule subst_qualified_constant_expr >> simp[]) >>
     `loop_iterator_place replacement = NONE` by
       (simp[Abbr `replacement`] >> irule fold_const_expr_no_iterator_place >>
        qspecl_then [`e`,`v`] mp_tac
          (Q.INST [`imms` |-> `merge_constant_imms src acc imms`]
            evaluated_constant_subst_no_iterator_place) >>
        fs[Abbr `covers`, Abbr `closed`] >>
        disch_then irule >> rpt strip_tac >> first_assum (drule_then (ACCEPT_TAC o cj 2))) >>
     `closed (E ++ [((src,id),replacement)])` by
       (fs[Abbr `closed`, ALOOKUP_APPEND] >> rpt gen_tac >>
        Cases_on `ALOOKUP E key'` >> simp[]
        >- (Cases_on `(src,id) = key'` >> simp[] >> strip_tac >> gvs[]) >>
        rpt strip_tac >> gvs[] >>
        qpat_assum `!key r. ALOOKUP E key = SOME r ==> _`
          (drule_then strip_assume_tac) >> simp[]) >>
     `covers (E ++ [((src,id),replacement)])
         (merge_constant_imms src (acc |+ (id,(tv,v))) imms)` by
       (fs[Abbr `covers`] >> rpt strip_tac >>
        rename1 `declared_constant mods target name` >>
        Cases_on `target = src /\ name = id`
        >- (gvs[ALOOKUP_APPEND] >> Cases_on `ALOOKUP E (src,id)` >> simp[]) >>
        `IS_SOME (FLOOKUP (get_source_immutables target
           (merge_constant_imms src acc imms)) name)` by
          (Cases_on `target = src` >>
           gvs[merge_constant_imms_def, get_source_immutables_set_same,
               get_source_immutables_set_other, FLOOKUP_FUNION, FLOOKUP_UPDATE]) >>
        qpat_x_assum `!src id. declared_constant mods _ _ /\ _ ==> _`
          (qspecl_then [`target`, `name`] mp_tac) >> simp[ALOOKUP_APPEND] >>
        Cases_on `ALOOKUP E (target,name)` >> simp[]) >>
     qpat_assum `!E'. _ ==> covers _ _ /\ closed _`
       (qspec_then `E ++ [((src,id),replacement)]` mp_tac) >>
     impl_tac >- (simp[] >> rpt gen_tac >> disch_tac >>
       rename1 `MEM (VariableDecl vis (Constant value) name ty init) ts` >>
       qpat_assum `!vis e id ty init. _ ==> constant_expr mods e`
         (qspecl_then [`vis`, `value`, `name`, `ty`, `init`] mp_tac) >> simp[]) >>
     simp[]) >>
     first_assum (qspec_then `E` mp_tac) >> simp[]) >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  `!rest imms final E.
     constants_fold mods imms rest = SOME final /\
     EVERY (\unit. MEM unit mods) rest /\ covers E imms /\ closed E ==>
     closed (consts_env_mods_acc rest E)` by
    (Induct >- simp[consts_env_mods_acc_def] >>
     Cases_on `h` >> rename1 `(src,ts)` >>
     simp[constants_fold_def, consts_env_mods_acc_def, AllCaseEqs()] >>
     rpt strip_tac >>
     rename1 `constants_fold_module mods imms src ts FEMPTY = SOME accumulated` >>
     `covers E (merge_constant_imms src FEMPTY imms)` by
       (fs[Abbr `covers`, merge_constant_imms_def] >> rpt strip_tac >>
        Cases_on `src' = src` >>
        gvs[get_source_immutables_set_same, get_source_immutables_set_other] >>
        first_x_assum drule_all >> simp[]) >>
     `!vis e id ty init. MEM (VariableDecl vis (Constant e) id ty init) ts ==>
       constant_expr mods e` by
       (rpt strip_tac >>
        `ALOOKUP mods src = SOME ts` by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
        drule_all check_contract_toplevel_decl_MEM_checked >>
        simp[check_toplevel_decl_def]) >>
     qpat_assum `!other base src ts acc. _`
       (qspecl_then [`mods`, `imms`, `src`, `ts`, `FEMPTY`]
         (qspecl_then [`E`, `accumulated`] mp_tac o REWRITE_RULE [])) >>
     impl_tac >- asm_rewrite_tac[] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def, LET_THM, bool_case_eq]) >>
  `?imms final. initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    constants_fold mods imms (constants_order mods) = SOME final` by
    (Cases_on `initial_immutables (type_env_all_modules mods) mods` >>
     fs[contract_constants_ok_def, optionTheory.IS_SOME_EXISTS]) >>
  `covers [] imms` by
    (simp_tac bool_ss [Abbr `covers`, declared_constant_def] >> rpt strip_tac >>
     drule_all checked_initial_immutables_constant_absent >> strip_tac >> fs[]) >>
  `closed (consts_env_mods mods)` by
    (simp[consts_env_mods_def] >>
     qpat_assum `!rest imms final E. _`
       (qspecl_then [`constants_order mods`, `imms`, `final`, `[]`] mp_tac) >>
     simp[EVERY_MEM, MEM_constants_order] >>
     simp[Abbr `closed`]) >>
  fs[Abbr `closed`] >>
  qpat_assum `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> drule_then ACCEPT_TAC (cj 1 constant_expr_no_internal_calls)
QED

Triviality qualified_const_subst_expr_int_calls:
  (!key r. ALOOKUP E key = SOME r ==> int_calls_expr r = []) ==>
  (!e. int_calls_expr (subst_consts_expr_mods E e) = int_calls_expr e) /\
  (!t. int_calls_target (subst_consts_btarget_mods E t) = int_calls_target t) /\
  (!es. int_calls_exprs (subst_consts_exprs_mods E es) = int_calls_exprs es) /\
  (!opt. int_calls_opt (subst_consts_opt_mods E opt) = int_calls_opt opt) /\
  (!fs. int_calls_named_exprs (subst_consts_fields_mods E fs) = int_calls_named_exprs fs)
Proof
  strip_tac >>
  qabbrev_tac `no_calls = \(E:((num option # string) # expr) list).
    !key r. ALOOKUP E key = SOME r ==> int_calls_expr r = []` >>
  `no_calls E` by (simp_tac bool_ss [Abbr `no_calls`] >> first_assum ACCEPT_TAC) >>
  `(!E e. no_calls E ==> int_calls_expr (subst_consts_expr_mods E e) = int_calls_expr e) /\
   (!E t. no_calls E ==> int_calls_target (subst_consts_btarget_mods E t) = int_calls_target t) /\
   (!E es. no_calls E ==> int_calls_exprs (subst_consts_exprs_mods E es) = int_calls_exprs es) /\
   (!E opt. no_calls E ==> int_calls_opt (subst_consts_opt_mods E opt) = int_calls_opt opt) /\
   (!E fs. no_calls E ==>
     int_calls_named_exprs (subst_consts_fields_mods E fs) = int_calls_named_exprs fs)`
    suffices_by (strip_tac >> simp[]) >>
  ho_match_mp_tac subst_consts_expr_mods_ind >>
  rpt strip_tac >> gvs[subst_consts_expr_mods_def, int_calls_expr_def]
  >~ [`Call`] >- (Cases_on `ct` >> gvs[int_calls_expr_def]) >>
  Cases_on `ALOOKUP E' (ns,id)` >> gvs[int_calls_expr_def, Abbr `no_calls`] >>
  first_assum (drule_then ACCEPT_TAC)
QED

Triviality qualified_const_subst_stmts_int_calls:
  (!key r. ALOOKUP E key = SOME r ==> int_calls_expr r = []) ==>
  int_calls_stmts (subst_consts_stmts_mods E ss) = int_calls_stmts ss
Proof
  strip_tac >>
  qabbrev_tac `no_calls = \(E:((num option # string) # expr) list).
    !key r. ALOOKUP E key = SOME r ==> int_calls_expr r = []` >>
  `no_calls E` by (simp_tac bool_ss [Abbr `no_calls`] >> first_assum ACCEPT_TAC) >>
  `(!E t. no_calls E ==>
     int_calls_atarget (subst_consts_target_mods E t) = int_calls_atarget t) /\
   (!E ts. no_calls E ==>
     int_calls_atargets (subst_consts_targets_mods E ts) = int_calls_atargets ts)` by
    (ho_match_mp_tac subst_consts_target_mods_ind >>
     simp[subst_consts_target_mods_def, int_calls_atarget_def] >>
     rpt strip_tac >> gvs[Abbr `no_calls`] >>
     drule qualified_const_subst_expr_int_calls >> simp[]) >>
  `!E es. subst_consts_exprs_mods E es = MAP (subst_consts_expr_mods E) es` by
    (gen_tac >> Induct >> simp[subst_consts_expr_mods_def]) >>
  `!E fs. MAP SND (subst_consts_fields_mods E fs) =
    MAP (subst_consts_expr_mods E) (MAP SND fs)` by
    (gen_tac >> Induct >> simp[pairTheory.FORALL_PROD, subst_consts_expr_mods_def]) >>
  `(!E s. no_calls E ==> int_calls_stmt (subst_consts_stmt_mods E s) = int_calls_stmt s) /\
   (!E ss. no_calls E ==> int_calls_stmts (subst_consts_stmts_mods E ss) = int_calls_stmts ss)`
    suffices_by (strip_tac >> simp[]) >>
  ho_match_mp_tac subst_consts_stmt_mods_ind >>
  simp[subst_consts_stmt_mods_def, int_calls_stmt_def] >>
  rpt strip_tac >> gvs[] >>
  `!key r. ALOOKUP E' key = SOME r ==> int_calls_expr r = []` by
    (fs[Abbr `no_calls`] >> first_assum ACCEPT_TAC) >>
  drule qualified_const_subst_expr_int_calls >> strip_tac >> simp[]
  >~ [`subst_consts_iter_mods`]
  >- (Cases_on `it` >> simp[subst_consts_iter_mods_def, int_calls_iterator_def])
  >~ [`subst_consts_areason_mods`]
  >- (Cases_on `r` >>
      simp[subst_consts_areason_mods_def, int_calls_assert_reason_def] >>
      Cases_on `c` >> simp[subst_consts_error_mods_def, custom_error_exprs_def] >>
      qpat_assum `!E es. subst_consts_exprs_mods E es = _` (fn mapped =>
        qpat_assum `!es. int_calls_exprs (subst_consts_exprs_mods _ es) = _`
          (fn preserved => simp_tac (srw_ss()) [GSYM MAP_APPEND, GSYM mapped, preserved])))
  >~ [`subst_consts_rreason_mods`]
  >- (Cases_on `r` >>
      simp[subst_consts_rreason_mods_def, int_calls_raise_reason_def] >>
      Cases_on `c` >> simp[subst_consts_error_mods_def, custom_error_exprs_def] >>
      qpat_assum `!E es. subst_consts_exprs_mods E es = _` (fn mapped =>
        qpat_assum `!es. int_calls_exprs (subst_consts_exprs_mods _ es) = _`
          (fn preserved => simp_tac (srw_ss()) [GSYM MAP_APPEND, GSYM mapped, preserved]))) >>
  qpat_assum `!E es. subst_consts_exprs_mods E es = _` (fn mapped =>
    qpat_assum `!es. int_calls_exprs (subst_consts_exprs_mods _ es) = _`
      (fn preserved => simp_tac (srw_ss()) [GSYM mapped, preserved]))
QED

Triviality subst_qualified_iterator_place_access:
  !e p.
    (!key r. ALOOKUP E key = SOME r ==> loop_iterator_place r = NONE) /\
    loop_iterator_place (subst_consts_expr_mods E e) = SOME p ==>
    ?q. loop_iterator_place e = SOME q /\
        !attrs. place_access p attrs = place_access q attrs
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  simp[subst_consts_expr_mods_def, loop_iterator_place_def, AllCaseEqs()] >>
  rpt strip_tac
  >~ [`TopLevelName`]
  >- (rename1 `TopLevelName _ nid` >> PairCases_on `nid` >>
      gvs[subst_consts_expr_mods_def, loop_iterator_place_def, AllCaseEqs()] >>
      Cases_on `ALOOKUP E (nid0,nid1)` >> gvs[loop_iterator_place_def] >>
      first_x_assum drule >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[place_access_def]
QED

Theorem checked_subst_consts_loop_calls_ok_mods:
  check_contract mode layouts addr mods = SOME artifact /\
  stmts_loop_calls_ok mods ss ==>
  stmts_loop_calls_ok mods (subst_consts_stmts_mods (consts_env_mods mods) ss)
Proof
  strip_tac >>
  qabbrev_tac `E = consts_env_mods mods` >>
  `!key r. ALOOKUP E key = SOME r ==>
    loop_iterator_place r = NONE /\ int_calls_expr r = []` by
    (simp_tac bool_ss [Abbr `E`] >> rpt gen_tac >> strip_tac >>
     drule_all checked_qualified_const_loop_replacements >> simp[]) >>
  `(!E s.
    (!key r. ALOOKUP E key = SOME r ==> loop_iterator_place r = NONE /\ int_calls_expr r = []) /\
    stmt_loop_calls_ok mods s ==> stmt_loop_calls_ok mods (subst_consts_stmt_mods E s)) /\
   (!E ss.
    (!key r. ALOOKUP E key = SOME r ==> loop_iterator_place r = NONE /\ int_calls_expr r = []) /\
    stmts_loop_calls_ok mods ss ==> stmts_loop_calls_ok mods (subst_consts_stmts_mods E ss))`
    suffices_by
      (strip_tac >> qpat_assum `!E ss. _ ==> stmts_loop_calls_ok _ _`
        (qspecl_then [`E`, `ss`] mp_tac) >>
       impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  ho_match_mp_tac subst_consts_stmt_mods_ind >>
  simp[subst_consts_stmt_mods_def, stmt_loop_calls_ok_def] >>
  rpt strip_tac >> res_tac >>
  Cases_on `it` >> gvs[subst_consts_iter_mods_def] >>
  Cases_on `loop_iterator_place (subst_consts_expr_mods E' e)` >> simp[] >>
  qspecl_then [`e`, `x`] mp_tac
    (Q.INST [`E` |-> `E'`] subst_qualified_iterator_place_access) >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_assum (drule_then (ACCEPT_TAC o cj 1))) >>
  disch_then (qx_choose_then `p` strip_assume_tac) >> fs[] >>
  `int_calls_stmts (subst_consts_stmts_mods E' ss') = int_calls_stmts ss'` by
    (irule qualified_const_subst_stmts_int_calls >> rpt strip_tac >>
     first_assum (drule_then (ACCEPT_TAC o cj 2))) >>
  `callee_write_ok x = callee_write_ok p` by
    simp[FUN_EQ_THM, callee_write_ok_def, place_contains_def] >>
  `callee_writes_ok mods x = callee_writes_ok mods p` by
    (qpat_assum `callee_write_ok x = callee_write_ok p` (fn same =>
       simp_tac (srw_ss()) [FUN_EQ_THM, callee_writes_ok_def, same])) >>
  simp[]
QED
