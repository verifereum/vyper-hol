(* Qualified compiler inlining follows the checker's ordered constants fold. *)
Theory linkedConstantReplacementValue
Ancestors
  constSubstCorrect constSubstMods constSubst
  vyperTypeContract vyperTypeConstantFold vyperTypeContractStaticMaps
  vyperConstantFoldReplay vyperLinkedConstantFoldTrace
  vyperSubscriptOverlap vyperInterpreter vyperTypeSystem vyperContext vyperAST
  list alist finite_map pair option

Theorem checked_linked_constant_replacement_value:
  check_contract mode layouts addr mods = SOME art /\
  (!s ts. MEM (s,ts) mods ==>
    ?cells. constants_fold_module mods imms s ts FEMPTY = SOME cells /\
      cells SUBMAP get_source_immutables s imms) /\
  ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==>
  ?ts vis init ty slot tv v.
    ALOOKUP mods src = SOME ts /\
    MEM (VariableDecl vis (Constant init) id ty slot) ts /\
    expr_type r = ty /\ constant_expr mods r /\
    (!a. MEM a (vyperSubscriptOverlap$accesses_expr r) ==>
      a = vyperSubscriptOverlap$RiskyAcc) /\
    evaluate_type (type_env_all_modules mods) ty = SOME tv /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
    constant_value mods imms r = SOME v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!env E ref dst.
    (!src id v. declared_constant mods src id /\
      constant_value mods ref (TopLevelName NoneT (src,id)) = SOME v ==>
      ?r. ALOOKUP E (src,id) = SOME r /\
          FLOOKUP env.bare_globals (src,id) = SOME (expr_type r) /\
          FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type (expr_type r)) /\
          constant_expr mods r /\ constant_value mods dst r = SOME v /\
          (!a. MEM a (vyperSubscriptOverlap$accesses_expr r) ==>
            a = vyperSubscriptOverlap$RiskyAcc)) /\
    (!ty a b. constant_expr mods a /\ well_typed_expr env (Subscript ty a b) ==>
       well_typed_expr env a) ==>
    ((!A e. A = E /\ constant_expr mods e /\ well_typed_expr env e ==>
      !v. constant_value mods ref e = SOME v ==>
        expr_type (subst_consts_expr_mods A e) = expr_type e /\
        constant_expr mods (subst_consts_expr_mods A e) /\
        constant_value mods dst (subst_consts_expr_mods A e) = SOME v /\
        (!a. MEM a (vyperSubscriptOverlap$accesses_expr
            (subst_consts_expr_mods A e)) ==> a = vyperSubscriptOverlap$RiskyAcc)) /\
     (!A:((num option # identifier) # expr) list. !bt:base_assignment_target. T) /\
     (!A es. A = E /\ EVERY (constant_expr mods) es /\ well_typed_exprs env es ==>
      !vs. constant_values mods ref es = SOME vs ==>
        LENGTH (subst_consts_exprs_mods A es) = LENGTH es /\
        MAP expr_type (subst_consts_exprs_mods A es) = MAP expr_type es /\
        EVERY (constant_expr mods) (subst_consts_exprs_mods A es) /\
        constant_values mods dst (subst_consts_exprs_mods A es) = SOME vs /\
        (!a. MEM a (vyperSubscriptOverlap$accesses_exprs
            (subst_consts_exprs_mods A es)) ==> a = vyperSubscriptOverlap$RiskyAcc)) /\
     (!A:((num option # identifier) # expr) list. !opt:expr option. T) /\
     (!A fs. A = E /\ EVERY (constant_expr mods) (MAP SND fs) /\
        well_typed_named_exprs env fs ==>
      !vs. constant_values mods ref (MAP SND fs) = SOME vs ==>
        MAP FST (subst_consts_fields_mods A fs) = MAP FST fs /\
        EVERY (constant_expr mods) (MAP SND (subst_consts_fields_mods A fs)) /\
        constant_values mods dst (MAP SND (subst_consts_fields_mods A fs)) = SOME vs /\
        (!a. MEM a (vyperSubscriptOverlap$accesses_named_exprs
            (subst_consts_fields_mods A fs)) ==> a = vyperSubscriptOverlap$RiskyAcc)))` by
    (rpt gen_tac >> strip_tac >> ho_match_mp_tac subst_consts_expr_mods_ind >>
     simp[constant_expr_def, subst_consts_expr_mods_def, expr_type_def, SF ETA_ss] >>
     simp[constant_value_def] >>
     simp[vyperSubscriptOverlapTheory.accesses_expr_def] >>
     rpt strip_tac >> gvs[]
     >>~- ([`well_typed_expr _ (TopLevelName _ _)`],
            qpat_assum `!src id v. declared_constant _ _ _ /\ _ ==> _`
              (qspecl_then [`ns`,`id'`,`v`] mp_tac) >>
            impl_tac >- fs[constant_value_def] >>
            disch_then (qx_choose_then `replacement` strip_assume_tac) >>
            qpat_x_assum `well_typed_expr _ (TopLevelName _ _)` mp_tac >>
            simp[well_typed_expr_def, subst_consts_expr_mods_def, expr_type_def] >>
            strip_tac >> fs[])
     >>~- ([`well_typed_expr _ (StructLit _ _ _)`],
           `well_typed_named_exprs env fs` by fs[well_typed_expr_def] >>
           res_tac >> fs[])
     >> suspend "replacement_structure") >>
  suspend "checked_ordered_fold"
QED

Resume checked_linked_constant_replacement_value[replacement_structure]:
  markerLib.RESUME_TAC
  >> FIRST
    [rename1 `well_typed_exprs env (e::es)` >>
       Cases_on `constant_value mods ref e` >>
       Cases_on `constant_values mods ref es` >> gvs[well_typed_expr_def],
     rename1 `well_typed_named_exprs env ((k,e)::fs)` >>
       Cases_on `constant_value mods ref e` >>
       Cases_on `constant_values mods ref (MAP SND fs)` >> gvs[well_typed_expr_def],
     rename1 `well_typed_expr env (Attribute ty e k)` >>
       Cases_on `constant_value mods ref e` >> gvs[well_typed_expr_def],
     rename1 `well_typed_expr env (Builtin ty bt es)` >>
       Cases_on `constant_values mods ref es` >> gvs[well_typed_expr_def],
     rename1 `well_typed_expr env (TypeBuiltin ty bt target es)` >>
       Cases_on `constant_values mods ref es` >> gvs[well_typed_expr_def],
     rename1 `well_typed_expr env (Subscript ty e ix)` >>
       `well_typed_expr env e` by
         (qpat_assum `!ty a b. _ /\ well_typed_expr _ (Subscript ty a b) ==> _`
           (qspecl_then [`ty`,`e`,`ix`] mp_tac) >> simp[]) >>
       `well_typed_expr env ix` by fs[well_typed_expr_def] >>
       Cases_on `constant_value mods ref e` >>
       Cases_on `constant_value mods ref ix` >> gvs[]] >>
  rpt (qpat_x_assum `well_typed_expr _ _ ==> !v. _`
    (fn th => drule th >> disch_then drule >> strip_tac)) >>
  rpt (qpat_x_assum `well_typed_exprs _ _ ==> !vs. _`
    (fn th => drule th >> disch_then drule >> strip_tac)) >>
  rpt (qpat_x_assum `well_typed_named_exprs _ _ ==> !vs. _`
    (fn th => drule th >> disch_then drule >> strip_tac)) >>
  fs[] >>
  rename1 `MEM a (if risky_builtin bt then [RiskyAcc] else [])` >>
  Cases_on `risky_builtin bt` >> fs[]
QED

Resume checked_linked_constant_replacement_value[checked_ordered_fold]:
  qabbrev_tac `good = \s n e. ?ts vis init ty slot tv v.
    ALOOKUP mods s = SOME ts /\
    MEM (VariableDecl vis (Constant init) n ty slot) ts /\
    expr_type e = ty /\ constant_expr mods e /\
    (!a. MEM a (accesses_expr e) ==> a = RiskyAcc) /\
    evaluate_type (type_env_all_modules mods) ty = SOME tv /\
    FLOOKUP (get_source_immutables s imms) n = SOME (tv,v) /\
    !dst. constant_value mods dst e = SOME v` >>
  qabbrev_tac `closed = \E. !s n e. ALOOKUP E (s,n) = SOME e ==> good s n e` >>
  qabbrev_tac `covers = \ref (E:((num option # identifier) # expr) list). !s n p. declared_constant mods s n /\
    FLOOKUP (get_source_immutables s ref) n = SOME p ==>
    FLOOKUP (get_source_immutables s imms) n = SOME p /\
    ?e. ALOOKUP E (s,n) = SOME e` >>
  qabbrev_tac `prefix_ok = \ref E. covers ref E /\ closed E` >>
  `contract_namespaces_ok F mods` by (drule check_contract_runtime_namespaces >> simp[]) >>
  `!s ts. MEM (s,ts) mods ==> ALOOKUP mods s = SOME ts` by
    (rpt strip_tac >> irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  `!s ts vis init n ty slot.
     ALOOKUP mods s = SOME ts /\ MEM (VariableDecl vis (Constant init) n ty slot) ts ==>
     FLOOKUP art.cta_bare_globals (s,n) = SOME ty /\
     FLOOKUP art.cta_toplevel_vtypes (s,n) = SOME (Type ty)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (drule check_contract_nonsig_maps >> strip_tac >> simp[] >>
         irule build_contract_type_artifact_bare_globals_complete >> metis_tac[])
     >> drule vyperTypeContractStaticMapsTheory.check_contract_bare_global_toplevel_vtype >>
     disch_then drule >> disch_then drule >> simp[]) >>
  `ALOOKUP (constant_context mods).sources (constant_context mods).txn.target = SOME mods` by
    simp[constant_context_def] >>
  `!s ty e ix. constant_expr mods e /\
     well_typed_expr (artifact_env art mods s) (Subscript ty e ix) ==>
     well_typed_expr (artifact_env art mods s) e` by
    (rpt strip_tac >> drule_all constant_subscript_base_well_typed >> simp[]) >>
  qabbrev_tac `permitted = \a. a = RiskyAcc` >>
  `!ty bi es. EVERY permitted (accesses_exprs es) ==>
     EVERY permitted (accesses_expr (fold_const_builtin ty bi es))` by
    (rpt (qpat_x_assum `!x. _` kall_tac) >>
     rpt gen_tac >> strip_tac >>
     `fold_const_builtin ty bi es = Builtin ty bi es \/
      ?lit. fold_const_builtin ty bi es = Literal ty lit` by
       (simp[fold_const_builtin_def] >> rpt (CASE_TAC >> simp[])) >>
     qpat_x_assum `fold_const_builtin _ _ _ = _` SUBST1_TAC >>
     Cases_on `risky_builtin bi` >>
     simp[Abbr `permitted`, vyperSubscriptOverlapTheory.accesses_expr_def]) >>
  `(!e. constant_expr mods e /\ EVERY permitted (accesses_expr e) ==>
        EVERY permitted (accesses_expr (fold_const_expr e))) /\
   (!es. EVERY (constant_expr mods) es /\ EVERY permitted (accesses_exprs es) ==>
         EVERY permitted (accesses_exprs (fold_const_exprs es))) /\
   (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ EVERY permitted (accesses_named_exprs fs) ==>
         EVERY permitted (accesses_named_exprs (fold_const_fields fs)))` by
    (qpat_x_assum `!ty bi es. _ ==> EVERY permitted (accesses_expr (fold_const_builtin ty bi es))`
       (fn th => rpt (qpat_x_assum `!x. _` kall_tac) >> assume_tac th) >>
     ho_match_mp_tac const_local_refs_ind >>
     simp[constant_expr_def, fold_const_expr_def, SF ETA_ss,
          vyperSubscriptOverlapTheory.accesses_expr_def, EVERY_APPEND] >>
     rpt strip_tac >> gvs[] >> first_x_assum irule >> simp[]) >>
  `!ms base s ts acc cells n.
     constants_fold_module ms base s ts acc = SOME cells /\ ~MEM n (const_decl_names ts) ==>
     FLOOKUP cells n = FLOOKUP acc n` by
    (rpt (qpat_x_assum `!x. _` kall_tac) >>
     ho_match_mp_tac constants_fold_module_ind >>
     rw[constants_fold_module_def, const_decl_names_def] >>
     gvs[AllCaseEqs()] >> metis_tac[FLOOKUP_UPDATE]) >>
  `!s s' base acc n n' p.
     FLOOKUP (get_source_immutables s' (merge_constant_imms s (acc |+ (n,p)) base)) n' =
     if s' = s /\ n' = n then SOME p
     else FLOOKUP (get_source_immutables s' (merge_constant_imms s acc base)) n'` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> Cases_on `s' = s` >>
     simp[merge_constant_imms_def, vyperTypeInitialStateTheory.get_source_immutables_set_same,
          vyperTypeInitialStateTheory.get_source_immutables_set_other,
          FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
     Cases_on `n = n'` >> simp[] >> metis_tac[]) >>
  `!s s' base n. FLOOKUP (get_source_immutables s' (merge_constant_imms s FEMPTY base)) n =
                   FLOOKUP (get_source_immutables s' base) n` by
    (rpt gen_tac >> Cases_on `s' = s` >>
     simp[merge_constant_imms_def, vyperTypeInitialStateTheory.get_source_immutables_set_same,
          vyperTypeInitialStateTheory.get_source_immutables_set_other, FLOOKUP_FUNION]) >>
  (* A new cell changes only its qualified key. The old environment takes
     precedence in ALOOKUP, so an old hit remains a valid replacement. *)
  `!s base acc E n p e.
     prefix_ok (merge_constant_imms s acc base) E /\
     FLOOKUP (get_source_immutables s imms) n = SOME p /\ good s n e ==>
     prefix_ok (merge_constant_imms s (acc |+ (n,p)) base) (E ++ [((s,n),e)])` by
    (simp[Abbr `prefix_ok`] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (fs[Abbr `covers`] >> map_every qx_gen_tac [`u`,`k`,`cell`] >> strip_tac >>
         Cases_on `u = s /\ k = n`
         >- (gvs[ALOOKUP_APPEND] >> CASE_TAC >> simp[]) >>
         qpat_x_assum `(if _ then _ else _) = SOME cell` mp_tac >> simp[] >> disch_tac >>
         qpat_x_assum `!s n p. declared_constant _ s n /\ FLOOKUP _ n = SOME p ==> _`
           (qspecl_then [`u`,`k`,`cell`] mp_tac) >>
         simp[] >> strip_tac >> simp[ALOOKUP_APPEND]) >>
     fs[Abbr `closed`] >> map_every qx_gen_tac [`u`,`k`,`replacement`] >> strip_tac >>
     Cases_on `ALOOKUP E (u,k)` >> gvs[ALOOKUP_APPEND]) >>
  (* A successful read has a present cell in the canonical prefix. Its
     replacement denotes the same value because both agree with the installed cell. *)
  `!site ref E dst u n w. prefix_ok ref E /\ declared_constant mods u n /\
     constant_value mods ref (TopLevelName NoneT (u,n)) = SOME w ==>
     ?e. ALOOKUP E (u,n) = SOME e /\
         FLOOKUP (artifact_env art mods site).bare_globals (u,n) = SOME (expr_type e) /\
         FLOOKUP (artifact_env art mods site).toplevel_vtypes (u,n) = SOME (Type (expr_type e)) /\
         constant_expr mods e /\ constant_value mods dst e = SOME w /\
         !a. MEM a (accesses_expr e) ==> permitted a` by
    (map_every qx_gen_tac [`site`,`ref`,`E`,`dst`,`u`,`n`,`w`] >> strip_tac >>
     `?tv. FLOOKUP (get_source_immutables u ref) n = SOME (tv,w)` by
       (qpat_x_assum `constant_value _ _ (TopLevelName _ _) = SOME _` mp_tac >>
        simp[constant_value_def, AllCaseEqs(), FORALL_PROD] >>
        strip_tac >> gvs[] >> metis_tac[PAIR]) >>
     fs[Abbr `prefix_ok`, Abbr `covers`, Abbr `closed`] >>
     qpat_x_assum `!s n p. declared_constant _ s n /\ FLOOKUP _ n = SOME p ==> _`
       (qspecl_then [`u`,`n`,`(tv,w)`] mp_tac) >> simp[] >> strip_tac >>
     rename1 `ALOOKUP E (u,n) = SOME replacement` >>
     `good u n replacement` by (first_x_assum irule >> simp[]) >>
     fs[Abbr `good`] >>
     qpat_assum `!s ts vis init n ty slot. _ ==> FLOOKUP art.cta_bare_globals _ = _ /\ _`
       (fn th => drule_all th) >>
     strip_tac >> simp[artifact_env_def] >>
     qpat_x_assum `FLOOKUP (get_source_immutables u imms) n = SOME (_,v)` mp_tac >> simp[]) >>
  `!s ts vis init n ty slot tv w ref E.
      ALOOKUP mods s = SOME ts /\ MEM (VariableDecl vis (Constant init) n ty slot) ts /\
      evaluate_type (type_env_all_modules mods) ty = SOME tv /\
      FLOOKUP (get_source_immutables s imms) n = SOME (tv,w) /\
      constant_value mods ref init = SOME w /\ prefix_ok ref E ==>
      good s n (fold_const_expr (subst_consts_expr_mods E init))` by
    (map_every qx_gen_tac [`s`,`ts`,`vis`,`init`,`n`,`ty`,`tvslot`,`tv`,`w`,`ref`,`E`] >>
     strip_tac >> drule_all checked_const_decl_typed >> strip_tac >>
     qabbrev_tac `u = subst_consts_expr_mods E init` >>
     `!dst. expr_type u = ty /\ constant_expr mods u /\
            constant_value mods dst u = SOME w /\ EVERY permitted (accesses_expr u)` by
       (qx_gen_tac `dst` >> markerLib.UNABBREV_TAC "u" >> pure_rewrite_tac[EVERY_MEM] >>
        qpat_x_assum `!env E ref dst. (!s n v. _ ==> ?x. _) /\ _ ==> _`
          (qspecl_then [`artifact_env art mods s`,`E`,`ref`,`dst`] mp_tac) >>
        impl_tac
        >- (conj_tac
            >- (rpt strip_tac >>
                qpat_assum `!site ref E dst u n w. prefix_ok ref E /\ _ ==> _`
                  (qspecl_then [`s`,`ref`,`E`,`dst`] (fn th => drule_all th)) >> simp[]) >>
            qpat_assum `!s ty e ix. _ ==> well_typed_expr (artifact_env _ _ s) e`
              (qspec_then `s` ACCEPT_TAC)) >>
        disch_then (qspec_then `E` mp_tac o CONJUNCT1) >>
        disch_then (qspec_then `init` mp_tac) >> simp[]) >>
     qpat_x_assum `!dst. expr_type u = _ /\ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [FORALL_AND_THM]) >>
     `!a. MEM a (accesses_expr (fold_const_expr u)) ==> a = RiskyAcc` by
       (`EVERY permitted (accesses_expr (fold_const_expr u))` by
          (first_x_assum irule >> simp[]) >>
        pop_assum mp_tac >> markerLib.UNABBREV_TAC "permitted" >>
        pure_rewrite_tac[EVERY_MEM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> simp_tac (srw_ss()) []) >>
     `constant_expr mods (fold_const_expr u)` by
       (irule (CONJUNCT1 fold_const_expr_constant) >> first_assum ACCEPT_TAC) >>
     `!dst. constant_value mods dst (fold_const_expr u) = SOME w` by
       (gen_tac >> dep_rewrite.DEP_REWRITE_TAC[fold_const_expr_value] >> simp[]) >>
     markerLib.UNABBREV_TAC "good" >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
     qexistsl [`ts`,`vis`,`init`,`ty`,`tvslot`,`tv`,`w`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
                       (pure_asm_rewrite_tac[fold_const_expr_type] >> REFL_TAC))) >>
  (* Synchronize the folds within a module. Distinct declaration names mean
     that the cell just written can already be read in the final module map. *)
  `!s tops seed cells.
     ALOOKUP mods s = SOME tops /\ cells SUBMAP get_source_immutables s imms ==>
     !tail acc E. constants_fold_module mods seed s tail acc = SOME cells /\
       EVERY (\d. MEM d tops) tail /\ ALL_DISTINCT (const_decl_names tail) /\
       prefix_ok (merge_constant_imms s acc seed) E ==>
       prefix_ok (merge_constant_imms s cells seed) (module_consts_env_mods s tail E)` by
    (map_every qx_gen_tac [`s`,`tops`,`seed`,`cells`] >> strip_tac >>
     Induct >- simp[constants_fold_module_def, module_consts_env_mods_def] >>
     qx_gen_tac `decl` >> Cases_on `decl` >>
     TRY (rename1 `VariableDecl vis mut n ty slot::_` >> Cases_on `mut`) >>
     simp[constants_fold_module_def, module_consts_env_mods_def,
          const_decl_names_def, AllCaseEqs()] >>
     map_every qx_gen_tac [`acc`,`E`] >> strip_tac >>
     TRY (first_x_assum (qspecl_then [`acc`,`E`] mp_tac) >> simp[] >> NO_TAC) >>
     rename1 `evaluate_type (type_env_all_modules mods) ty = SOME tv` >>
     rename1 `constant_value mods (merge_constant_imms s acc seed) init = SOME w` >>
     rename1 `~MEM n (const_decl_names tail)` >>
     `FLOOKUP cells n = SOME (tv,w)` by
       (qpat_assum `!ms seed s ts acc cells n. _ ==> FLOOKUP cells n = FLOOKUP acc n`
          (fn th => drule th) >>
        disch_then (qspec_then `n` mp_tac) >> simp[FLOOKUP_UPDATE]) >>
     `FLOOKUP (get_source_immutables s imms) n = SOME (tv,w)` by
       (drule_all FLOOKUP_SUBMAP >> simp[]) >>
     `good s n (fold_const_expr (subst_consts_expr_mods E init))` by
       (first_x_assum irule >> metis_tac[]) >>
     first_x_assum (qspecl_then
       [`acc |+ (n,(tv,w))`, `E ++ [((s,n),fold_const_expr (subst_consts_expr_mods E init))]`] mp_tac) >>
     simp[] >> disch_then irule >> first_x_assum irule >> simp[]) >>
  (* Replay only uses agreement at cells already present in the prefix. *)
  `!s ts seed E cells. MEM (s,ts) mods /\ prefix_ok seed E /\
     constants_fold_module mods seed s ts FEMPTY = SOME cells ==>
     cells SUBMAP get_source_immutables s imms` by
    (map_every qx_gen_tac [`s`,`ts`,`seed`,`E`,`cells`] >> strip_tac >>
     `ALOOKUP mods s = SOME ts` by (first_x_assum irule >> simp[]) >>
     `constants_fold_module mods imms s ts FEMPTY = SOME cells` by
       (irule constants_fold_module_replay_present >> conj_tac
        >- (rpt strip_tac >> drule_all checked_const_decl_typed >> simp[]) >>
        qexists_tac `seed` >> simp[] >> fs[Abbr `prefix_ok`, Abbr `covers`] >>
        map_every qx_gen_tac [`u`,`k`] >>
        Cases_on `FLOOKUP (get_source_immutables u seed) k` >> simp[] >>
        strip_tac >>
        qpat_x_assum `!s n p. declared_constant _ s n /\ FLOOKUP _ n = SOME p ==> _`
          (fn th => drule_all th) >> simp[]) >>
     qpat_assum `!s ts. MEM (s,ts) mods ==> ?cells. _`
       (fn th => drule th) >> strip_tac >>
     qpat_x_assum `constants_fold_module mods imms s ts FEMPTY = SOME cells` mp_tac >>
     simp[] >> disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `!rest seed last E. constants_fold mods seed rest = SOME last /\
     EVERY (\m. MEM m mods) rest /\ prefix_ok seed E ==>
     prefix_ok last (consts_env_mods_acc rest E)` by
    (Induct >- simp[constants_fold_def, consts_env_mods_acc_def] >>
     qx_gen_tac `entry` >> PairCases_on `entry` >>
     simp[constants_fold_def, consts_env_mods_acc_def, AllCaseEqs()] >>
     map_every qx_gen_tac [`seed`,`last`,`E`] >> strip_tac >>
     rename1 `constants_fold_module mods seed s ts FEMPTY = SOME cells` >>
     `ALOOKUP mods s = SOME ts` by (first_x_assum irule >> simp[]) >>
     `ALL_DISTINCT (const_decl_names ts)` by
       (drule_all checked_const_decl_names_distinct >> simp[]) >>
     `cells SUBMAP get_source_immutables s imms` by
       (first_x_assum irule >> metis_tac[]) >>
     `prefix_ok (merge_constant_imms s FEMPTY seed) E` by
       fs[Abbr `prefix_ok`, Abbr `covers`] >>
     `prefix_ok (merge_constant_imms s cells seed) (module_consts_env_mods s ts E)` by
       (first_x_assum irule >> simp[] >> conj_tac
        >- (qexists_tac `FEMPTY` >> simp[]) >>
        simp[EVERY_MEM]) >>
     first_x_assum (qspecl_then
       [`merge_constant_imms s cells seed`,`last`,`module_consts_env_mods s ts E`] mp_tac) >> simp[]) >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = SOME _`
       (fn th => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac th) >>
     gvs[check_contract_def]) >>
  `?ini last. initial_immutables (type_env_all_modules mods) mods = SOME ini /\
     constants_fold mods ini (constants_order mods) = SOME last` by
    (qpat_x_assum `contract_constants_ok mods` mp_tac >>
     simp[contract_constants_ok_def, IS_SOME_EXISTS] >> CASE_TAC >> simp[]) >>
  `prefix_ok ini []` by
    (map_every markerLib.UNABBREV_TAC ["prefix_ok","covers","closed"] >>
     CONV_TAC (DEPTH_CONV BETA_CONV) >> reverse conj_tac >- simp[] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `declared_constant _ _ _`
       (strip_assume_tac o REWRITE_RULE[declared_constant_def]) >>
     drule_all vyperTypeConstantCellsTheory.checked_initial_immutables_constant_absent >> simp[]) >>
  `prefix_ok last (consts_env_mods mods)` by
    (qpat_assum `!rest seed last E. constants_fold mods seed rest = SOME last /\ _ ==> _`
       (qspecl_then [`constants_order mods`,`ini`,`last`,`[]`] mp_tac) >>
     simp[consts_env_mods_def, consts_env_modules_order_eq, EVERY_MEM, MEM_constants_order]) >>
  `good src id r` by fs[Abbr `prefix_ok`, Abbr `closed`] >>
  qpat_x_assum `good src id r` mp_tac >> markerLib.UNABBREV_TAC "good" >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  qexistsl [`ts`,`vis`,`init`,`ty`,`slot`,`tv`,`v`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (qspec_then `imms` ACCEPT_TAC))
QED
Finalise checked_linked_constant_replacement_value
