(* Static map presence for the selected runtime-constant default slice. *)
Theory bodyIntCallDefaultSliceGlobalRootsMods
Ancestors
  bodyIntCallDefaultSliceOccurrenceAccessMods
  bodyIntCallDefaultOwnedImmutableLocationMods
  bodyIntCallDefaultSelectedReadsMods
  bodyFullPreds bodyFullPredsMods bodyInvSplit exprSimHypsDefs
  constSubst constSubstMods constSubstCorrect
  vyperTypeContract vyperTypeContractStaticMaps vyperAST vyperContext
  finite_map alist list pair option rich_list

Theorem global_roots_module_const_keys[local]:
  !tops src acc owner vis e id ty slot.
    (owner = src /\ MEM (VariableDecl vis (Constant e) id ty slot) tops) \/
    MEM (owner,id) (MAP FST acc) ==>
    MEM (owner,id) (MAP FST (module_consts_env_mods src tops acc))
Proof
  Induct >> simp[module_consts_env_mods_def] >>
  Cases_on `h` >> simp[module_consts_env_mods_def] >>
  TRY (first_assum ACCEPT_TAC) >>
  rename1 `VariableDecl _ mut _ _ _` >> Cases_on `mut` >>
  simp[module_consts_env_mods_def] >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  simp[MAP_APPEND] >> metis_tac[]
QED

Theorem global_roots_declared_constant_root[local]:
  !mods src id.
    ALL_DISTINCT (MAP FST mods) /\
    declared_constant mods src id ==>
    const_name_root_mods mods (TopLevelName ann (src,id))
Proof
  rpt gen_tac >> strip_tac >>
  fs[declared_constant_def] >>
  drule_all_then assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
  `MEM (NONE,id) (MAP FST (module_consts_env_mods NONE tls []))` by
    (irule global_roots_module_const_keys >> metis_tac[]) >>
  `module_consts_env_mods NONE tls [] =
   MAP (\(k,v). ((NONE,k),v)) (module_consts_env tls [])` by
    (qspecl_then [`tls`,`[]`] mp_tac module_consts_env_mods_singleton >> simp[]) >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, const_name_root_mods_def,
      cx_const_name_mods_def, MEM_MAP, FORALL_PROD, EXISTS_PROD] >>
  goal_assum (drule_at Any)
QED

Theorem runtime_constant_expr_no_pop[local]:
  !mods e. runtime_constant_expr mods e ==>
    ~supported_expr_exists
      (\x. case x of Pop _ _ => T | _ => F) e
Proof
  ho_match_mp_tac runtime_constant_expr_ind >>
  simp[runtime_constant_expr_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.supported_exprs_exists_every,
       supportedExprTraverseTheory.supported_fields_exists_every,
       EVERY_MEM, EXISTS_MEM, MEM_MAP, combinTheory.o_DEF] >>
  metis_tac[whitelistCheckerConstsTheory.constant_expr_runtime_constant]
QED

Theorem intcall_default_slice_no_unallocated_mods:
  contract_inv mods exps ctx cd p /\
  body_const_cells_agree mods p ed mid /\
  exports_ok p.layouts p.txn.target mods exps /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rawfn name args dflts ret ss) tops /\
  MEM (src,name) (linked_live_functions mods exps) /\
  ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts) /\
  EVERY (runtime_constant_expr mods) ds /\
  ~supported_exprs_exists (const_name_root_mods mods) ds ==>
  ~supported_exprs_exists (unallocated_bare_global_root cd ed) ds
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `ds = _` SUBST_ALL_TAC >>
  qpat_x_assum `supported_exprs_exists (unallocated_bare_global_root _ _) _`
    (qx_choosel_then [`e`] strip_assume_tac o
      MATCH_MP default_slice_occurrence_witness) >>
  qpat_x_assum `supported_exprs_exists ($= e) _`
    (strip_assume_tac o
      PURE_REWRITE_RULE [supportedExprTraverseTheory.supported_exprs_exists_every,
                         EXISTS_MEM]) >>
  `runtime_constant_expr mods e'` by
    (qpat_x_assum `EVERY (runtime_constant_expr _) _` mp_tac >>
     simp[EVERY_MEM] >> disch_then irule >> simp[]) >>
  `~supported_expr_exists (\x. case x of Pop _ _ => T | _ => F) e'` by
    (drule runtime_constant_expr_no_pop >> simp[]) >>
  Cases_on `e` >> gvs[unallocated_bare_global_root_def]
  >- (rename1 `TopLevelName ann nsid` >> PairCases_on `nsid` >>
      `supported_exprs_exists ($= (TopLevelName ann (nsid0,nsid1)))
         (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))` by
        (simp[supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
         qexists_tac `e'` >> simp[]) >>
      qpat_x_assum `body_const_cells_agree _ _ _ _`
        (strip_assume_tac o PURE_REWRITE_RULE [body_const_cells_agree_def]) >>
      `(!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
         vyperSubscriptOverlap$accesses_expr r = [])` by
        (rpt gen_tac >> strip_tac >> PairCases_on `key` >>
         qpat_assum `!src id r. ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==>
            declared_constant mods src id /\ constant_expr mods r /\
            vyperSubscriptOverlap$accesses_expr r = [] /\ _`
           (qspecl_then [`key0`,`key1`,`r`] (drule_then (ACCEPT_TAC o cj 3)))) >>
      pop_assum (mk_asm "consts_env_accesses_free") >>
      `declared_constant mods nsid0 nsid1 \/ declared_immutable mods nsid0 nsid1` by
        (irule (cj 1 default_name_occurrence_declared) >>
         qexistsl_tac [`ann`,`e'`] >> simp[])
      >- (drule_then assume_tac check_contract_runtime_namespaces >>
          `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
          drule_all_then assume_tac global_roots_declared_constant_root >>
          qpat_x_assum `~supported_exprs_exists (const_name_root_mods _) _` mp_tac >>
          simp[] >> irule (cj 3 supportedExprTraverseTheory.supported_expr_exists_mono) >>
          qexists_tac `$= (TopLevelName ann (nsid0,nsid1))` >>
          simp[] >> rpt strip_tac >> gvs[])
      >- (`MEM (ReadAcc (StateRef (nsid0,nsid1))) (accesses_exprs dflts)` by
            (irule intcall_default_slice_raw_read_access_mods >>
             qexistsl_tac [`consts_env_mods mods`,`ann`,`n`] >>
             conj_tac
             >- asm "consts_env_accesses_free" ACCEPT_TAC
             >- simp[]) >>
          drule_then assume_tac contract_inv_immutable_section_layout >>
          drule_all intcall_default_owned_immutable_location_mods >> simp[])) >>
  qpat_x_assum `~supported_expr_exists _ e'` mp_tac >> simp[] >>
  irule (cj 1 supportedExprTraverseTheory.supported_expr_exists_mono) >>
  rename1 `supported_expr_exists ($= (Pop ty tgt)) e'` >>
  qexists_tac `$= (Pop ty tgt)` >> simp[] >> rpt strip_tac >> gvs[]
QED
