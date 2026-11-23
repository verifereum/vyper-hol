(* Qualified constant substitutions retain the checked initializer type. *)
Theory linkedConstantReplacementTyping
Ancestors
  linkedBodyLoopCalls constSubstCorrect constSubstMods constSubst
  vyperTypeContract vyperTypeConstantFold vyperTypeContractStaticMaps
  vyperConstantFoldReplay vyperLinkedConstantFoldTrace
  vyperTypeSystem vyperContext vyperAST list alist finite_map pair option

Theorem checked_linked_constant_replacements_typed:
  check_contract mode layouts addr mods = SOME art /\
  EVERY (no_neg_exp_expr o SND) (consts_env_mods mods) /\
  ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==>
  !current_src. well_typed_expr (artifact_env art mods current_src) r
Proof
  strip_tac >>
  qabbrev_tac `good = \(key,r).
    constant_expr mods r /\ (!dst. well_typed_expr (artifact_env art mods dst) r) /\
    (!s ann. well_typed_expr (artifact_env art mods s) (TopLevelName ann key) ==>
             expr_type r = ann)` >>
  `!E key e. EVERY good E /\ ALOOKUP E key = SOME e ==>
    constant_expr mods e /\ (!dst. well_typed_expr (artifact_env art mods dst) e) /\
    (!s ann. well_typed_expr (artifact_env art mods s) (TopLevelName ann key) ==>
             expr_type e = ann)` by
    (rpt gen_tac >> strip_tac >> drule_then assume_tac ALOOKUP_MEM >>
     fs[EVERY_MEM] >> first_x_assum (drule_then mp_tac) >>
     simp[Abbr `good`] >> rpt strip_tac >> first_assum irule >> simp[]) >>
  pop_assum (mk_asm "entry") >>
  `!E e n.
    (int_literal_value e = SOME n ==>
     int_literal_value (subst_consts_expr_mods E e) = SOME n) /\
    (nonneg_int_literal e ==> nonneg_int_literal (subst_consts_expr_mods E e))` by
    (rpt gen_tac >> Cases_on `e` >>
     simp[int_literal_value_def, nonneg_int_literal_def, subst_consts_expr_mods_def] >>
     Cases_on `l` >> simp[subst_consts_expr_mods_def]) >>
  pop_assum (mk_asm "literal") >>
  `!E ty ix rt. expr_type (subst_consts_expr_mods E ix) = expr_type ix /\
    subscript_type_ok ty ix rt ==> subscript_type_ok ty (subst_consts_expr_mods E ix) rt` by
    (rpt gen_tac >> Cases_on `ty` >> simp[subscript_type_ok_def] >>
     Cases_on `ix` >> simp[subscript_type_ok_def, subst_consts_expr_mods_def] >>
     Cases_on `l` >> simp[subst_consts_expr_mods_def]) >>
  pop_assum (mk_asm "index") >>
  `!E ty bi es.
    no_neg_exp_expr (Builtin ty bi (subst_consts_exprs_mods E es)) /\
    MAP expr_type (subst_consts_exprs_mods E es) = MAP expr_type es /\
    well_typed_builtin_app ty bi (MAP expr_type es) /\ builtin_operands_ok ty bi es ==>
    builtin_operands_ok ty bi (subst_consts_exprs_mods E es)` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `bi = Bop Exp \/ bi = Bop ShL \/ bi = Bop ShR`
     >- (gvs[well_typed_builtin_app_def] >>
         Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
         gvs[builtin_operands_ok_def, subst_consts_expr_mods_def, shift_amount_ok_def]
         >~ [`power_operands_ok ty (subst_consts_expr_mods E h) (subst_consts_expr_mods E h')`]
         >- (`IS_SOME (int_literal_value h) ==>
              IS_SOME (int_literal_value (subst_consts_expr_mods E h))` by
               (asm "literal" (fn th => metis_tac[th, IS_SOME_EXISTS])) >>
             `power_exponent_ok ty h' ==> subst_consts_expr_mods E h' = h'` by
               (Cases_on `h'` >> simp[power_exponent_ok_def, subst_consts_expr_mods_def]) >>
             qpat_x_assum `no_neg_exp_expr _` mp_tac >>
             gvs[power_operands_ok_def, no_neg_exp_expr_def] >>
             rpt strip_tac >> gvs[] >> metis_tac[]) >>
         asm "literal" (fn th => metis_tac[th])) >>
     Cases_on `bi` >> gvs[builtin_operands_ok_def] >>
     Cases_on `b` >> gvs[builtin_operands_ok_def]) >>
  pop_assum (mk_asm "operands") >>
  `ALOOKUP (constant_context mods).sources (constant_context mods).txn.target = SOME mods`
    by simp[constant_context_def] >>
  `!s ty a b. constant_expr mods a /\
    well_typed_expr (artifact_env art mods s) (Subscript ty a b) ==>
    well_typed_expr (artifact_env art mods s) a` by
    (rpt gen_tac >> strip_tac >> drule_all constant_subscript_base_well_typed >> simp[]) >>
  pop_assum (mk_asm "subscript_base") >>
  `!E s dst. EVERY good E ==>
    (!e. constant_expr mods e /\ well_typed_expr (artifact_env art mods s) e /\
      no_neg_exp_expr (subst_consts_expr_mods E e) ==>
      constant_expr mods (subst_consts_expr_mods E e) /\
      well_typed_expr (artifact_env art mods dst) (subst_consts_expr_mods E e) /\
      expr_type (subst_consts_expr_mods E e) = expr_type e) /\
    (!es. EVERY (constant_expr mods) es /\ well_typed_exprs (artifact_env art mods s) es /\
      no_neg_exp_exprs (subst_consts_exprs_mods E es) ==>
      EVERY (constant_expr mods) (subst_consts_exprs_mods E es) /\
      well_typed_exprs (artifact_env art mods dst) (subst_consts_exprs_mods E es) /\
      MAP expr_type (subst_consts_exprs_mods E es) = MAP expr_type es) /\
    (!fs. EVERY (constant_expr mods) (MAP SND fs) /\
      well_typed_named_exprs (artifact_env art mods s) fs /\
      no_neg_exp_fields (subst_consts_fields_mods E fs) ==>
      EVERY (constant_expr mods) (MAP SND (subst_consts_fields_mods E fs)) /\
      well_typed_named_exprs (artifact_env art mods dst) (subst_consts_fields_mods E fs) /\
      MAP FST (subst_consts_fields_mods E fs) = MAP FST fs /\
      MAP (expr_type o SND) (subst_consts_fields_mods E fs) = MAP (expr_type o SND) fs)` by
    (rpt gen_tac >> disch_tac >> ho_match_mp_tac const_local_refs_ind >>
     simp[constant_expr_def, subst_consts_expr_mods_def, expr_type_def, SF ETA_ss] >>
     rpt conj_tac >> rpt (gen_tac ORELSE disch_then strip_assume_tac)
     >~ [`subst_consts_expr_mods E (TopLevelName ty key)`] >-
       (PairCases_on `key` >>
        Cases_on `ALOOKUP E (key0,key1)` >>
        gvs[subst_consts_expr_mods_def, expr_type_def, constant_expr_def]
        >- gvs[well_typed_expr_def, artifact_env_def] >>
        asm "entry" drule_all >> strip_tac >> simp[] >> first_assum irule >> metis_tac[])
     >~ [`well_typed_expr _ (Subscript ty (subst_consts_expr_mods E a) (subst_consts_expr_mods E b))`] >-
       (`well_typed_expr (artifact_env art mods s) a` by
          (asm "subscript_base" drule_all >> simp[]) >>
        `subscript_type_ok (expr_type a) b ty` by
          (drule_all constant_subscript_type_ok >> simp[]) >>
        `well_typed_expr (artifact_env art mods s) b /\
         well_formed_type (type_env_all_modules mods) ty` by
          fs[Once well_typed_expr_def, artifact_env_def] >>
        fs[no_neg_exp_expr_def] >>
        rpt (qpat_x_assum `_ ==> constant_expr _ _ /\ _` mp_tac >>
             (impl_tac >- simp[]) >> strip_tac) >>
        simp[Once well_typed_expr_def, artifact_env_def] >> disj1_tac >>
        simp[] >> conj_tac
        >- (asm "index" irule >> simp[]) >>
        irule constant_subscript_base_exact >> metis_tac[])
     >~ [`well_typed_expr _ (Builtin ty bi (subst_consts_exprs_mods E es))`] >-
       (gvs[Once well_typed_expr_def, artifact_env_def] >>
        qpat_x_assum `_ ==> EVERY _ _ /\ _` mp_tac >>
        (impl_tac >- fs[no_neg_exp_expr_def]) >> strip_tac >>
        simp[Once well_typed_expr_def, artifact_env_def] >>
        conj_tac >- (Cases_on `bi` >> gvs[constant_builtin_def, slice_operands_ok_def]) >>
        asm "operands" irule >> simp[]) >>
     gvs[Once well_typed_expr_def, no_neg_exp_expr_def, artifact_env_def, SF ETA_ss] >>
     rpt (qpat_x_assum `_ ==> _` mp_tac >> (impl_tac >- simp[]) >> strip_tac) >>
     gvs[Once well_typed_expr_def, artifact_env_def, SF ETA_ss]) >>
  pop_assum (mk_asm "fragment") >>
  (* Folding either keeps the builtin or produces a bytes literal. *)
  `!ty bi es. fold_const_builtin ty bi es = Builtin ty bi es \/
    (bi = Sha256 /\ ?aty l bs. es = [Literal aty l] /\
       fold_const_builtin ty bi es = Literal ty (BytesL bs))` by
    (rpt gen_tac >> Cases_on `es` >> simp[fold_const_builtin_def] >>
     Cases_on `bi` >> simp[] >> Cases_on `t` >> simp[] >>
     Cases_on `h` >> simp[] >> rpt CASE_TAC >> simp[]) >>
  pop_assum (mk_asm "fold_builtin") >>
  `(!e. no_neg_exp_expr (fold_const_expr e) = no_neg_exp_expr e) /\
   (!t. no_neg_exp_btarget (fold_const_btarget t) = no_neg_exp_btarget t) /\
   (!es. no_neg_exp_exprs (fold_const_exprs es) = no_neg_exp_exprs es) /\
   (!d. no_neg_exp_opt (fold_const_opt d) = no_neg_exp_opt d) /\
   (!fs. no_neg_exp_fields (fold_const_fields fs) = no_neg_exp_fields fs)` by
    (ho_match_mp_tac fold_const_expr_ind >>
     simp[fold_const_expr_def, no_neg_exp_expr_def] >> rpt strip_tac >>
     rename1 `fold_const_builtin ty bi (fold_const_exprs es)` >>
     asm "fold_builtin" (qspecl_then [`ty`,`bi`,`fold_const_exprs es`] strip_assume_tac) >>
     gvs[no_neg_exp_expr_def] >> Cases_on `bi = Bop Exp` >> gvs[] >>
     Cases_on `es` >> simp[fold_const_expr_def] >>
     Cases_on `t` >> simp[fold_const_expr_def] >>
     Cases_on `t'` >> simp[fold_const_expr_def] >>
     Cases_on `h'` >> simp[fold_const_expr_def] >>
     rename1 `fold_const_builtin bty bb (fold_const_exprs bes)` >>
     asm "fold_builtin" (qspecl_then [`bty`,`bb`,`fold_const_exprs bes`] strip_assume_tac) >>
     simp[]) >>
  `!ns tops vis init name ty slot E.
    ALOOKUP mods ns = SOME tops /\ MEM (VariableDecl vis (Constant init) name ty slot) tops /\
    EVERY good E /\ no_neg_exp_expr (fold_const_expr (subst_consts_expr_mods E init)) ==>
    good ((ns,name),fold_const_expr (subst_consts_expr_mods E init))` by
    (rpt gen_tac >> strip_tac >> drule_all checked_const_decl_typed >> strip_tac >>
     `!dst. constant_expr mods (subst_consts_expr_mods E init) /\
        well_typed_expr (artifact_env art mods dst) (subst_consts_expr_mods E init) /\
        expr_type (subst_consts_expr_mods E init) = ty` by
       (gen_tac >> asm "fragment" (qspecl_then [`E`,`ns`,`dst`] mp_tac) >>
        simp[] >> strip_tac >>
        qpat_x_assum `!e. constant_expr _ e /\ well_typed_expr _ e /\ _ ==> _`
          (qspec_then `init` mp_tac) >> gvs[]) >>
     simp[Abbr `good`, fold_const_expr_type] >>
     conj_tac
     >- (strip_assume_tac fold_const_expr_constant >>
         qpat_assum `!e. constant_expr _ e ==> constant_expr _ (fold_const_expr e)` irule >>
         first_assum (qspec_then `ns` mp_tac) >> simp[]) >>
     conj_tac >- (gen_tac >> irule fold_const_expr_typed >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     `MEM (ns,tops) mods` by (drule ALOOKUP_MEM >> simp[]) >>
     drule_all vyperTypeConstantCellsTheory.checked_constant_declared_type >> simp[]) >>
  pop_assum (mk_asm "decl") >>
  (* The guard travels backwards through each append; good entries travel forwards. *)
  qabbrev_tac `guard = (EVERY (no_neg_exp_expr o SND) : ((num option # string) # expr) list -> bool)` >>
  `!ns tops ts E. ALOOKUP mods ns = SOME tops /\ EVERY (\t. MEM t tops) ts /\
    guard (module_consts_env_mods ns ts E) ==>
    guard E /\ (EVERY good E ==> EVERY good (module_consts_env_mods ns ts E))` by
    (rpt gen_tac >> qid_spec_tac `E` >> Induct_on `ts`
     >- simp[module_consts_env_mods_def] >>
     rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
     Cases_on `h` >> fs[module_consts_env_mods_def]
     >~ [`module_consts_env_mods ns (VariableDecl vis mut name ty slot :: ts) E`] >-
       (Cases_on `mut` >> fs[module_consts_env_mods_def]
        >~ [`fold_const_expr (subst_consts_expr_mods E init)`] >-
          (qabbrev_tac `new = fold_const_expr (subst_consts_expr_mods E init)` >>
           qpat_x_assum `!E. _ ==> guard E /\ _`
             (qspec_then `E ++ [((ns,name),new)]` mp_tac) >> simp[] >> strip_tac >>
           fs[Abbr `guard`, EVERY_APPEND] >> disch_tac >>
           first_x_assum irule >> simp[EVERY_APPEND, Abbr `new`] >>
           asm "decl" irule >> metis_tac[]) >>
        qpat_assum `!E. _ ==> guard E /\ _` (qspec_then `E` mp_tac) >> simp[]) >>
     qpat_assum `!E. _ ==> guard E /\ _` (qspec_then `E` mp_tac) >> simp[]) >>
  pop_assum (mk_asm "module") >>
  `!units E. (!ns tops. MEM (ns,tops) units ==> ALOOKUP mods ns = SOME tops) /\
    guard (consts_env_mods_acc units E) ==>
    guard E /\ (EVERY good E ==> EVERY good (consts_env_mods_acc units E))` by
    (Induct >- simp[consts_env_mods_acc_def] >>
     qx_gen_tac `unit` >> PairCases_on `unit` >> rename1 `(ns,tops)` >>
     simp[consts_env_mods_acc_def, DISJ_IMP_THM, FORALL_AND_THM] >> gen_tac >> strip_tac >>
     qpat_x_assum `!E. _ ==> guard E /\ _`
       (qspec_then `module_consts_env_mods ns tops E` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     asm "module" (qspecl_then [`ns`,`tops`,`tops`,`E`] mp_tac) >>
     simp[EVERY_MEM] >> strip_tac >> simp[] >> rpt strip_tac >>
     first_assum irule >> first_assum irule >> simp[]) >>
  pop_assum (mk_asm "units") >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule vyperTypeContractContextTheory.check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  `EVERY good (consts_env_mods mods)` by
    (asm "units" (qspecl_then [`constants_order mods`,`[]`] mp_tac) >>
     simp[GSYM consts_env_mods_def, Abbr `guard`] >>
     disch_then irule >> rpt strip_tac >>
     irule ALOOKUP_ALL_DISTINCT_MEM >> fs[vyperInterpreterTheory.MEM_constants_order]) >>
  asm "entry" drule_all >> strip_tac >> simp[]
QED
