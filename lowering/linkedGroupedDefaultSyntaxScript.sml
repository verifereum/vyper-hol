(* The grouped dispatcher consumes the checker facts after constant inlining. *)
Theory linkedGroupedDefaultSyntax
Ancestors
  constSubst constSubstMods linkedConstAnnotations whitelistLinkedBodyCallSites
  constSubstCorrect
  whitelistCheckerConsts vyperTypeContract vyperTypeContractContext
  vyperTypeExternalDefaults vyperAST alist list pair arithmetic combin

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

Theorem subst_qualified_runtime_constant:
  EVERY (constant_expr mods o SND) E /\ runtime_constant_expr mods e ==>
  runtime_constant_expr mods (subst_consts_expr_mods E e)
Proof
  strip_tac >>
  `!key r. ALOOKUP E key = SOME r ==> constant_expr mods r` by
    (rpt strip_tac >>
     qpat_assum `EVERY _ E`
       (qspec_then `(key,r)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[combinTheory.o_DEF] >> metis_tac[ALOOKUP_MEM]) >>
  `!s id ty. (declared_constant mods s id \/ declared_immutable mods s id) ==>
       runtime_constant_expr mods (subst_consts_expr_mods E (TopLevelName ty (s,id)))` by
    (rpt gen_tac >> Cases_on `ALOOKUP E (s,id)` >>
     simp[subst_consts_expr_mods_def, runtime_constant_expr_def] >>
     metis_tac[constant_expr_runtime_constant]) >>
  `!exp. bool_literal_expr exp ==> bool_literal_expr (subst_consts_expr_mods E exp)` by
    (Cases >> simp[bool_literal_expr_def, subst_consts_expr_mods_def]) >>
  `!es. EVERY (constant_expr mods) es ==>
        EVERY (constant_expr mods) (subst_consts_exprs_mods E es)` by
    (rpt strip_tac >> irule (cj 2 subst_const_mods_constant) >> asm_rewrite_tac[]) >>
  `!es. subst_consts_exprs_mods E es = MAP (subst_consts_expr_mods E) es` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `!fs. MAP SND (subst_consts_fields_mods E fs) =
        MAP (subst_consts_expr_mods E) (MAP SND fs)` by
    (Induct >> simp[subst_consts_expr_mods_def] >>
     Cases >> simp[subst_consts_expr_mods_def]) >>
  `!ms exp. ms = mods /\ runtime_constant_expr ms exp ==>
     runtime_constant_expr ms (subst_consts_expr_mods E exp)`
    suffices_by metis_tac[] >>
  ho_match_mp_tac runtime_constant_expr_ind >>
  simp[runtime_constant_expr_def] >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `!s id ty. _` irule >> simp[] >> NO_TAC) >>
  simp[subst_consts_expr_mods_def, runtime_constant_expr_def] >>
  fs[EVERY_MAP, combinTheory.o_DEF, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP] >> res_tac >> fs[] >>
  metis_tac[]
QED

Theorem grouped_checked_default_syntax_mods:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  module_allocated layouts addr src tops /\
  MEM (FunctionDecl External mut nr rr name args defaults ret body) tops /\
  ds = subst_consts_exprs_mods (consts_env_mods mods) defaults ==>
  LENGTH ds <= LENGTH args /\
  MAP expr_type ds = MAP SND (DROP (LENGTH args - LENGTH ds) args) /\
  EVERY (runtime_constant_expr mods) ds /\
  well_typed_exprs (artifact_env art mods src) ds
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `External <> Deploy` by simp[] >>
  drule_all check_contract_runtime_function_body_MEM >>
  simp[check_function_body_def, defaults_env_function_entry_env] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH defaults <= LENGTH args` by
    (qpat_assum `MAP expr_type defaults = _`
       (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `!es. subst_consts_exprs_mods (consts_env_mods mods) es =
        MAP (subst_consts_expr_mods (consts_env_mods mods)) es` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `MAP expr_type ds = MAP expr_type defaults` by
    (qpat_assum `ds = subst_consts_exprs_mods _ _` SUBST1_TAC >>
     qpat_assum `!es. subst_consts_exprs_mods _ es = _`
       (qspec_then `defaults` (fn th => PURE_REWRITE_TAC [th, MAP_MAP_o])) >>
     irule MAP_CONG >>
     simp[combinTheory.o_DEF] >> rpt strip_tac >>
     `well_typed_expr (artifact_env art mods src) x` by
       (irule frame_well_typed_exprs_member >>
        qexists_tac `defaults` >> asm_rewrite_tac[]) >>
     mp_tac (Q.INST [`dep` |-> `F`, `env` |-> `artifact_env art mods src`,
       `e` |-> `x`] (SPEC_ALL checked_linked_const_annotation)) >>
     simp[artifact_env_def]) >>
  `EVERY (constant_expr mods o SND) (consts_env_mods mods)` by
    (drule_then ACCEPT_TAC checked_const_mods_constant) >>
  `EVERY (runtime_constant_expr mods) ds` by
    (qpat_assum `ds = _` SUBST1_TAC >>
     qpat_assum `!es. subst_consts_exprs_mods _ es = _`
       (qspec_then `defaults` (fn th => PURE_REWRITE_TAC [th, EVERY_MAP, combinTheory.o_DEF])) >>
     simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `e` >> strip_tac >>
     irule subst_qualified_runtime_constant >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qpat_assum `EVERY (runtime_constant_expr mods) defaults`
       (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
  `LENGTH ds = LENGTH defaults` by
    (qpat_assum `ds = _` SUBST1_TAC >>
     qpat_assum `!es. subst_consts_exprs_mods _ es = _`
       (qspec_then `defaults` (fn th => PURE_REWRITE_TAC [th, LENGTH_MAP])) >>
     REFL_TAC) >>
  qpat_x_assum `ds = subst_consts_exprs_mods _ _` SUBST_ALL_TAC >>
  asm_rewrite_tac[]
QED
