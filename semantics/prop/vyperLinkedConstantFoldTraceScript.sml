(* Source-indexed trace of successful constant installation. *)
Theory vyperLinkedConstantFoldTrace
Ancestors
  vyperAST vyperState vyperTypeContract vyperTypeInitialState
  finite_map pred_set list pair

Theorem constants_fold_module_key_origin[local]:
  !mods imms src ts acc out id.
    constants_fold_module mods imms src ts acc = SOME out /\ id IN FDOM out ==>
    id IN FDOM acc \/
    ?vis e ty init. MEM (VariableDecl vis (Constant e) id ty init) ts
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rw[constants_fold_module_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
  metis_tac[]
QED

(* At each step, the current source is fresh for its declared constants.
   Other slots are unchanged, so the freshness hypothesis passes to the tail. *)
Theorem constants_fold_trace_aux[local]:
  !rest init last.
    constants_fold mods init rest = SOME last /\
    ALL_DISTINCT (MAP FST rest) /\
    EVERY (\m. MEM m mods) rest /\
    (!s ts id. MEM (s,ts) rest /\ declared_constant mods s id ==>
       FLOOKUP (get_source_immutables s init) id = NONE) ==>
    (!s. get_source_immutables s init SUBMAP get_source_immutables s last) /\
    (!src ts. MEM (src,ts) rest ==>
      ?ref env.
        constants_fold_module mods ref src ts FEMPTY = SOME env /\
        (!s. get_source_immutables s ref SUBMAP get_source_immutables s last) /\
        env SUBMAP get_source_immutables src last /\
        (!id. id IN FDOM env ==> declared_constant mods src id))
Proof
  Induct >- simp[constants_fold_def] >>
  Cases_on `h` >> rename1 `(src,ts)` >>
  simp[constants_fold_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >>
  rename1 `constants_fold_module mods init src ts FEMPTY = SOME env` >>
  `!id. id IN FDOM env ==> declared_constant mods src id` by
    (drule constants_fold_module_key_origin >>
     simp[declared_constant_def] >> metis_tac[]) >>
  qabbrev_tac `mid = merge_constant_imms src env init` >>
  `!s tops. MEM (s,tops) rest ==> s <> src` by
    (fs[MEM_MAP] >> metis_tac[FST]) >>
  `!s tops id. MEM (s,tops) rest /\ declared_constant mods s id ==>
     FLOOKUP (get_source_immutables s mid) id = NONE` by
    (rpt strip_tac >>
     `s <> src` by metis_tac[] >>
     simp[Abbr `mid`, merge_constant_imms_def, get_source_immutables_set_other] >>
     metis_tac[]) >>
  `!s. get_source_immutables s init SUBMAP get_source_immutables s mid` by
    (gen_tac >> Cases_on `s = src` >>
     simp[Abbr `mid`, merge_constant_imms_def, get_source_immutables_set_same,
          get_source_immutables_set_other] >>
     irule (CONJUNCT2 SUBMAP_FUNION_ID) >>
     simp[IN_DISJOINT] >> metis_tac[flookup_thm]) >>
  first_x_assum (qspecl_then [`mid`, `last`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  conj_asm1_tac >- metis_tac[SUBMAP_TRANS] >>
  rpt gen_tac >> disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (gvs[] >> qexistsl [`init`, `env`] >> simp[] >>
      `env SUBMAP get_source_immutables src mid` by
        simp[Abbr `mid`, merge_constant_imms_def, get_source_immutables_set_same,
             SUBMAP_FUNION_ID] >>
      metis_tac[SUBMAP_TRANS]) >>
  metis_tac[]
QED

Theorem constants_fold_member_trace:
  constants_fold mods init rest = SOME last /\
  ALL_DISTINCT (MAP FST rest) /\
  EVERY (\m. MEM m mods) rest /\
  (!s ts id. MEM (s,ts) rest /\ declared_constant mods s id ==>
     FLOOKUP (get_source_immutables s init) id = NONE) /\
  MEM (src,ts) rest ==>
  ?ref env.
    constants_fold_module mods ref src ts FEMPTY = SOME env /\
    (!s. get_source_immutables s ref SUBMAP get_source_immutables s last) /\
    env SUBMAP get_source_immutables src last /\
    (!id. id IN FDOM env ==> declared_constant mods src id)
Proof
  rpt strip_tac >> drule_all constants_fold_trace_aux >>
  disch_then (mp_tac o CONJUNCT2) >>
  disch_then drule >> simp[]
QED
