Theory sourceMeaningEnv
Ancestors
  sourceMeaningConst sourceConstEnvProps sourceConstEnv sourceConstEval alist list

(* Independent finite dependency derivations. A constant can be introduced
   only after all referenced declarations have meanings; fresh extension starts
   at the supplied seed. Cyclic/self-supporting fixed points are NOT meanings.
   This relation neither calls the resolver nor chooses its dependency order. *)
Inductive source_meaning_declarations:
[done:]
  source_meaning_declarations seed [] seed
[extend:]
  source_const_ready seed original /\
  source_meaning_const seed original = SC_Value value /\
  source_const_value_ok value /\ ALOOKUP seed path = NONE /\
  source_meaning_declarations (seed ++ [(path,SC_Constant value)])
    (before ++ after) constants ==>
  source_meaning_declarations seed (before ++ (path,original)::after) constants
End

Theorem source_meaning_pending_derivation:
  !seed pending. !constants.
    ALL_DISTINCT (MAP FST seed ++ MAP FST pending) /\
    source_const_resolve_pending seed pending = SCEnv_Resolved constants ==>
    source_meaning_declarations seed pending constants
Proof
  ho_match_mp_tac source_const_resolve_pending_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_const_resolve_pending _ _ = _` mp_tac >>
  Cases_on `pending = []`
  >- (gvs[Once source_const_resolve_pending_def] >>
      simp[source_meaning_declarations_rules]) >>
  simp[Once source_const_resolve_pending_def] >>
  Cases_on `source_const_pick seed pending` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  rename1 `source_const_pick seed pending = SOME ((path,original),rest)` >> simp[] >>
  Cases_on `source_const_eval seed original` >> simp[] >>
  rename1 `SC_Value value` >>
  Cases_on `source_const_value_ok value` >> simp[] >> strip_tac >>
  drule_all source_const_pick_distinct >> strip_tac >>
  drule_all source_const_pick_fresh >> strip_tac >>
  drule source_const_pick_decomposition >> strip_tac >> gvs[] >>
  gvs[source_meaning_const_correct] >>
  metis_tac[extend, APPEND_ASSOC, APPEND]
QED

Theorem source_meaning_resolve_derivation:
  source_const_resolve seed declarations = SCEnv_Resolved constants ==>
  source_meaning_declarations seed declarations constants
Proof
  simp[source_const_resolve_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> drule_all source_meaning_pending_derivation >> simp[]
QED

Theorem source_meaning_declarations_domain:
  !seed declarations constants.
    source_meaning_declarations seed declarations constants ==>
    !path. MEM path (MAP FST constants) <=>
      MEM path (MAP FST seed) \/ MEM path (MAP FST declarations)
Proof
  ho_match_mp_tac source_meaning_declarations_ind >> simp[] >>
  rpt gen_tac >> strip_tac >> simp[] >> metis_tac[]
QED

(* Finite derivations preserve every already-bound declaration identity, not
   merely the final domain. This also transports named defaults under extension. *)
Theorem source_meaning_declarations_extension:
  !seed declarations constants.
    source_meaning_declarations seed declarations constants ==>
    ?added. constants = seed ++ added
Proof
  ho_match_mp_tac source_meaning_declarations_ind >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[APPEND_ASSOC]
QED

Theorem source_meaning_declarations_lookup:
  source_meaning_declarations seed declarations constants /\
  ALOOKUP seed path = SOME binding ==>
  ALOOKUP constants path = SOME binding
Proof
  strip_tac >> drule source_meaning_declarations_extension >>
  strip_tac >> gvs[ALOOKUP_APPEND]
QED

Theorem source_meaning_declarations_evaluation:
  source_meaning_declarations seed declarations constants /\
  source_const_ready seed original ==>
  source_meaning_const constants original = source_meaning_const seed original
Proof
  strip_tac >> irule source_meaning_const_transport >>
  gvs[source_const_ready_def, EVERY_MEM] >> rpt strip_tac >>
  Cases_on `ALOOKUP seed p` >> gvs[ALOOKUP_NONE] >>
  drule_all source_meaning_declarations_lookup >> simp[]
QED

Theorem source_meaning_no_self_support:
  ~source_meaning_declarations [] [(path,SCE_Name path)] constants
Proof
  simp[Once source_meaning_declarations_cases, source_const_ready_def,
    source_const_names_def, APPEND_EQ_SING]
QED
