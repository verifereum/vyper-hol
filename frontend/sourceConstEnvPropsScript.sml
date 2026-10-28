Theory sourceConstEnvProps
Ancestors
  sourceConstEnv sourceConstEval alist list rich_list pair

(* TOP-LEVEL: append-only/environment preservation, dependency selection,
   unique canonical identities and rejection boundaries. These are local
   opt-in environment contracts, not JSON import/type/deployment theorems. *)

(* ===== Picker interface ===== *)

Theorem source_const_pick_decomposition:
  !ds d rest. source_const_pick env ds = SOME (d,rest) ==>
    ?before after. ds = before ++ d::after /\ rest = before ++ after /\
                   source_const_ready env (SND d)
Proof
  Induct >> simp[source_const_pick_def] >> rpt gen_tac >>
  Cases_on `source_const_ready env (SND h)` >> simp[]
  >- (strip_tac >> gvs[] >> qexistsl_tac [`[]`,`ds`] >> simp[]) >>
  Cases_on `source_const_pick env ds` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >> simp[] >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`h::before`,`after`] >> simp[]
QED

Theorem source_const_pick_none:
  !ds. source_const_pick env ds = NONE <=>
       EVERY (\d. ~source_const_ready env (SND d)) ds
Proof
  Induct >> simp[source_const_pick_def] >>
  Cases_on `source_const_ready env (SND h)` >> simp[] >>
  Cases_on `source_const_pick env ds` >> simp[]
QED

Theorem source_const_pick_members:
  source_const_pick env ds = SOME (d,rest) ==>
  MEM d ds /\ (!x. MEM x rest ==> MEM x ds) /\
  (!key. MEM key (MAP FST ds) <=>
         key = FST d \/ MEM key (MAP FST rest))
Proof
  strip_tac >> drule source_const_pick_decomposition >>
  strip_tac >> gvs[] >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem source_const_pick_partition:
  source_const_pick env ds = SOME (d,rest) ==>
  source_const_ready env (SND d) /\
  (!x. MEM x ds <=> x = d \/ MEM x rest)
Proof
  strip_tac >> drule source_const_pick_decomposition >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem source_const_pick_fresh:
  ALL_DISTINCT (MAP FST env ++ MAP FST ds) /\
  source_const_pick env ds = SOME ((path,expr),rest) ==>
  ALOOKUP env path = NONE
Proof
  strip_tac >> drule source_const_pick_decomposition >>
  strip_tac >> gvs[ALL_DISTINCT_APPEND, ALOOKUP_NONE] >> metis_tac[]
QED

Theorem source_const_pick_distinct:
  ALL_DISTINCT (MAP FST env ++ MAP FST ds) /\
  source_const_pick env ds = SOME ((path,expr),rest) ==>
  ALL_DISTINCT (MAP FST (env ++ [(path,SC_Constant v)]) ++ MAP FST rest)
Proof
  strip_tac >> drule source_const_pick_decomposition >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* No-ready is a blocked dependency region, not a budget failure. With all
   paths accounted for, every blocked declaration depends on another pending
   identity. The payload may also include acyclic dependents of a cycle. *)
Theorem source_const_blocked_dependencies:
  pending <> [] /\ source_const_pick env pending = NONE /\
  (!path expr dep. MEM (path,expr) pending /\
      MEM dep (source_const_names expr) ==>
      MEM dep (MAP FST env) \/ MEM dep (MAP FST pending)) ==>
  !path expr. MEM (path,expr) pending ==>
    ?dep. MEM dep (source_const_names expr) /\
          ~MEM dep (MAP FST env) /\ MEM dep (MAP FST pending)
Proof
  simp[source_const_pick_none, EVERY_MEM, source_const_ready_def, FORALL_PROD] >>
  metis_tac[]
QED

(* ===== Evaluation depends only on resolved name dependencies ===== *)

Theorem source_const_eval_name_congruence:
  !env expr. !other.
    (!path. MEM path (source_const_names expr) ==>
            ALOOKUP env path = ALOOKUP other path) ==>
    source_const_eval env expr = source_const_eval other expr
Proof
  ho_match_mp_tac source_const_eval_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once source_const_names_def, MEM_FLAT, MEM_MAP, PULL_EXISTS,
       DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >>
  simp[source_const_eval_def, source_const_lookup_def] >>
  rpt (FIRST [FIRST_ASSUM (fn th => irule th >> metis_tac[]),
              cong_tac (SOME 1)])
QED

Theorem source_const_eval_append:
  source_const_ready env expr ==>
  source_const_eval (env ++ added) expr = source_const_eval env expr
Proof
  strip_tac >> irule source_const_eval_name_congruence >>
  gvs[source_const_ready_def, EVERY_MEM] >> rw[ALOOKUP_APPEND] >>
  Cases_on `ALOOKUP env path` >> gvs[ALOOKUP_NONE]
QED

(* ===== Append-only and dynamic-binding invariants ===== *)

Theorem source_const_pending_extension:
  !env pending. !out.
    source_const_resolve_pending env pending = SCEnv_Resolved out ==>
    ?added. out = env ++ added /\ EVERY (source_const_binding_ok o SND) added /\
      EVERY (\entry. ?v. SND entry = SC_Constant v /\ source_const_value_ok v) added
Proof
  ho_match_mp_tac source_const_resolve_pending_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `pending = []`
  >- (gvs[Once source_const_resolve_pending_def] >> strip_tac >>
      gvs[] >> qexists_tac `[]` >> simp[]) >>
  simp[Once source_const_resolve_pending_def] >>
  Cases_on `source_const_pick env pending` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  rename1 `source_const_pick env pending = SOME ((path,expr),rest)` >> simp[] >>
  Cases_on `source_const_eval env expr` >> simp[] >>
  rename1 `SC_Value value` >>
  Cases_on `source_const_value_ok value` >> simp[] >>
  strip_tac >> fs[source_const_binding_ok_def]
QED

Theorem source_const_resolve_extension:
  source_const_resolve seed decls = SCEnv_Resolved out ==>
  ?added. out = seed ++ added /\ EVERY (source_const_binding_ok o SND) added /\
    EVERY (\entry. ?v. SND entry = SC_Constant v /\ source_const_value_ok v) added
Proof
  simp[source_const_resolve_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> drule source_const_pending_extension >> simp[]
QED

Theorem source_const_resolve_preserves_lookup:
  source_const_resolve seed decls = SCEnv_Resolved out /\
  ALOOKUP seed path = SOME binding ==>
  ALOOKUP out path = SOME binding
Proof
  strip_tac >> drule source_const_resolve_extension >>
  strip_tac >> gvs[ALOOKUP_APPEND]
QED

Theorem source_const_resolve_preserves_dynamic:
  source_const_resolve seed decls = SCEnv_Resolved out /\
  ALOOKUP seed path = SOME SC_DynamicBinding ==>
  source_const_lookup out path = SC_NotConstant
Proof
  strip_tac >> drule_all source_const_resolve_preserves_lookup >>
  simp[source_const_lookup_def]
QED

Theorem source_const_resolve_bindings_ok:
  source_const_resolve seed decls = SCEnv_Resolved out ==>
  EVERY (source_const_binding_ok o SND) out
Proof
  strip_tac >> drule source_const_resolve_extension >> strip_tac >>
  gvs[source_const_resolve_def, LET_THM, AllCaseEqs(), combinTheory.o_DEF]
QED

Theorem source_const_resolve_dynamic_origin:
  source_const_resolve seed decls = SCEnv_Resolved out /\
  ALOOKUP out path = SOME SC_DynamicBinding ==>
  ALOOKUP seed path = SOME SC_DynamicBinding
Proof
  strip_tac >> drule source_const_resolve_extension >> strip_tac >>
  gvs[ALOOKUP_APPEND, AllCaseEqs()] >>
  drule ALOOKUP_MEM >> strip_tac >>
  qpat_x_assum `EVERY (\entry. _) added`
    (qspec_then `(path,SC_DynamicBinding)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  simp[]
QED

(* Adding declarations in other resolved modules cannot change any expression
   whose names were already bound. In particular imports and lexical runtime
   bindings do not acquire a new meaning when the constant env is extended. *)
Theorem source_const_resolve_preserves_evaluation:
  source_const_resolve seed decls = SCEnv_Resolved out /\
  source_const_ready seed expr ==>
  source_const_eval out expr = source_const_eval seed expr
Proof
  strip_tac >> irule source_const_eval_name_congruence >>
  drule source_const_resolve_extension >> strip_tac >>
  gvs[source_const_ready_def, EVERY_MEM] >> rw[ALOOKUP_APPEND] >>
  Cases_on `ALOOKUP seed path` >> gvs[ALOOKUP_NONE]
QED

(* ===== Key/domain invariants ===== *)

Theorem source_const_pending_distinct:
  !env pending. !out.
  ALL_DISTINCT (MAP FST env ++ MAP FST pending) /\
  source_const_resolve_pending env pending = SCEnv_Resolved out ==>
  ALL_DISTINCT (MAP FST out)
Proof
  ho_match_mp_tac source_const_resolve_pending_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_const_resolve_pending _ _ = _` mp_tac >>
  Cases_on `pending = []`
  >- (gvs[Once source_const_resolve_pending_def] >> rw[] >> gvs[]) >>
  simp[Once source_const_resolve_pending_def] >>
  Cases_on `source_const_pick env pending` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  rename1 `source_const_pick env pending = SOME ((path,expr),rest)` >> simp[] >>
  Cases_on `source_const_eval env expr` >> simp[] >>
  rename1 `SC_Value value` >>
  Cases_on `source_const_value_ok value` >> simp[] >>
  strip_tac >> fs[] >> first_x_assum irule >> simp[] >>
  drule_all source_const_pick_distinct >> simp[]
QED

Theorem source_const_pending_domain:
  !env pending. !out.
  source_const_resolve_pending env pending = SCEnv_Resolved out ==>
  !path. MEM path (MAP FST out) <=>
         MEM path (MAP FST env) \/ MEM path (MAP FST pending)
Proof
  ho_match_mp_tac source_const_resolve_pending_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `pending = []`
  >- (gvs[Once source_const_resolve_pending_def] >> rw[] >> gvs[]) >>
  simp[Once source_const_resolve_pending_def] >>
  Cases_on `source_const_pick env pending` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  rename1 `source_const_pick env pending = SOME ((path,expr),rest)` >> simp[] >>
  Cases_on `source_const_eval env expr` >> simp[] >>
  rename1 `SC_Value value` >>
  Cases_on `source_const_value_ok value` >> simp[] >>
  strip_tac >> fs[] >>
  drule source_const_pick_members >> simp[] >> metis_tac[]
QED

(* ===== Each computed binding agrees with its original initializer ===== *)

Theorem source_const_selected_sound:
  ALL_DISTINCT (MAP FST env ++ MAP FST pending) /\
  source_const_pick env pending = SOME ((path,expr),rest) /\
  source_const_eval env expr = SC_Value v /\
  source_const_resolve_pending (env ++ [(path,SC_Constant v)]) rest =
    SCEnv_Resolved out ==>
  ALOOKUP out path = SOME (SC_Constant v) /\
  source_const_eval out expr = SC_Value v
Proof
  strip_tac >> drule_all source_const_pick_fresh >> strip_tac >>
  drule source_const_pick_partition >> strip_tac >>
  drule source_const_pending_extension >> strip_tac >>
  gvs[] >> conj_tac >- simp[ALOOKUP_APPEND] >>
  drule source_const_eval_append >>
  disch_then (qspec_then `[(path,SC_Constant v)] ++ added` mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem source_const_pending_initializer_values:
  !env pending. !out.
  ALL_DISTINCT (MAP FST env ++ MAP FST pending) /\
  source_const_resolve_pending env pending = SCEnv_Resolved out ==>
  !path expr. MEM (path,expr) pending ==>
    ?v. ALOOKUP out path = SOME (SC_Constant v) /\
        source_const_eval out expr = SC_Value v
Proof
  ho_match_mp_tac source_const_resolve_pending_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_const_resolve_pending _ _ = _` mp_tac >>
  Cases_on `pending = []` >- gvs[] >>
  simp[Once source_const_resolve_pending_def] >>
  Cases_on `source_const_pick env pending` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  rename1 `source_const_pick env pending = SOME ((path,expr),rest)` >> simp[] >>
  Cases_on `source_const_eval env expr` >> simp[] >>
  rename1 `SC_Value value` >>
  Cases_on `source_const_value_ok value` >> simp[] >> strip_tac >>
  `ALL_DISTINCT (MAP FST (env ++ [(path,SC_Constant value)]) ++ MAP FST rest)` by
    (drule_all source_const_pick_distinct >> simp[]) >>
  fs[] >> drule source_const_pick_partition >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac
  >- (gvs[] >> drule_all source_const_selected_sound >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem source_const_resolve_initializer_values:
  source_const_resolve seed decls = SCEnv_Resolved out ==>
  !path expr. MEM (path,expr) decls ==>
    ?v. ALOOKUP out path = SOME (SC_Constant v) /\
        source_const_eval out expr = SC_Value v
Proof
  simp[source_const_resolve_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> drule_all source_const_pending_initializer_values >>
  metis_tac[]
QED

Theorem source_const_resolve_identity_invariant:
  source_const_resolve seed decls = SCEnv_Resolved out ==>
  ALL_DISTINCT (MAP FST out) /\
  EVERY source_const_identity_ok (MAP FST out) /\
  (!path. MEM path (MAP FST out) <=>
          MEM path (MAP FST seed) \/ MEM path (MAP FST decls))
Proof
  simp[source_const_resolve_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >>
  drule source_const_pending_domain >> strip_tac >>
  drule_all source_const_pending_distinct >> strip_tac >>
  simp[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

(* Canonical identity is component equality: equal leaf spelling is not enough
   for substitution, and no string-joining convention is used. *)
Theorem source_const_lookup_distinct_identity:
  path <> other ==>
  source_const_lookup ((other,binding)::env) path = source_const_lookup env path
Proof
  simp[source_const_lookup_def]
QED

Theorem source_const_duplicate_rejected:
  EVERY source_const_identity_ok (MAP FST seed ++ MAP FST decls) /\
  ~ALL_DISTINCT (MAP FST seed ++ MAP FST decls) ==>
  source_const_resolve seed decls =
    SCEnv_Duplicate (MAP FST seed ++ MAP FST decls)
Proof
  simp[source_const_resolve_def, EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >>
  metis_tac[]
QED
