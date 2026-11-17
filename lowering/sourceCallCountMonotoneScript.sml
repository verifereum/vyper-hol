(* Budget monotonicity for the shared source outcome counter. *)
Theory sourceCallCountMonotone
Ancestors
  sourceCallCount list option pair arithmetic vyperState
Libs BasicProvers

val _ = Parse.hide "run";

(* A larger synthetic budget follows the same probes until non-exhaustion. *)
Theorem entry_calls_within_from_mono:
  !run.
    (!prefix extra.
       entry_calls_within_from 0 prefix run ==>
       entry_calls_within_from 0 (prefix ++ extra) run) ==>
    !n m os.
      n <= m /\ entry_calls_within_from n os run ==>
      entry_calls_within_from m os run
Proof
  gen_tac >> strip_tac >> Induct_on `n`
  >- (rpt gen_tac >> strip_tac >> Cases_on `m` >- gvs[] >>
      qpat_x_assum `!prefix extra. _`
        (qspecl_then [`os`,`[probe_failed_outcome]`] mp_tac) >>
      impl_tac >- asm_rewrite_tac [] >>
      Cases_on `run (os ++ [probe_failed_outcome])` >>
      simp[entry_calls_within_from_def] >>
      rename1 `run (os ++ [probe_failed_outcome]) = SOME rp` >>
      Cases_on `rp` >> simp[])
  >> rpt gen_tac >> Cases_on `m` >- simp[] >>
  Cases_on `run (os ++ [probe_failed_outcome])` >>
  simp[entry_calls_within_from_def] >>
  rename1 `run (os ++ [probe_failed_outcome]) = SOME rp` >>
  Cases_on `rp` >> rw[] >>
  first_x_assum irule >> simp[]
QED

(* Before the real oracle ends, increasing the budget also extends TAKE n. *)
Theorem entry_calls_within_mono:
  !run.
    (!prefix extra.
       entry_calls_within_from 0 prefix run ==>
       entry_calls_within_from 0 (prefix ++ extra) run) ==>
    !n m os.
      n <= m /\ entry_calls_within n os run ==>
      entry_calls_within m os run
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n <= LENGTH os`
  >- (`n - LENGTH (TAKE n os) = 0` by
        simp[LENGTH_TAKE_EQ, MIN_DEF] >>
      `TAKE n (TAKE m os) = TAKE n os` by
        (rw[TAKE_TAKE_MIN, MIN_DEF] >> `m = n` by decide_tac >> simp[]) >>
      `TAKE m os = TAKE n os ++ DROP n (TAKE m os)` by
        metis_tac[TAKE_DROP] >>
      `entry_calls_within_from 0 (TAKE m os) run` by
        metis_tac[entry_calls_within_def] >>
      simp[entry_calls_within_def] >>
      irule entry_calls_within_from_mono >> simp[] >>
      qexists_tac `0` >> simp[])
  >> `TAKE n os = os /\ TAKE m os = os` by
       (conj_tac >> irule TAKE_LENGTH_TOO_LONG >> decide_tac) >>
  fs[entry_calls_within_def, TAKE_LENGTH_TOO_LONG] >>
  irule entry_calls_within_from_mono >> simp[] >>
  qexists_tac `n - LENGTH os` >> simp[] >> decide_tac
QED

Theorem source_calls_within_zero_append[local]:
  !am tx gobs prefix extra.
    entry_calls_within_from 0 prefix
      (\xs. call_entry_run xs gobs am tx) ==>
    entry_calls_within_from 0 (prefix ++ extra)
      (\xs. call_entry_run xs gobs am tx)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `call_entry_run (prefix ++ extra) gobs am tx` >>
  simp[entry_calls_within_from_def] >>
  rename1 `call_entry_run (prefix ++ extra) gobs am tx = SOME rp` >>
  Cases_on `rp` >> rename1 `SOME (res,st)` >>
  `source_calls_within (LENGTH prefix) am tx (prefix ++ extra) gobs` by
    simp[source_calls_within_def, entry_calls_within_def, TAKE_APPEND1] >>
  `LENGTH prefix <= LENGTH (prefix ++ extra)` by simp[] >>
  drule_all source_calls_within_truncate >> simp[] >>
  disch_then (qx_choose_then `rest` strip_assume_tac) >> simp[]
QED

Theorem deploy_source_calls_within_zero_append[local]:
  !tops am tx gobs prefix extra.
    entry_calls_within_from 0 prefix
      (\xs. deploy_entry_run xs gobs tops am tx) ==>
    entry_calls_within_from 0 (prefix ++ extra)
      (\xs. deploy_entry_run xs gobs tops am tx)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `deploy_entry_run (prefix ++ extra) gobs tops am tx` >>
  simp[entry_calls_within_from_def] >>
  rename1 `deploy_entry_run (prefix ++ extra) gobs tops am tx = SOME rp` >>
  Cases_on `rp` >> rename1 `SOME (res,st)` >>
  `deploy_source_calls_within (LENGTH prefix) tops am tx (prefix ++ extra) gobs` by
    simp[deploy_source_calls_within_def, entry_calls_within_def, TAKE_APPEND1] >>
  `LENGTH prefix <= LENGTH (prefix ++ extra)` by simp[] >>
  drule_all deploy_source_calls_within_truncate >> simp[] >>
  disch_then (qx_choose_then `rest` strip_assume_tac) >> simp[]
QED

Theorem source_calls_within_mono:
  !n m am tx os gobs.
    n <= m /\ source_calls_within n am tx os gobs ==>
    source_calls_within m am tx os gobs
Proof
  simp_tac bool_ss [source_calls_within_def] >> rpt strip_tac >>
  irule entry_calls_within_mono >>
  simp[source_calls_within_zero_append] >>
  qexists_tac `n` >> simp[]
QED

Theorem deploy_source_calls_within_mono:
  !n m tops am tx os gobs.
    n <= m /\ deploy_source_calls_within n tops am tx os gobs ==>
    deploy_source_calls_within m tops am tx os gobs
Proof
  simp_tac bool_ss [deploy_source_calls_within_def] >> rpt strip_tac >>
  irule entry_calls_within_mono >>
  simp[deploy_source_calls_within_zero_append] >>
  qexists_tac `n` >> simp[]
QED
