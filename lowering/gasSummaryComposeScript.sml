(* Sequential source evaluation concatenates explicit-event markings,
   while target paths account for every generated and explicit read. *)
Theory gasSummaryCompose
Ancestors
  gasSummary fragGasMode fragGasPath fragGasPathMem gasCount vyperState vyperInterpreter
  list rich_list arithmetic

Theorem gas_explicit_append_path:
  gas_path ctx func s (LENGTH left) (OK t) ==>
  gas_explicit (left ++ right) s.vs_gas_readings =
    gas_explicit left s.vs_gas_readings ++
    gas_explicit right t.vs_gas_readings
Proof
  strip_tac >> drule gas_path_suffix >>
  simp[gas_count_suffix_def, gas_explicit_append]
QED

Theorem gas_source_bind_normal:
  (!tail. source (es with gas_obs := xs ++ tail) =
     (INL v, mid with gas_obs := tail)) /\
  (!tail. next v ((mid with gas_obs := []) with gas_obs := ys ++ tail) =
     (res, fin with gas_obs := tail)) ==>
  !tail. bind source next (es with gas_obs := (xs ++ ys) ++ tail) =
     (res, fin with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[bind_def]
QED

Theorem gas_source_bind_exception:
  (!tail. source (es with gas_obs := xs ++ tail) =
     (INR exc, fin with gas_obs := tail)) ==>
  !tail. bind source next (es with gas_obs := xs ++ tail) =
     (INR exc, fin with gas_obs := tail)
Proof
  simp[bind_def]
QED

Theorem gas_source_ignore_return_exception_bind:
  (!tail. ignore_bind source (return ()) (es with gas_obs := xs ++ tail) =
     (INR exc, fin with gas_obs := tail)) ==>
  !tail. bind source next (es with gas_obs := xs ++ tail) =
     (INR exc, fin with gas_obs := tail)
Proof
  strip_tac >> gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `source (es with gas_obs := xs ++ tail)` >>
  rename1 `source _ = (result, state)` >> Cases_on `result` >>
  simp[ignore_bind_def, bind_def, return_def]
QED

Theorem gas_source_finally_exception:
  (!tail. source (es with gas_obs := xs ++ tail) =
     (INR exc, mid with gas_obs := tail)) /\
  (!tail. cleanup ((mid with gas_obs := []) with gas_obs := tail) =
     (INL (), fin with gas_obs := tail)) ==>
  !tail. finally source cleanup (es with gas_obs := xs ++ tail) =
     (INR exc, fin with gas_obs := tail)
Proof
  simp[evaluation_state_component_equality] >> strip_tac >>
  simp[finally_def, ignore_bind_def, bind_def, raise_def]
QED

Theorem gas_source_try_exception:
  (!tail. source (es with gas_obs := xs ++ tail) =
     (INR exc, mid with gas_obs := tail)) /\
  (!tail. handler exc ((mid with gas_obs := []) with gas_obs := tail) =
     (INR exc, fin with gas_obs := tail)) ==>
  !tail. try source handler (es with gas_obs := xs ++ tail) =
     (INR exc, fin with gas_obs := tail)
Proof
  simp[evaluation_state_component_equality] >> strip_tac >> simp[try_def]
QED

Theorem gas_summary_bind:
  gas_summary (ctx, func) source (es, s0)
    (\res es_mid t.
       ?v. res = INL v /\
           gas_summary (ctx, func) (next v) (es_mid, t) Q R)
    (\res es_end r. ?exc. res = INR exc /\ R (INR exc) es_end r) ==>
  gas_summary (ctx, func) (bind source next) (es, s0) Q R
Proof
  rewrite_tac[gas_summary_def] >>
  disch_then (qx_choose_then `left` (qx_choose_then `res`
    (qx_choose_then `mid` strip_assume_tac)))
  >- (gvs[] >> (
      rename1 `!tail. next v (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) = (out, fin with gas_obs := tail)` >>
      qexistsl_tac [`left ++ right`, `out`, `fin`] >>
      conj_tac
      >- (`gas_explicit (left ++ right) s0.vs_gas_readings =
             gas_explicit left s0.vs_gas_readings ++
             gas_explicit right t.vs_gas_readings` by
            (irule gas_explicit_append_path >> metis_tac[]) >>
          asm_rewrite_tac[] >>
          irule gas_source_bind_normal >>
          qexistsl_tac [`mid`, `v`] >> simp[]) >>
      simp[LENGTH_APPEND] >>
      drule_all gas_path_then >> strip_tac >>
      qmatch_asmsub_abbrev_tac `gas_path ctx func s0 (LENGTH left + LENGTH right) final` >>
      qexists_tac `final` >> simp[Abbr `final`])) >>
  gvs[] >> qexistsl_tac [`left`, `INR exc`, `mid`] >>
  conj_tac
  >- (irule gas_source_bind_exception >> simp[]) >>
  qexists_tac `r` >> simp[]
QED


Theorem gas_marked_exec_bind_normal:
  gas_marked_exec memory (ctx, func) source (es, s0) left (INL v) mid (OK t) /\
  gas_marked_exec memory (ctx, func) (next v)
    (mid with gas_obs := [], t) right res fin r ==>
  gas_marked_exec memory (ctx, func) (bind source next)
    (es, s0) (left ++ right) res fin r
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >> conj_tac
  >- (`gas_explicit (left ++ right) s0.vs_gas_readings =
         gas_explicit left s0.vs_gas_readings ++
         gas_explicit right t.vs_gas_readings` by
        metis_tac[gas_marked_path_exec, gas_explicit_append_path] >>
      asm_rewrite_tac[] >> irule gas_source_bind_normal >>
      qexistsl_tac [`mid`, `v`] >> simp[]) >>
  simp[LENGTH_APPEND] >> metis_tac[gas_marked_path_then]
QED

Theorem gas_marked_source_bind_normal:
  gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
  (!tail. k v ((mid with gas_obs := []) with
       gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
     (res, ee with gas_obs := tail)) ==>
  !tail. bind a k (es with
      gas_obs := gas_explicit (left ++ right) s0.vs_gas_readings ++ tail) =
    (res, ee with gas_obs := tail)
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  `gas_explicit (left ++ right) s0.vs_gas_readings =
     gas_explicit left s0.vs_gas_readings ++
     gas_explicit right t.vs_gas_readings` by
    metis_tac[gas_marked_path_exec, gas_explicit_append_path] >>
  asm_rewrite_tac[] >> irule gas_source_bind_normal >>
  qexistsl_tac [`mid`, `v`] >> simp[]
QED

Theorem gas_marked_exec_bind_exception:
  gas_marked_exec memory (ctx, func) source (es, s0) marks (INR exc) fin r ==>
  gas_marked_exec memory (ctx, func) (bind source next)
    (es, s0) marks (INR exc) fin r
Proof
  simp[gas_marked_exec_def, gas_source_bind_exception]
QED

(* Scope and call cleanup can change the source frame without reading gas. *)
Theorem gas_marked_exec_finally:
  gas_marked_exec memory (ctx, func) source (es, s0) marks res mid r /\
  (!tail. cleanup ((mid with gas_obs := []) with gas_obs := tail) =
     (INL (), fin with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx, func) (finally source cleanup)
    (es, s0) marks res fin r
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  `!tail. ((mid with gas_obs := []) with gas_obs := tail) =
          (mid with gas_obs := tail)` by
    simp[evaluation_state_component_equality] >>
  gvs[] >> gen_tac >> simp[finally_def] >> Cases_on `res` >>
  simp[ignore_bind_def, bind_def, return_def, raise_def]
QED
