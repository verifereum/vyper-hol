(* Sequential source evaluation concatenates explicit-event markings,
   while target paths account for every generated and explicit read. *)
Theory gasSummaryCompose
Ancestors
  gasSummary fragGasPath gasCount vyperState vyperInterpreter list rich_list

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

Theorem gas_summary_bind:
  gas_summary (ctx, func) source (es, s0)
    (\res es_mid t.
       ?v. res = INL v /\
           gas_summary (ctx, func) (next v) (es_mid, t) Q R)
    (\res es_end r. ?exc. res = INR exc /\ R (INR exc) es_end r) ==>
  gas_summary (ctx, func) (bind source next) (es, s0) Q R
Proof
  cheat
QED
