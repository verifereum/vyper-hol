(* Source reads select the explicit events of an actual target GAS path.
   The unused source suffix cannot affect the result or its other fields. *)
Theory gasSummary
Ancestors
  fragGasPath gasCount gasOracleReplay fragExec venomState
  vyperInterpreter vyperState vyperValue list rich_list pair arithmetic

Definition gas_explicit_def:
  gas_explicit (marks : bool list) gs =
    MAP SND (FILTER FST (ZIP (marks, gas_prefix (LENGTH marks) gs)))
End

(* Concrete entry relations belong outside this existential summary.
   Every witness carries an actual target path and its outcome post. *)
Definition gas_summary_def:
  gas_summary (ctx, func) source (es, s0) Q R <=>
    ?marks res es_end.
      (!tail.
         source (es with gas_obs :=
                   gas_explicit marks s0.vs_gas_readings ++ tail) =
           (res, es_end with gas_obs := tail)) /\
      ?r. gas_path ctx func s0 (LENGTH marks) r /\
        ((?t. r = OK t /\ Q res (es_end with gas_obs := []) t) \/
         (exit_result r /\ R res (es_end with gas_obs := []) r))
End

Theorem gas_explicit_append:
  gas_explicit (left ++ right) gs =
    gas_explicit left gs ++ gas_explicit right (DROP (LENGTH left) gs)
Proof
  cheat
QED

Theorem gas_summary_conseq:
  gas_summary (ctx, func) source (es, s0) Q R /\
  (!res es_end t. Q res es_end t ==> Q' res es_end t) /\
  (!res es_end r. R res es_end r ==> R' res es_end r) ==>
  gas_summary (ctx, func) source (es, s0) Q' R'
Proof
  cheat
QED

Theorem gas_summary_no_source_read:
  (!tail. source (es with gas_obs := tail) =
            (res, es_end with gas_obs := tail)) /\
  gas_path ctx func s0 n r /\
  ((?t. r = OK t /\ Q res (es_end with gas_obs := []) t) \/
   (exit_result r /\ R res (es_end with gas_obs := []) r)) ==>
  gas_summary (ctx, func) source (es, s0) Q R
Proof
  cheat
QED

Theorem gas_summary_next_read:
  gas_path ctx func s0 1 (OK t) /\
  gas_prefix 1 s0.vs_gas_readings = [w] /\
  Q (INL (IntV (&w2n w))) (es with gas_obs := []) t ==>
  gas_summary (ctx, func) next_gas_reading (es, s0) Q R
Proof
  cheat
QED
