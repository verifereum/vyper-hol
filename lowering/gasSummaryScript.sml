(* Source reads select the explicit events of an actual target GAS path.
   The unused source suffix cannot affect the result or its other fields. *)
Theory gasSummary
Ancestors
  fragGasMode fragGasPath fragGasPathMem gasCount gasOracleReplay fragExec venomState
  vyperInterpreter vyperState vyperValue list rich_list pair arithmetic

Definition gas_explicit_def:
  gas_explicit (marks : bool list) gs =
    MAP SND (FILTER FST (ZIP (marks, gas_prefix (LENGTH marks) gs)))
End

(* Concrete entry relations belong outside this existential summary.
   Every witness carries an actual target path and its outcome post. *)
(* Each producer fixes its marks and concrete target segment before an
   enclosing consumer inspects the source result. *)
Definition gas_marked_exec_def:
  gas_marked_exec memory (ctx, func) source (es, s0) marks res es_end r <=>
    (!tail.
       source (es with gas_obs :=
                 gas_explicit marks s0.vs_gas_readings ++ tail) =
         (res, es_end with gas_obs := tail)) /\
    gas_marked_path memory ctx func s0 (LENGTH marks) r
End

Definition gas_summary_at_def:
  gas_summary_at memory (ctx, func) marks source (es, s0) Q R <=>
    ?res es_end r.
      gas_marked_exec memory (ctx, func) source (es, s0) marks res es_end r /\
      ((?t. r = OK t /\ Q res (es_end with gas_obs := []) t) \/
       (exit_result r /\ R res (es_end with gas_obs := []) r))
End

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

Theorem gas_explicit_nil[simp]:
  gas_explicit [] gs = []
Proof
  simp[gas_explicit_def]
QED

Theorem gas_explicit_cons:
  (gas_explicit (b::bs) [] =
     if b then 0w :: gas_explicit bs [] else gas_explicit bs []) /\
  (gas_explicit (b::bs) (g::gs) =
     if b then g :: gas_explicit bs gs else gas_explicit bs gs)
Proof
  Cases_on `b` >> simp[gas_explicit_def, gas_prefix_suc]
QED

Theorem gas_explicit_replicate_false[simp]:
  !n gs. gas_explicit (REPLICATE n F) gs = []
Proof
  Induct_on `n` >- simp[] >>
  gen_tac >> Cases_on `gs` >> simp[REPLICATE, gas_explicit_cons]
QED

Theorem gas_explicit_append:
  gas_explicit (left ++ right) gs =
    gas_explicit left gs ++ gas_explicit right (DROP (LENGTH left) gs)
Proof
  qid_spec_tac `gs` >> Induct_on `left` >- simp[] >>
  rpt gen_tac >> Cases_on `gs` >> Cases_on `h` >>
  simp[gas_explicit_cons]
QED

Theorem gas_summary_conseq:
  gas_summary (ctx, func) source (es, s0) Q R /\
  (!res es_end t. Q res es_end t ==> Q' res es_end t) /\
  (!res es_end r. R res es_end r ==> R' res es_end r) ==>
  gas_summary (ctx, func) source (es, s0) Q' R'
Proof
  pure_rewrite_tac[gas_summary_def] >> metis_tac[]
QED

Theorem gas_summary_no_source_read:
  (!tail. source (es with gas_obs := tail) =
            (res, es_end with gas_obs := tail)) /\
  gas_path ctx func s0 n r /\
  ((?t. r = OK t /\ Q res (es_end with gas_obs := []) t) \/
   (exit_result r /\ R res (es_end with gas_obs := []) r)) ==>
  gas_summary (ctx, func) source (es, s0) Q R
Proof
  strip_tac >> rewrite_tac[gas_summary_def] >>
  qexistsl_tac [`REPLICATE n F`, `res`, `es_end`] >>
  simp[] >> metis_tac[]
QED

Theorem gas_summary_next_read:
  gas_path ctx func s0 1 (OK t) /\
  gas_prefix 1 s0.vs_gas_readings = [w] /\
  Q (INL (IntV (&w2n w))) (es with gas_obs := []) t ==>
  gas_summary (ctx, func) next_gas_reading (es, s0) Q R
Proof
  strip_tac >>
  `gas_explicit [T] s0.vs_gas_readings = [w]` by
    simp[gas_explicit_def] >>
  rewrite_tac[gas_summary_def] >>
  qexistsl_tac [`[T]`, `INL (IntV (&w2n w))`, `es`] >>
  simp[next_gas_reading_def, return_def] >>
  qexists_tac `OK t` >> simp[]
QED

Theorem gas_summary_at_summary:
  gas_summary_at memory (ctx, func) marks source (es, s0) Q R ==>
  gas_summary (ctx, func) source (es, s0) Q R
Proof
  simp[gas_summary_at_def, gas_marked_exec_def, gas_summary_def] >>
  metis_tac[gas_marked_path_exec]
QED

(* Generated target reads carry false marks when the source reads no gas. *)
Theorem gas_marked_exec_no_source_read:
  (!tail. source (es with gas_obs := tail) =
            (res, es_end with gas_obs := tail)) /\
  gas_marked_path memory ctx func s0 n r ==>
  gas_marked_exec memory (ctx, func) source (es, s0)
    (REPLICATE n F) res es_end r
Proof
  simp[gas_marked_exec_def]
QED

Theorem gas_marked_exec_from_mem:
  gas_marked_exec T p source start marks res fin r ==>
  gas_marked_exec memory p source start marks res fin r
Proof
  PairCases_on `p` >> PairCases_on `start` >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[gas_path_mem_exec]
QED

Theorem gas_summary_at_from_mem:
  gas_summary_at T p marks source start Q R ==>
  gas_summary_at memory p marks source start Q R
Proof
  PairCases_on `p` >> PairCases_on `start` >>
  simp[gas_summary_at_def] >> metis_tac[gas_marked_exec_from_mem]
QED
