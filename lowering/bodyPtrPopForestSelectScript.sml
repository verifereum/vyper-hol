Theory bodyPtrPopForestSelect
Ancestors vyperState vyperPlaceResultTyping list

(* Exact read-prefix noninterference is already exported by
   vyperPlaceResultTyping; do not duplicate it here. *)
Theorem pop_replace_trusted_prefix:
  !fresh rt p replacement old v history.
    read_popped rt p fresh = SOME v /\
    replace_popped rt p replacement (fresh ++ old) = SOME history ==>
    ?fresh'. replace_popped rt p replacement fresh = SOME fresh' /\
      history = fresh' ++ old
Proof
  Induct >> simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[read_popped_def, replace_popped_def] >>
  Cases_on `IS_PREFIX p h0`
  >- (Cases_on `subscripts_type rt h0`
      >- (gvs[] >> metis_tac[APPEND]) >>
      Cases_on `evaluate_subscripts x h1 (DROP (LENGTH h0) p)`
      >- (Cases_on `assign_subscripts x h1 (DROP (LENGTH h0) p)
             (Replace replacement)` >> gvs[]) >>
      gvs[] >> metis_tac[APPEND]) >>
  gvs[] >> metis_tac[APPEND]
QED

Theorem pop_trusted_prefix_read_memory:
  entry.popped = fresh ++ old /\ entry.type = rt /\
  evaluate_subscripts rt entry.value q = INR err /\
  read_popped rt q fresh = SOME v ==>
  read_memory_path entry q = INL v
Proof
  strip_tac >> drule read_popped_prefix_noninterference >>
  disch_then (qspec_then `old` assume_tac) >>
  simp[read_memory_path_def]
QED
