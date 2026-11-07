Theory bodyPtrPopForest
Ancestors bodyPtrPopForestSelect bodyPtrDefs loweringPosts
  vyperPlaceInvariants valueEncoding pred_set vyperState vyperPlaceResultTyping

(* This task-local interface is shared by initialization, actual Pop closure,
   and forward simulation. The opaque suffix is deliberately unrepresented.
   This predicate alone does not assert reachable spatial compatibility. *)
Definition pop_retained_forest_def:
  pop_retained_forest rt a Q entry fresh old tn mem <=>
    entry.type = rt /\ entry.popped = fresh ++ old /\
    well_formed_type_value rt /\ value_has_type rt entry.value /\
    val_wf rt entry.value /\ popped_history_typed rt fresh /\
    (!m. mem_agree_outside tn.t_mem mem m ==>
      val_in_memory rt entry.value a m) /\
    (!p v. MEM (p,v) fresh ==> ?k tv.
      mem_path_offset rt p = SOME (k,tv) /\ val_wf tv v /\
      (!m. mem_agree_outside tn.t_mem mem m ==>
        val_in_memory tv v (a+k) m)) /\
    (!q. q IN Q ==>
      (?v. evaluate_subscripts rt entry.value q = INL v) \/
      (?v. read_popped rt q fresh = SOME v))
End

Theorem pop_retained_forest_init:
  entry.type = rt /\ well_formed_type_value rt /\
  value_has_type rt entry.value /\ val_wf rt entry.value /\
  (!m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory rt entry.value a m) /\
  (!q. q IN Q ==> ?v. evaluate_subscripts rt entry.value q = INL v) ==>
  pop_retained_forest rt a Q entry [] entry.popped tn mem
Proof
  simp[pop_retained_forest_def, popped_history_typed_def]
QED

Theorem pop_retained_forest_read:
  pop_retained_forest rt a Q entry fresh old tn mem /\ q IN Q ==>
  ?v. read_memory_path entry q = INL v /\
    (evaluate_subscripts rt entry.value q = INL v \/
     ( (?err. evaluate_subscripts rt entry.value q = INR err) /\
       read_popped rt q fresh = SOME v))
Proof
  simp[pop_retained_forest_def] >> strip_tac >>
  Cases_on `evaluate_subscripts rt entry.value q`
  >- (simp[read_memory_path_def]) >>
  `?v. read_popped rt q fresh = SOME v` by metis_tac[sumTheory.sum_distinct] >>
  drule read_popped_prefix_noninterference >>
  disch_then (qspec_then `old` assume_tac) >>
  simp[read_memory_path_def]
QED
