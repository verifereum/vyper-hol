Theory makeSsaCurrentNameStoreReplay
Ancestors makeSsaCurrentSuffixOrigins makeSsaCurrentAllocation
  makeSsaCurrentRenameTrace makeSsaCurrentSequentialOrigins
  makeSsaCurrentDynamicStores list pair combin

Theorem current_history_token_nondefault:
  current_history_valid V H /\ MEM t (MAP FST H) ==>
  !v. t <> CurrentDefault v
Proof
  simp[current_history_valid_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> PairCases_on `y` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem current_history_name_injective:
  current_history_valid V H /\ MEM t (MAP FST H) /\ MEM u (MAP FST H) /\
  current_token_name H t = SOME x /\ current_token_name H u = SOME x ==>
  t = u
Proof
  metis_tac[current_history_token_nondefault, current_allocated_name_injective]
QED

Theorem current_occurrence_name_commute:
  !outs names k ks ns t x.
  LIST_REL (\u y. (u = t <=> y = x)) outs names /\ ks t = ns x ==>
  current_origin_sequential ks (current_occurrence_bindings n k outs) t =
  current_origin_sequential ns (current_occurrence_bindings n k names) x
Proof
  Induct >> Cases_on `names` >>
  simp[current_occurrence_bindings_def, current_origin_sequential_def] >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[GSYM current_origin_sequential_def] >>
  first_x_assum irule >> simp[APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem current_write_name_commute:
  LIST_REL (\u y. (u = t <=> y = x)) outs names /\ ks t = ns x ==>
  current_origin_write_last ks n outs t = current_origin_write_last ns n names x
Proof
  simp[current_origin_write_last_def] >>
  metis_tac[current_occurrence_name_commute]
QED

Theorem current_inst_trace_fixed_names:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_annotations_ok V H anns ==>
  LIST_REL (\(t,v) x. MEM t (MAP FST (H' ++ tail)) /\
    current_token_name (H' ++ tail) t = SOME x) anns inst'.inst_outputs
Proof
  strip_tac >> drule_all current_inst_trace_outputs >>
  `MAP FST H' = MAP FST H ++ MAP FST anns` by
    metis_tac[current_outputs_trace_keys, current_inst_trace_def] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  qpat_x_assum `!n. _` (qspec_then `n` mp_tac) >>
  Cases_on `EL n anns` >> simp[] >> strip_tac >> conj_tac
  >- (disj1_tac >> disj2_tac >> simp[MEM_MAP, MEM_EL] >>
      qexists_tac `EL n anns` >> simp[] >> metis_tac[]) >>
  irule current_token_name_append_stable >> simp[]
QED

Theorem current_local_trace_fixed_names:
  !annss insts s rs H E insts' s' rs' H' E' Hb tail.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) /\ Hb = H' ++ tail ==>
  LIST_REL (\anns i. LIST_REL (\(t,v) x.
    MEM t (MAP FST Hb) /\ current_token_name Hb t = SOME x)
      anns i.inst_outputs) annss insts'
Proof
  Induct >- simp[current_local_trace_def] >>
  rpt gen_tac >> strip_tac >> gvs[current_local_trace_def] >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (fs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  conj_tac
  >- (drule current_local_trace_history >> strip_tac >>
      drule_all current_inst_trace_fixed_names >>
      disch_then (qspec_then `tail' ++ tail` mp_tac) >>
      simp[APPEND_ASSOC]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_history_write_commute:
  current_history_valid V H /\ MEM t (MAP FST H) /\
  current_token_name H t = SOME x /\ ks t = ns x /\
  LIST_REL (\(u,v) y. MEM u (MAP FST H) /\
    current_token_name H u = SOME y) anns names ==>
  current_origin_write_last ks n (MAP FST anns) t =
    current_origin_write_last ns n names x
Proof
  strip_tac >> irule current_write_name_commute >> simp[] >>
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >> simp[EL_MAP] >>
  qpat_x_assum `!n. _` (qspec_then `n` mp_tac) >>
  Cases_on `EL n anns` >> simp[] >> strip_tac >>
  metis_tac[current_history_name_injective, optionTheory.SOME_11]
QED

Theorem current_replay_names:
  !annss insts n ks ns j.
  LIST_REL (\anns i. LIST_REL (\(t,v) x.
    MEM t (MAP FST H) /\ current_token_name H t = SOME x)
      anns i.inst_outputs) annss insts /\
  current_history_valid V H /\
  (!t x. MEM t (MAP FST H) /\ current_token_name H t = SOME x ==>
     ks t = ns x) ==>
  !t x. MEM t (MAP FST H) /\ current_token_name H t = SOME x ==>
  current_token_replay n (TAKE j annss) ks t =
    current_source_replay n (TAKE j insts) ns x
Proof
  Induct >- simp[current_token_replay_def, current_source_replay_def] >>
  Cases_on `insts` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `j` >- simp[current_token_replay_def, current_source_replay_def] >>
  simp[TAKE_def, current_token_replay_def, current_source_replay_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >> rpt strip_tac >>
  irule current_history_write_commute >> metis_tac[]
QED

Theorem current_local_trace_name_replay:
  current_local_trace annss insts s rs H0 E insts' s' rs' Hf E' /\
  current_annotations_ok V H0 (FLAT annss) /\
  current_history_valid V Hf /\
  (!t x. MEM t (MAP FST Hf) /\ current_token_name Hf t = SOME x ==>
     ks t = ns x) ==>
  !n j t x. MEM t (MAP FST Hf) /\ current_token_name Hf t = SOME x ==>
  current_token_replay n (TAKE j annss) ks t =
    current_source_replay n (TAKE j insts') ns x
Proof
  strip_tac >>
  `LIST_REL (\anns i. LIST_REL (\(t,v) x.
    MEM t (MAP FST Hf) /\ current_token_name Hf t = SOME x)
      anns i.inst_outputs) annss insts'` by
    (irule current_local_trace_fixed_names >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `[]` >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule current_replay_names >> metis_tac[]
QED

Theorem current_annotations_take[local]:
  current_annotations_ok V H (FLAT annss) ==>
  current_annotations_ok V H (FLAT (TAKE j annss))
Proof
  `FLAT annss = FLAT (TAKE j annss) ++ FLAT (DROP j annss)` by
    metis_tac[TAKE_DROP, FLAT_APPEND] >>
  pop_assum SUBST1_TAC >>
  simp[current_annotations_ok_def, ALL_DISTINCT_APPEND]
QED

(* The history-domain condition deliberately remains explicit: default tokens
   alias first allocations and are not covered by this projection. *)
Theorem current_local_trace_concrete_origin_operand:
  current_local_trace annss insts s rs H E insts' s' rs' Hf E' /\
  EVERY (\i. i.inst_opcode <> PHI) insts /\
  current_annotations_ok V H (FLAT annss) /\
  (!v. E v = CurrentDefault v \/ MEM (E v) (MAP FST H)) /\
  current_live_origin_agree (current_suffix_demand insts D) E ms ks /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_history_valid V Hf /\
  (!t x. MEM t (MAP FST Hf) /\ current_token_name Hf t = SOME x ==>
     ks t = ns x) /\
  j < LENGTH insts /\ MEM (Var v) (EL j insts).inst_operands /\ MEM v V ==>
  ?sj rsj Hj Ej.
    current_local_trace (TAKE j annss) (TAKE j insts)
      s rs H E (TAKE j insts') sj rsj Hj Ej /\
    current_local_trace (DROP j annss) (DROP j insts)
      sj rsj Hj Ej (DROP j insts') s' rs' Hf E' /\
    current_env_realizes Hj Ej rsj V /\
    (MEM (Ej v) (MAP FST Hf) ==>
      current_source_replay n (TAKE j insts) ms v =
      current_source_replay n (TAKE j insts') ns (latest_current_name rsj v))
Proof
  strip_tac >> drule_all current_local_trace_origin_operand >>
  disch_then (qspec_then `n` strip_assume_tac) >>
  `current_annotations_ok V H (FLAT (TAKE j annss))` by
    metis_tac[current_annotations_take] >>
  `current_env_realizes Hj Ej rsj V` by
    metis_tac[current_local_trace_preserves] >>
  qexistsl_tac [`sj`, `rsj`, `Hj`, `Ej`] >> simp[] >> strip_tac >>
  `current_token_name Hf (Ej v) = SOME (latest_current_name rsj v)` by
    (qpat_x_assum `current_local_trace (DROP j annss) _ _ _ _ _ _ _ _ _ _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP current_local_trace_history) >>
     gvs[] >> irule current_token_name_append_stable >>
     fs[current_env_realizes_def]) >>
  drule_all current_local_trace_name_replay >>
  disch_then (qspecl_then [`n`, `j`] mp_tac) >>
  simp[]
QED
