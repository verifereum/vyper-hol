Theory makeSsaCurrentSuffixOrigins
Ancestors makeSsaCurrentSequentialTransfer makeSsaCurrentLiveOriginTransfer
  makeSsaCurrentSequentialOrigins makeSsaCurrentRenameTrace
  makeSsaCurrentDynamicStores venomInst list combin

Definition current_suffix_demand_def:
  (current_suffix_demand [] D v <=> D v) /\
  (current_suffix_demand (i::is) D v <=>
    MEM (Var v) i.inst_operands \/
    (current_suffix_demand is D v /\ ~MEM v i.inst_outputs))
End

Definition current_source_replay_def:
  (current_source_replay n [] ms = ms) /\
  (current_source_replay n (i::is) ms =
    current_source_replay (SUC n) is
      (current_origin_write_last ms n i.inst_outputs))
End

Definition current_token_replay_def:
  (current_token_replay n [] ks = ks) /\
  (current_token_replay n (anns::annss) ks =
    current_token_replay (SUC n) annss
      (current_origin_write_last ks n (MAP FST anns)))
End

Theorem current_suffix_demand_singleton:
  current_suffix_demand [i] D v <=>
  MEM (Var v) i.inst_operands \/ (D v /\ ~MEM v i.inst_outputs)
Proof
  simp[current_suffix_demand_def]
QED

Theorem current_suffix_demand_read_write:
  MEM (Var v) i.inst_operands /\ MEM v i.inst_outputs ==>
  current_suffix_demand (i::is) D v
Proof
  simp[current_suffix_demand_def]
QED

Theorem current_outputs_trace_env_range[local]:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  (!v. E v = CurrentDefault v \/ MEM (E v) (MAP FST H)) ==>
  !v. E' v = CurrentDefault v \/ MEM (E' v) (MAP FST H')
Proof
  Induct >- simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[MAP_APPEND, APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem current_local_trace_suffix_origin:
  !annss insts s rs H E insts' s' rs' H' E' V D ms ks n j.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  EVERY (\i. i.inst_opcode <> PHI) insts /\
  current_annotations_ok V H (FLAT annss) /\
  (!v. E v = CurrentDefault v \/ MEM (E v) (MAP FST H)) /\
  current_live_origin_agree (current_suffix_demand insts D) E ms ks /\
  j <= LENGTH insts ==>
  ?sj rsj Hj Ej.
    current_local_trace (TAKE j annss) (TAKE j insts)
      s rs H E (TAKE j insts') sj rsj Hj Ej /\
    current_local_trace (DROP j annss) (DROP j insts)
      sj rsj Hj Ej (DROP j insts') s' rs' H' E' /\
    current_live_origin_agree (current_suffix_demand (DROP j insts) D) Ej
      (current_source_replay n (TAKE j insts) ms)
      (current_token_replay n (TAKE j annss) ks)
Proof
  Induct >- simp[current_local_trace_def, current_source_replay_def,
    current_token_replay_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `j` >- (fs[current_local_trace_def, current_source_replay_def,
    current_token_replay_def] >> metis_tac[]) >>
  gvs[current_local_trace_def] >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (fs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  `!v. E1 v = CurrentDefault v \/ MEM (E1 v) (MAP FST H1)` by
    (irule current_outputs_trace_env_range >> metis_tac[current_inst_trace_def]) >>
  `current_live_origin_agree (current_suffix_demand rest D) E1
    (current_origin_write_last ms n inst.inst_outputs)
    (current_origin_write_last ks n (MAP FST h))` by
    (fs[current_inst_trace_def] >>
     `current_live_origin_agree
       (\v. current_suffix_demand rest D v /\ ~MEM v (MAP SND h)) E ms ks` by
       (fs[current_live_origin_agree_def, current_suffix_demand_def] >>
        rpt strip_tac >> first_x_assum irule >> simp[]) >>
     drule_all current_outputs_trace_live_origin_last >> simp[]) >>
  first_x_assum drule_all >>
  disch_then (qspec_then `SUC n` mp_tac) >>
  strip_tac >> qexistsl_tac [`sj`, `rsj`, `Hj`, `Ej`] >>
  simp[TAKE_def, DROP_def, current_source_replay_def, current_token_replay_def] >>
  metis_tac[]
QED

Theorem current_local_trace_lengths[local]:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  LENGTH annss = LENGTH insts /\ LENGTH insts' = LENGTH insts
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem current_local_trace_origin_exit:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  EVERY (\i. i.inst_opcode <> PHI) insts /\
  current_annotations_ok V H (FLAT annss) /\
  (!v. E v = CurrentDefault v \/ MEM (E v) (MAP FST H)) /\
  current_live_origin_agree (current_suffix_demand insts D) E ms ks ==>
  current_live_origin_agree D E'
    (current_source_replay n insts ms) (current_token_replay n annss ks)
Proof
  strip_tac >> `LENGTH insts <= LENGTH insts` by simp[] >>
  drule_all current_local_trace_suffix_origin >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  drule current_local_trace_lengths >> strip_tac >>
  gvs[TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG,
    current_local_trace_def, current_live_origin_agree_def, current_suffix_demand_def]
QED

Theorem current_suffix_demand_operand[local]:
  !j insts. j < LENGTH insts /\ MEM (Var v) (EL j insts).inst_operands ==>
  current_suffix_demand (DROP j insts) D v
Proof
  Induct >> Cases_on `insts` >> simp[DROP_def, current_suffix_demand_def] >>
  metis_tac[]
QED

Theorem current_local_trace_origin_operand:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  EVERY (\i. i.inst_opcode <> PHI) insts /\
  current_annotations_ok V H (FLAT annss) /\
  (!v. E v = CurrentDefault v \/ MEM (E v) (MAP FST H)) /\
  current_live_origin_agree (current_suffix_demand insts D) E ms ks /\
  j < LENGTH insts /\ MEM (Var v) (EL j insts).inst_operands ==>
  ?sj rsj Hj Ej.
    current_local_trace (TAKE j annss) (TAKE j insts)
      s rs H E (TAKE j insts') sj rsj Hj Ej /\
    current_local_trace (DROP j annss) (DROP j insts)
      sj rsj Hj Ej (DROP j insts') s' rs' H' E' /\
    current_source_replay n (TAKE j insts) ms v =
      current_token_replay n (TAKE j annss) ks (Ej v)
Proof
  strip_tac >> `j <= LENGTH insts` by simp[] >>
  drule_all current_local_trace_suffix_origin >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`sj`, `rsj`, `Hj`, `Ej`] >> simp[] >>
  fs[current_live_origin_agree_def] >> first_x_assum irule >>
  metis_tac[current_suffix_demand_operand]
QED
