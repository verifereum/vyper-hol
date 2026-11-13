Theory makeSsaRfAllocation
Ancestors makeSsaCurrentAllocation makeSsaCurrentTokens
  makeSsaDefs makeSsaCurrentProps irSupply list alist pair

(* Occurrence tokens, independent of concrete variable spellings. *)







Definition current_env_owned_def:
  current_env_owned V H E <=>
    !v. MEM v V ==> E v = CurrentDefault v \/ ?n. MEM (E v,v,n) H
End

Theorem current_env_owned_initial:
  current_env_owned V [] CurrentDefault
Proof
  simp[current_env_owned_def]
QED

Theorem current_env_owned_append:
  current_env_owned V H E ==> current_env_owned V (H ++ tail) E
Proof
  simp[current_env_owned_def] >> metis_tac[MEM_APPEND]
QED

Theorem current_env_owned_push:
  current_env_owned V H E ==>
  current_env_owned V (H ++ [(t,v,n)]) ((v =+ t) E)
Proof
  simp[current_env_owned_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `v' = v` >> gvs[] >> metis_tac[]
QED















Theorem current_history_name_unique:
  current_history_valid V H /\ MEM (t,v,n) H /\ MEM (u,w,n) H ==> v = w
Proof
  simp[current_history_valid_def, MEM_EL] >> rpt strip_tac >>
  `EL n' (MAP (SND o SND) H) = EL n'' (MAP (SND o SND) H)` by
    (simp[EL_MAP] >> metis_tac[SND]) >>
  `n' = n''` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
  metis_tac[PAIR_EQ]
QED

Theorem current_history_entry_name:
  current_history_valid V H /\ MEM (t,v,n) H ==>
  current_token_name H t = SOME n
Proof
  strip_tac >>
  `ALOOKUP H t = SOME (v,n)` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[current_history_valid_def]) >>
  `!w. t <> CurrentDefault w` by
    (fs[current_history_valid_def, EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  Cases_on `t` >> gvs[current_token_name_def]
QED

Theorem current_history_owner_spelling:
  current_history_valid V H /\ MEM (t,v,n) H /\ MEM n V ==> n = v
Proof
  simp[current_history_valid_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_owned_name_separation:
  current_history_valid V H /\ current_env_owned V H E /\
  current_env_owned V H G /\ MEM v V /\ MEM w V /\ v <> w /\
  current_token_name H (E v) = SOME n /\
  current_token_name H (G w) = SOME m ==> n <> m
Proof
  rpt strip_tac >> gvs[] >>
  `E v = CurrentDefault v \/ ?a. MEM (E v,v,a) H` by
    metis_tac[current_env_owned_def] >>
  `G w = CurrentDefault w \/ ?b. MEM (G w,w,b) H` by
    metis_tac[current_env_owned_def] >>
  gvs[] >> imp_res_tac current_history_entry_name >> gvs[] >>
  metis_tac[current_history_name_unique, current_history_owner_spelling]
QED

Theorem current_latest_name_separation:
  current_history_valid V H /\ current_env_owned V H E /\
  current_env_realizes H E rs V /\ MEM v V /\ MEM w V /\ v <> w ==>
  latest_current_name rs v <> latest_current_name rs w
Proof
  metis_tac[current_owned_name_separation, current_env_realizes_def]
QED

Theorem current_env_realizes_append:
  current_env_realizes H E rs V ==> current_env_realizes (H ++ tail) E rs V
Proof
  simp[current_env_realizes_def] >> metis_tac[current_token_name_append_stable]
QED

Theorem rf_current_env_realizes_restore:
  current_env_realizes H E rs V /\ SND restored = SND rs ==>
  current_env_realizes (H ++ tail) E restored V
Proof
  PairCases_on `rs` >> PairCases_on `restored` >>
  simp[] >> strip_tac >> gvs[] >>
  drule current_env_realizes_append >>
  simp[current_env_realizes_def, latest_current_name_def]
QED

Theorem current_push_nonowner_separation:
  current_allocation_consistent V H s rs /\
  current_env_realizes H E rs V /\ current_env_owned V H E /\
  MEM v V /\ MEM w V /\ w <> v /\
  push_current_name s rs v = (rs',s',n) ==>
  latest_current_name rs w <> n
Proof
  strip_tac >>
  `~MEM n (MAP (SND o SND) H) /\ (MEM n V ==> n = v)` by
    metis_tac[current_push_name_unused] >>
  `E w = CurrentDefault w \/ ?a. MEM (E w,w,a) H` by
    metis_tac[current_env_owned_def] >>
  `current_token_name H (E w) = SOME (latest_current_name rs w)` by
    metis_tac[current_env_realizes_def] >>
  gvs[] >- metis_tac[] >>
  `current_history_valid V H` by fs[current_allocation_consistent_def] >>
  drule_all current_history_entry_name >> strip_tac >> gvs[] >>
  fs[MEM_MAP] >> metis_tac[SND]
QED
