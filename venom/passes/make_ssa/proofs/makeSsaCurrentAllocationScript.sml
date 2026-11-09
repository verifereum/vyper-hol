Theory makeSsaCurrentAllocation
Ancestors
  makeSsaCurrentTokens makeSsaDefs makeSsaCurrentProps irSupply
  list alist pair

(* Histories contain definition occurrences only. Defaults intentionally alias
   the first definition's original spelling, but are never history keys. *)
Definition current_token_name_def:
  (current_token_name H (CurrentDefault v) = SOME v) /\
  (current_token_name H (CurrentOriginal l i j) =
    OPTION_MAP SND (ALOOKUP H (CurrentOriginal l i j))) /\
  (current_token_name H (CurrentInserted v l) =
    OPTION_MAP SND (ALOOKUP H (CurrentInserted v l)))
End

Definition current_history_valid_def:
  current_history_valid V H <=>
    ALL_DISTINCT (MAP FST H) /\ ALL_DISTINCT (MAP (SND o SND) H) /\
    EVERY (\(t,v,n). (!w. t <> CurrentDefault w) /\ MEM v V /\
      (MEM n V ==> n = v)) H
End

Definition current_owner_count_def:
  current_owner_count H v = LENGTH (FILTER (\e. FST (SND e) = v) H)
End

Definition current_counter_def:
  current_counter rs v = case ALOOKUP (FST rs) v of NONE => 0n | SOME n => n
End

Definition current_allocation_consistent_def:
  current_allocation_consistent V H s rs <=>
    current_history_valid V H /\
    (!v. current_counter rs v = current_owner_count H v) /\
    ssa_vars_covered s V /\
    ssa_vars_covered s (MAP (SND o SND) H) /\
    ssa_stacks_covered s (SND rs)
End

Definition current_env_realizes_def:
  current_env_realizes H E rs V <=>
    !v. MEM v V ==>
      current_token_name H (E v) = SOME (latest_current_name rs v)
End

Theorem current_token_name_default[simp]:
  current_token_name H (CurrentDefault v) = SOME v
Proof
  simp[current_token_name_def]
QED

Theorem current_token_name_append_stable:
  current_token_name H t = SOME n ==>
  current_token_name (H ++ tail) t = SOME n
Proof
  Cases_on `t` >> simp[current_token_name_def, ALOOKUP_APPEND] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem current_token_name_new:
  (!w. t <> CurrentDefault w) /\ ~MEM t (MAP FST H) ==>
  current_token_name (H ++ [(t,v,n)]) t = SOME n
Proof
  Cases_on `t` >> simp[current_token_name_def, ALOOKUP_APPEND] >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `ALOOKUP H key` >>
  `ALOOKUP H key = NONE` by
    (Cases_on `ALOOKUP H key` >> simp[] >>
     imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, Abbr `key`] >> metis_tac[FST]) >> simp[]
QED

Theorem current_owner_count_append[simp]:
  current_owner_count (H ++ [(t,v,n)]) w =
    current_owner_count H w + if v = w then 1 else 0
Proof
  simp[current_owner_count_def, FILTER_APPEND_DISTRIB] >> Cases_on `v = w` >> simp[]
QED

Theorem current_push_latest:
  push_current_name s rs v = (rs',s',n) ==>
  latest_current_name rs' w = if w = v then n else latest_current_name rs w
Proof
  PairCases_on `rs` >> simp[push_current_name_def] >>
  Cases_on `ALOOKUP rs0 v` >> simp[]
  >- (strip_tac >> Cases_on `w = v` >>
      gvs[latest_current_name_def, ALOOKUP_FILTER]) >>
  rename1 `ALOOKUP rs0 v = SOME k` >> Cases_on `k = 0` >> simp[]
  >- (strip_tac >> Cases_on `w = v` >>
      gvs[latest_current_name_def, ALOOKUP_FILTER]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[latest_current_name_def] >>
  Cases_on `w = v` >> simp[ALOOKUP_FILTER]
QED

Theorem current_push_counter:
  push_current_name s rs v = (rs',s',n) ==>
  current_counter rs' w = current_counter rs w + if w = v then 1 else 0
Proof
  PairCases_on `rs` >> simp[push_current_name_def] >>
  Cases_on `ALOOKUP rs0 v` >> simp[]
  >- (strip_tac >> Cases_on `w = v` >>
      gvs[current_counter_def, ALOOKUP_FILTER]) >>
  rename1 `ALOOKUP rs0 v = SOME k` >> Cases_on `k = 0` >> simp[]
  >- (strip_tac >> Cases_on `w = v` >>
      gvs[current_counter_def, ALOOKUP_FILTER]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[current_counter_def] >>
  Cases_on `w = v` >> simp[ALOOKUP_FILTER]
QED

Theorem current_push_env_realizes:
  current_env_realizes H E rs V /\
  (!w. t <> CurrentDefault w) /\ ~MEM t (MAP FST H) /\
  push_current_name s rs v = (rs',s',n) ==>
  current_env_realizes (H ++ [(t,v,n)]) ((v =+ t) E) rs' V
Proof
  rpt strip_tac >> simp[current_env_realizes_def] >> rpt strip_tac >>
  drule current_push_latest >> disch_then (qspec_then `v'` assume_tac) >>
  Cases_on `v' = v` >> gvs[]
  >- metis_tac[current_token_name_new] >>
  fs[current_env_realizes_def, combinTheory.APPLY_UPDATE_THM] >>
  irule current_token_name_append_stable >> simp[]
QED

Theorem current_push_counts:
  (!w. current_counter rs w = current_owner_count H w) /\
  push_current_name s rs v = (rs',s',n) ==>
  !w. current_counter rs' w = current_owner_count (H ++ [(t,v,n)]) w
Proof
  rpt strip_tac >> drule current_push_counter >>
  disch_then (qspec_then `w` mp_tac) >> simp[] >>
  Cases_on `w = v` >> simp[]
QED

Theorem current_push_choice:
  push_current_name s rs v = (rs',s',n) ==>
  (current_counter rs v = 0 /\ n = v /\ s' = s) \/
  (current_counter rs v <> 0 /\ fresh_ir_var s = (n,s'))
Proof
  PairCases_on `rs` >> simp[push_current_name_def, current_counter_def] >>
  Cases_on `ALOOKUP rs0 v` >> simp[] >>
  rename1 `ALOOKUP rs0 v = SOME k` >> Cases_on `k = 0` >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem current_owner_count_zero:
  current_owner_count H v = 0 ==> !t n. ~MEM (t,v,n) H
Proof
  simp[current_owner_count_def, FILTER_EQ_NIL, EVERY_MEM] >>
  metis_tac[FST, SND]
QED

Theorem current_push_name_unused:
  current_allocation_consistent V H s rs /\ MEM v V /\
  push_current_name s rs v = (rs',s',n) ==>
  ~MEM n (MAP (SND o SND) H) /\ (MEM n V ==> n = v)
Proof
  rpt strip_tac >> drule current_push_choice >> strip_tac
  >- (gvs[current_allocation_consistent_def] >>
      drule current_owner_count_zero >>
      fs[current_history_valid_def, EVERY_MEM, MEM_MAP] >>
      rpt strip_tac >> PairCases_on `y` >> gvs[] >>
      first_x_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[] >>
      metis_tac[]) >>
  drule fresh_ir_var_contract >> strip_tac >>
  fs[current_allocation_consistent_def, ssa_vars_covered_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem current_history_valid_append:
  current_history_valid V H /\ (!w. t <> CurrentDefault w) /\
  ~MEM t (MAP FST H) /\ ~MEM n (MAP (SND o SND) H) /\
  MEM v V /\ (MEM n V ==> n = v) ==>
  current_history_valid V (H ++ [(t,v,n)])
Proof
  simp[current_history_valid_def, MAP_APPEND, ALL_DISTINCT_APPEND] >>
  metis_tac[]
QED

Theorem current_push_consistent:
  current_allocation_consistent V H s rs /\ MEM v V /\
  (!w. t <> CurrentDefault w) /\ ~MEM t (MAP FST H) /\
  push_current_name s rs v = (rs',s',n) ==>
  current_allocation_consistent V (H ++ [(t,v,n)]) s' rs'
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM n (MAP (SND o SND) H) /\ (MEM n V ==> n = v)` by
    (drule_all current_push_name_unused >> simp[]) >>
  `MEM v s.irs_used_vars` by
    (fs[current_allocation_consistent_def, ssa_vars_covered_def, EVERY_MEM]) >>
  `ssa_stacks_covered s' (SND rs') /\ MEM n s'.irs_used_vars /\
   ssa_supply_extends s s'` by
    (irule push_current_name_covered >>
     fs[current_allocation_consistent_def] >> metis_tac[]) >>
  simp[current_allocation_consistent_def] >> conj_tac
  >- (irule current_history_valid_append >>
      fs[current_allocation_consistent_def]) >>
  conj_tac
  >- (fs[current_allocation_consistent_def] >>
      drule_all current_push_counts >> simp[]) >>
  fs[current_allocation_consistent_def] >>
  `ssa_vars_covered s' V` by metis_tac[ssa_vars_covered_mono] >>
  `ssa_vars_covered s' (MAP (SND o SND) H)` by
    metis_tac[ssa_vars_covered_mono] >>
  fs[MAP_APPEND, ssa_vars_covered_def]
QED

Theorem current_token_name_allocated:
  (!w. t <> CurrentDefault w) /\ current_token_name H t = SOME n ==>
  ?v. MEM (t,v,n) H
Proof
  Cases_on `t` >> simp[current_token_name_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[PAIR]
QED

Theorem current_allocated_name_injective:
  current_history_valid V H /\
  (!w. t <> CurrentDefault w) /\ (!w. u <> CurrentDefault w) /\
  current_token_name H t = SOME n /\ current_token_name H u = SOME n ==>
  t = u
Proof
  rpt strip_tac >>
  `?v. MEM (t,v,n) H` by metis_tac[current_token_name_allocated] >>
  `?w. MEM (u,w,n) H` by metis_tac[current_token_name_allocated] >>
  fs[current_history_valid_def, MEM_EL] >>
  `EL n' H = EL n'' H` suffices_by metis_tac[PAIR_EQ] >>
  `n' = n''` suffices_by simp[] >>
  `EL n' (MAP (SND o SND) H) = EL n'' (MAP (SND o SND) H)` by
    (simp[EL_MAP] >> metis_tac[SND]) >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

Theorem current_allocation_initial:
  ssa_vars_covered s V ==>
  current_allocation_consistent V [] s ([],[]) /\
  current_env_realizes [] CurrentDefault ([],[]) V
Proof
  simp[current_allocation_consistent_def, current_history_valid_def,
       current_counter_def, current_owner_count_def,
       ssa_vars_covered_def, ssa_stacks_covered_def,
       current_env_realizes_def, latest_current_name_def]
QED

Theorem current_first_allocation_alias:
  current_allocation_consistent V H s rs /\
  current_owner_count H v = 0 /\ (!w. t <> CurrentDefault w) /\
  ~MEM t (MAP FST H) /\ push_current_name s rs v = (rs',s',n) ==>
  n = v /\ s' = s /\
  current_token_name (H ++ [(t,v,n)]) t =
    current_token_name (H ++ [(t,v,n)]) (CurrentDefault v)
Proof
  rpt gen_tac >> strip_tac >> drule current_push_choice >>
  fs[current_allocation_consistent_def] >> strip_tac >> gvs[] >>
  metis_tac[current_token_name_new, current_token_name_default]
QED

Theorem current_repeated_allocation_distinct:
  current_allocation_consistent V H s rs /\ MEM v V /\
  (!w. t <> CurrentDefault w) /\ ~MEM t (MAP FST H) /\
  push_current_name s rs v = (rs1,s1,n1) /\
  push_current_name s1 rs1 v = (rs2,s2,n2) ==>
  n1 <> n2
Proof
  rpt strip_tac >>
  `current_allocation_consistent V (H ++ [(t,v,n1)]) s1 rs1` by
    (irule current_push_consistent >> metis_tac[]) >>
  drule_all current_push_name_unused >> simp[]
QED
